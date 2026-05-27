import Mathlib
import Lean.Meta.Tactic.TryThis

open Lean Elab Tactic Meta

namespace WZProver
namespace Tactic

private def jsonString (s : String) : Json :=
  Json.str s

private def collectUserHypotheses (lctx : LocalContext) : MetaM (Array String) := do
  let mut hs : Array String := #[]
  for fvarId in lctx.getFVarIds do
    let decl := lctx.fvarIdToDecl.find! fvarId
    if decl.isImplementationDetail || decl.isAuxDecl then
      continue
    let typeFmt ← Meta.ppExpr decl.type
    hs := hs.push s!"({decl.userName} : {typeFmt})"
  return hs

private def buildTheoremHeaderFromGoal : TacticM String := withMainContext do
  let mvarId ← getMainGoal
  let mvarDecl ← mvarId.getDecl
  let hyps ← collectUserHypotheses mvarDecl.lctx
  let targetFmt ← Meta.ppExpr mvarDecl.type
  let hypsStr := String.intercalate " " hyps.toList
  if hypsStr.isEmpty then
    return s!"theorem wz_tmp : {targetFmt}"
  return s!"theorem wz_tmp {hypsStr} : {targetFmt}"

private def postToWZServer (theoremHeader : String) : TacticM Json := do
  let payload := Json.mkObj [
    ("theorem", jsonString theoremHeader)
  ]
  let out ← IO.Process.output {
    cmd := "curl"
    args := #[
      "--silent",
      "--show-error",
      "--fail",
      "--connect-timeout", "3",
      "--max-time", "180",
      "-X", "POST",
      "http://127.0.0.1:5001/parse",
      "-H", "accept: application/json",
      "-H", "Content-Type: application/json",
      "--data", payload.pretty
    ]
  }
  if out.exitCode != 0 then
    if out.exitCode == 28 then
      throwError "wz_prove: request timed out. Server is running, but proof generation took longer than 180s."
    let err := out.stderr.trim
    if err.isEmpty then
      throwError "wz_prove: request failed (curl exit code {out.exitCode}). Make sure server is running at http://127.0.0.1:5001/parse"
    throwError "wz_prove: request failed (curl exit code {out.exitCode}): {err}"
  match Json.parse out.stdout with
  | .ok js =>
      return js
  | .error e =>
      throwError "wz_prove: invalid JSON response: {e}"

private def extractTacticFromResponse (js : Json) : TacticM String := do
  let status ←
    match js.getObjValAs? String "status" with
    | .ok s => pure s
    | .error _ => throwError "wz_prove: response missing 'status'"
  if status == "success" then
    match js.getObjValAs? String "tactic" with
    | .ok tac =>
        if tac.trim.isEmpty then
          throwError "wz_prove: server returned empty tactic"
        pure tac
    | .error _ =>
        throwError "wz_prove: response missing 'tactic'"
  else
    let msg :=
      match js.getObjValAs? String "message" with
      | .ok m => m
      | .error _ => "unknown server error"
    throwError "wz_prove server error: {msg}"

syntax (name := wzProveTac) "wz_prove" : tactic

@[tactic wzProveTac] def evalWzProveTac : Tactic := fun stx => do
  try
    let theoremHeader ← buildTheoremHeaderFromGoal
    let js ← postToWZServer theoremHeader
    let tacticText ← extractTacticFromResponse js
    Lean.Meta.Tactic.TryThis.addSuggestion stx
      {
        suggestion := tacticText
        toCodeActionTitle? := some (fun _ => "Replace wz_prove with generated WZ proof")
      }
      (origSpan? := (← getRef))
    logInfoAt stx "wz_prove: suggestion generated. Click Try This or use code action to apply."
  catch e =>
    logWarningAt stx e.toMessageData

end Tactic
end WZProver
