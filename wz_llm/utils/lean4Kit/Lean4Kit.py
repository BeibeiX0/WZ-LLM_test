import subprocess
import json
import signal
from pathlib import Path
import sys
from .LeanKitException import *
import time
class TacticState():
    def __init__(self, res, state_type="cmd"):
        self.finishFlag = False
        self.proofStates = []
        self.history_tactics = []
        # self.formal_theorem = 
        self.goals = []
        self.error = False
        self.messages = res.get('messages')
        if self.messages == None:self.messages = res.get("message")
        self.sorries = res.get("sorries")
        self.env = res.get("env")
        if self.messages:
            if isinstance(self.messages,str):
                if self.messages.find("error")!=-1:
                    self.error = True
            else:
                for i in self.messages:
                    if i["severity"].find('error')!=-1 and not i['data'].startswith("unsolved goals"):
                        self.error = True
        else:
            if not self.sorries:
                self.error = False
                self.finishFlag = True
        if state_type == 'tactic':
            self.init_tacticState(res)
        elif state_type == 'have':
            self.init_haveTacticState(res)
        else:
            self.init_cmdState(res)

    def getTacticState(self) -> str:
        """Get the current proof state"""
        if len(self.goals)==0:
            return "no goals"
        goal = self.goals[0]
        if isinstance(goal,list):
            if len(goal):
                goal_ = ""
                for i in goal:
                    goal_ += i
                return goal_
            else: return "no goals"
        else:
            return goal
    def init_haveTacticState(self, res):
        self.init_cmdState(res)
        self.proofStates.append((res.get('proofState')))
        self.goals.append(res.get("goals"))
    def init_cmdState(self, res):
        if self.sorries and self.sorries != []:
            self.finishFlag = False
            self.proofStates.append(self.sorries[-1]["proofState"])
            self.goals.append(self.sorries[-1]["goal"])

    def init_tacticState(self, res):
        self.proofStates.append((res.get('proofState')))
        self.goals.append(res.get("goals"))

        if self.goals[0] == None:
            self.error = True
        if not self.error and len(self.goals[0]) == 0:
            self.finishFlag = True
        else:
            self.finishFlag = False

    def isFinish(self):
        return self.finishFlag

    def isError(self):
        return self.error

    def print(self):
        if self.proofStates:
            print("proofStates:", self.proofStates)
        if self.goals:
            print("goals:", self.goals)
        print("error:", self.error)
        print("messages:", self.messages)
        print("sorries:", self.sorries) # only present in cmdState
        print("is finish:", self.finishFlag)
        print()

class Lean4Kit:
    def __init__(self, work_dir, repl_version, verbose=False):
        repl_path = Path(__file__).parent.resolve() / f'repl_v{repl_version}'

        cmd = f"lake env {repl_path}"

        try:
            self.proc = subprocess.Popen(
                cmd,
                cwd=work_dir,
                shell=True,  # support string commands
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True  # use text mode
            )


        except Exception as e:
            raise RuntimeError(f"Failed to start process: {e}")

    def run_import(self, code, env=None, verbose=False):
        if env != None:
            command = json.dumps({
                "cmd": code,
                "env": env
            })
        else:
            command = json.dumps({
                "cmd": code
            })
        return self.__runCommand__(command, verbose=verbose)

    def new_thm(self, code, env=None, verbose=False):
        if env != None:
            command = json.dumps({
                "cmd": code+" := by sorry",
                "env": env
            })
        else:
            command = json.dumps({
                "cmd": code+" := by sorry"
            })
        try:
            result = self.__runCommand__(command, verbose=verbose)
        except TypeError:
            raise TheoremInitException("Theorem environment error or theorem description error")
        return result
    def run_tactic(self, tactic, proofState, cmd_type='tactic', verbose=False):
        command = json.dumps({
                "tactic": tactic,
                "proofState": proofState
            })
        return self.__runCommand__(command, cmd_type, verbose)
    def run_have_tactic(self, tactic, proofState, cmd_type='have', verbose=False):
        command = json.dumps({
                "tactic": tactic+":= by sorry",
                "proofState": proofState
            })
        return self.__runCommand__(command, cmd_type, verbose)
    def is_correct_and_finished(self, code, verbose=False,timeout=160):
        """
        Verify correctness of complete code
        """
        command = json.dumps({
            "cmd": code,
            "nc": True
        })
        try:
            stat = self.__runCommand__(command, verbose=verbose,timeout=timeout)# set timeout larger, otherwise verification of longer theorems may fail
        except:
            raise VerificationFailedException("Error while verifying theorem correctness")
        messages = stat.messages
        sorries = stat.sorries
        # stat.print()
        if sorries and len(sorries): return False
        print("messages:", messages)
        if messages:
            if isinstance(messages,str):
                if messages.find("error")!=-1:
                    return False
            else:
                for i in messages:
                    if i["severity"]=="warning" and i["data"].find('sorry')!=-1:
                        return False # incomplete
                    elif i["severity"]=="error":
                        return False # error
        return True

    def verify_sketch(self, code, verbose=False, timeout=300) -> tuple[bool, str]:
        """Verify a proof sketch that may contain sorry placeholders.

        Returns (ok, msg):
            ok  – True if the code has no Lean *errors* (sorry warnings are OK).
            msg – empty string if ok, otherwise the first error message.
        """
        command = json.dumps({"cmd": code, "nc": True})
        try:
            stat = self.__runCommand__(command, verbose=verbose, timeout=timeout)
        except Exception as e:
            return False, str(e)
        messages = stat.messages or []
        if isinstance(messages, str):
            if "error" in messages:
                return False, messages
            return True, ""
        for m in messages:
            if isinstance(m, dict) and m.get("severity") == "error":
                return False, m.get("data", "unknown error")
        return True, ""

    def run_allTactics(self, code, env=None, verbose=True):
        """Get JSON-format infotree, slow for longer theorems"""
        if env:
            command = json.dumps({
                "cmd": code,
                "infotree": "substantive"
            })
        else:
            command = json.dumps({
                "cmd": code,
                "infotree": "substantive"
            })

        try:
            self.proc.stdin.write(command + "\n")
            self.proc.stdin.flush()

            response = ""
            self.proc.stdin.write("\n")
            self.proc.stdin.flush()
            while True:
                line = self.proc.stdout.readline()  # read output line by line
                if not line:
                    break
                response += line
                # print(response)
                try:
                    json_data = json.loads(response)
                    return json_data
                except json.JSONDecodeError:
                    continue

        except Exception as e:
            raise RuntimeError(f"Command execution failed: {e}")
   # Code without timeout 
    # def __send_command(self, command, timeout=20):
    #     """Send command to subprocess and get output"""
    #     if self.proc.stdin is None or self.proc.stdout is None:
    #         raise RuntimeError("Subprocess I/O not available")

    #     try:
    #         # Write command
    #         self.proc.stdin.write(command + "\n")
    #         self.proc.stdin.flush()

    #         # Wait for subprocess response
    #         response = ""
    #         self.proc.stdin.write("\n")
    #         self.proc.stdin.flush()

    #         while True:
    #             line = self.proc.stdout.readline()
    #             if not line:  # subprocess ended
    #                 break
    #             response += line
    #             try:
    #                 # Try to parse JSON data
    #                 json_data = json.loads(response)
    #                 return json_data
    #             except json.JSONDecodeError:
    #                 # Incomplete JSON data, continue reading
    #                 continue

    #     except Exception as e:
    #         raise RuntimeError(f"Command execution failed: {e}")

    def __send_command(self, command, timeout=60):
        """Send command to subprocess and get output, with timeout"""
        if self.proc.stdin is None or self.proc.stdout is None:
            raise RuntimeError("Subprocess I/O not available")

        try:
            self.proc.stdin.write(command + "\n")
            self.proc.stdin.flush()

            response = ""
            self.proc.stdin.write("\n")
            self.proc.stdin.flush()

            start_time = time.time()

            while True:
                elapsed_time = time.time() - start_time
                if elapsed_time > timeout:
                    raise TimeoutError(f"Command execution timed out ({timeout} seconds)")

                line = self.proc.stdout.readline()
                if not line:  # subprocess ended
                    break
                response += line
                try:
                    # Try to parse JSON data
                    json_data = json.loads(response)
                    return json_data
                except json.JSONDecodeError:
                    # Incomplete JSON data, continue reading
                    continue
        except TimeoutError as te:
            raise TimeoutError(f"Command timed out: {te}")
        except Exception as e:
            raise RuntimeError(f"Command execution failed: {e}")

    def __runCommand__(self, command, cmd_type="cmd", verbose=False,timeout=60):
        """Run command and return TacticState"""
        try:
            json_response = self.__send_command(command,timeout=timeout)
            return TacticState(json_response, cmd_type)
        except json.JSONDecodeError as e:
            raise InteractiveEOFException(f"Failed to parse JSON: {e}")
        except Exception as e:
            raise RuntimeError(f"Command execution failed: {e}")
    def close(self):
        if self.proc:
            self.proc.terminate()
            self.proc.wait()
