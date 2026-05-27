

class TheoremInitException(Exception):
    '''Exception occurred when creating environment with interactive tool'''
    def __init__(self, *args):
        super().__init__(*args)

class TacticApplyException(Exception):
    '''Incorrect proof tactic was used'''
    def __init__(self, *args):
        super().__init__(*args)

class ProofStateException(Exception):
    '''Error in the current interactive proof state'''
    def __init__(self, *args):
        super().__init__(*args)

class InteractiveTimeoutException(Exception):
    '''Interactive timeout exception'''
    def __init__(self, *args):
        super().__init__(*args)
class VerificationFailedException(Exception):
    '''Exception during verification'''
    def __init__(self, *args):
        super().__init__(*args)
class InteractiveEOFException(Exception):
    """Exception during interaction"""
    def __init__(self, *args):
        super().__init__(*args)