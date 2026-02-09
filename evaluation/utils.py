"""
    Given a path to a problem file 
    Returns true if the problem is labelled as unsatisfiable
"""
def isProblemUnsatisfiable(problem_path: str) -> bool:
    with open(problem_path, "r", encoding="utf-8") as f:
        problem: str = f.read()
        
    return "True" if "Unsatisfiable" in problem else "False"


"""
    The TPTP format can include a variety of different formats 
    Some contain fof formulas, these must be converted to CNF before they can be handled by our prover
    Other tptp files do not contain all the clauses in the file, but rather reference other axiom files 
    Since, currently we are only interested in solving problems already in clausal form 
    We only look at problems already in CNF with no references to axiom files
"""
def isClausalFormProblemWithNoAxiomReferences(problem_path):
    with open(problem_path, "r", encoding="utf-8") as f:
        problem: str = f.read()
        
    return "include(" not in problem and "cnf(" in problem


def withEquality(problem_path):
    with open(problem_path, "r", encoding="utf-8") as f:
        problem: str = f.read()
        
    return "=" in problem


def parseProverOutput(proofOutput: str) -> str:
    proofOutput = proofOutput.strip().splitlines()[-1]
        
    if proofOutput not in ["True", "False"]:
        return "Unexpected Output: " + proofOutput
    
    return proofOutput


def parseIproverOutput(proofOutput:str) -> str:
    proofOutput = proofOutput.strip()
    
    if "% SZS status Satisfiable" in proofOutput or "% SZS status CounterSatisfiable" in proofOutput: 
        return "False"

    if "% SZS status Unsatisfiable" in proofOutput or "SZS status Theorem" in proofOutput: 
        return "True"

    return "Unexpected Output: " + proofOutput

if __name__ == "__main__": 
    pass