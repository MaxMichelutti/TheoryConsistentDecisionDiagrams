"""module for extracting lemmas from all SMT formulas through all SMT computation"""

import logging
import time
from typing import Dict, List, Tuple
from pysmt.fnode import FNode
from theorydd import formula
from theorydd.solvers.solver import SMTEnumerator
from theorydd.constants import SAT, UNSAT


def extract(
    phi: FNode,
    smt_solver: SMTEnumerator,
    enumerate_true: bool = False,
    use_boolean_mapping: bool = True,
    computation_logger: Dict = None,
) -> Tuple[bool, List[FNode], Dict[FNode,FNode] | None]:
    """extract lemmas from a SMT-formula

    Args:
        phi (FNode): a pysmt formula
        smt_solver (SMTEnumerator): the SMT solver to be used for lemma extraction
        enumerate_true (bool) [False]: if set to True, enumerate all T-lemmas possible
            over the atoms of phi
        use_boolean_mapping (bool) [False]: optional for SMTEnumerator, if the solver 
            supports enumerating thorugh a boolean mapping
        computation_logger (Dict) [None]: a dictionary that will be updated to store computation info

    Returns:
        bool: SAT or UNSAT depnding on SMT-solver output
        List[FNode]: the list of lemmas extracted from phi. If phi is UNSAT this list is contains the lemmas that give T-unsatisfiability
        Dict | None: when using a boolean mapping the boolean mapping used, otherwise None
    """
    logger = logging.getLogger("theorydd_lemma_extractor")
    logger.info("Computing AllSMT...")
    if computation_logger is None:
        computation_logger = {}
    boolean_mapping = None
    if use_boolean_mapping:
        boolean_mapping = formula.get_boolean_mapping(phi)
    start_time = time.time()
    if enumerate_true:
        smt_result = smt_solver.enumerate_true(phi)
    else:
        smt_result = smt_solver.check_all_sat(phi, boolean_mapping)
    elapsed_time = time.time() - start_time
    logger.info("Computed AllSMT in %s seconds", str(elapsed_time))
    computation_logger["All-SMT computation time"] = elapsed_time
    lemmas = smt_solver.get_theory_lemmas()
    computation_logger["T-lemmas amount"] = len(lemmas)
    if smt_result == UNSAT:
        logger.info("Phi is T-UNSAT")
        computation_logger["All-SMT result"] = "UNSAT"
        return UNSAT, lemmas, boolean_mapping
    logger.info("Phi is T-SAT")
    computation_logger["All-SMT result"] = "SAT"
    return SAT, lemmas, boolean_mapping


def find_qvars(
    original_phi: FNode, phi_and_lemmas: FNode, computation_logger: Dict = None
):
    """Finds the atoms on which to existentially quantify when building a T-DD (the fresh T-atoms from T-lemmas)

    Args:
        original_phi (FNode): a pysmt formulas without integrated lemmas
        phi_and_lemmas (FNode): the same pysmt formula as phi, but with integrated lemmas
        computation_logger (Dict) [None]: a dictionary that will be updated to store computation info

    Returns:
        bool: True if the solver is valid, False otherwise
    """
    logger = logging.getLogger("theorydd_find_qvars")
    if computation_logger is None:
        computation_logger = {}
    start_time = time.time()
    logger.info("Finding fresh atoms from all-sat computation...")
    phi_atoms = formula.get_atoms(original_phi)
    phi_lemma_atoms = formula.get_atoms(phi_and_lemmas)
    new_theory_atoms = []
    if len(phi_atoms) < len(phi_lemma_atoms):
        new_theory_atoms = formula.atoms_difference(phi_atoms, phi_lemma_atoms)
    computation_logger["fresh T-atoms detected"] = len(new_theory_atoms)
    elapsed_time = time.time() - start_time
    logger.info("Fresh atoms found in %s seconds", str(elapsed_time))
    computation_logger["fresh T-atoms detection time"] = elapsed_time
    return new_theory_atoms
