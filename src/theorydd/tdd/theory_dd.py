"""interface for the theory DD classes"""

from abc import ABC, abstractmethod
from collections.abc import Iterator
import logging
import time
from typing import Dict, List, Tuple

from pysmt.fnode import FNode

from theorydd import formula
from theorydd.solvers.lemma_extractor import extract
from theorydd.solvers.solver import SMTEnumerator
from theorydd.walkers.walker_bdd import DagWalker as DDWalker


class TheoryDD(ABC):
    """interface for the theory DD classes

    This interface must be implemented by all the theory DDs that are used to compute all-SMT.
    """

    def __init__(self):
        if not hasattr(self, "abstraction"):
            self.abstraction = {}
        if not hasattr(self, "refinement"):
            self.refinement = {}
        if not hasattr(self, "qvars"):
            self.qvars = []
        if not hasattr(self, "logger"):
            self.logger = logging.getLogger("theorydd_tdd")

    def _normalize_input(
        self, phi: FNode, solver: SMTEnumerator, computation_logger: Dict
    ) -> FNode:
        """normalizes the input"""
        start_time = time.time()
        self.logger.info("Normalizing phi according to solver...")
        phi = formula.get_normalized(phi, solver.get_converter())
        elapsed_time = time.time() - start_time
        self.logger.info("Phi was normalized in %s seconds", str(elapsed_time))
        computation_logger["phi normalization time"] = elapsed_time
        return phi

    def _load_lemmas(
        self,
        phi: FNode,
        smt_solver: SMTEnumerator,
        tlemmas: List[FNode] | None,
        load_lemmas: str | None,
        sat_result: bool | None,
        computation_logger: Dict,
    ) -> Tuple[List[FNode], bool | None]:
        """loads the lemmas"""
        # LOADING LEMMAS
        start_time = time.time()
        self.logger.info("Loading Lemmas...")
        if tlemmas is not None:
            computation_logger["ALL SMT mode"] = "loaded"
        elif load_lemmas is not None:
            computation_logger["ALL SMT mode"] = "loaded"
            tlemmas = [formula.read_phi(load_lemmas)]
        else:
            computation_logger["ALL SMT mode"] = "computed"
            sat_result, tlemmas, _bm = extract(
                phi,
                smt_solver,
                computation_logger=computation_logger,
            )
        tlemmas = list(
            map(
                lambda l: formula.get_normalized(l, smt_solver.get_converter()), tlemmas
            )
        )
        # BASICALLY PADDING TO AVOID POSSIBLE ISSUES
        while len(tlemmas) < 2:
            tlemmas.append(formula.top())
        elapsed_time = time.time() - start_time
        self.logger.info("Lemmas loaded in %s seconds", str(elapsed_time))
        computation_logger["lemmas loading time"] = elapsed_time
        return tlemmas, sat_result

    def _build_unsat(self, walker: DDWalker, computation_logger: Dict) -> object:
        """builds the T-DD for an UNSAT formula

        Returns the root of the DD"""
        start_time = time.time()
        self.logger.info("Building T-DD for UNSAT formula...")
        root = walker.walk(formula.bottom())
        elapsed_time = time.time() - start_time
        self.logger.info(
            "T-DD for UNSAT formula built in %s seconds", str(elapsed_time)
        )
        computation_logger["UNSAT DD building time"] = elapsed_time
        return root

    def _build(
        self,
        phi: FNode,
        tlemmas: List[FNode],
        walker: DDWalker,
        computation_logger: Dict,
    ) -> None:
        """Builds the T-DD"""
        # DD for phi
        start_time = time.time()
        self.logger.info("Building DD for phi...")
        phi_bdd = walker.walk(phi)
        elapsed_time = time.time() - start_time
        self.logger.info("DD for phi built in %s seconds", str(elapsed_time))
        computation_logger["phi DD building time"] = elapsed_time

        # DD for t-lemmas
        start_time = time.time()
        self.logger.info("Building T-DD for big and of t-lemmas...")
        tlemmas_dd = walker.walk(formula.big_and(tlemmas))
        elapsed_time = time.time() - start_time
        self.logger.info("DD for T-lemmas built in %s seconds", str(elapsed_time))
        computation_logger["t-lemmas DD building time"] = elapsed_time

        # ENUMERATING OVER FRESH T-ATOMS
        mapped_qvars = [self.abstraction[atom] for atom in self.qvars]
        if len(mapped_qvars) > 0:
            start_time = time.time()
            self.logger.info("Enumerating over fresh T-atoms...")
            tlemmas_dd = self._enumerate_qvars(tlemmas_dd, mapped_qvars)
            elapsed_time = time.time() - start_time
            self.logger.info(
                "fresh T-atoms quantification completed in %s seconds",
                str(elapsed_time),
            )
            computation_logger["fresh T-atoms quantification time"] = elapsed_time
        else:
            computation_logger["fresh T-atoms quantification time"] = 0

        # JOINING PHI BDD AND TLEMMAS BDD
        start_time = time.time()
        self.logger.info("Joining phi DD and lemmas T-DD...")
        root = phi_bdd & tlemmas_dd
        elapsed_time = time.time() - start_time
        self.logger.info(
            "T-DD for phi and t-lemmas joint in %s seconds", str(elapsed_time)
        )
        computation_logger["DD joining time"] = elapsed_time
        return root

    @abstractmethod
    def _enumerate_qvars(
        self, tlemmas_dd: object, mapped_qvars: List[object]
    ) -> object:
        """enumerates over the fresh T-atoms"""
        raise NotImplementedError()

    @abstractmethod
    def _load_from_folder(self, folder_path: str):
        """loads the DD from a folder"""
        pass

    @abstractmethod
    def save_to_folder(self, folder_path: str):
        """saves the DD to a folder"""
        pass

    @abstractmethod
    def __len__(self) -> int:
        """returns the number of nodes in the DD"""
        pass

    @abstractmethod
    def count_nodes(self) -> int:
        """Returns the number of nodes in the DD"""
        pass

    @abstractmethod
    def count_vertices(self) -> int:
        """Returns the number of nodes in the DD"""
        pass

    @abstractmethod
    def count_models(self) -> int:
        """Returns the amount of models in the DD"""
        pass

    @abstractmethod
    def graphic_dump(self, output_file: str) -> None:
        """Save the DD on a file

        Args:
            output_file (str): the path to the output file
        """
        pass

    def get_mapping(self) -> Dict[FNode, str]:
        """Returns the variable mapping used,
        which defines the abstraction function"""
        return self.get_abstraction()

    def get_abstraction(self) -> Dict[FNode, object]:
        """Returns the abstraction function"""
        return self.abstraction

    def get_refinement(self) -> Dict[object, FNode]:
        """Returns the refinement function"""
        return self.refinement

    @abstractmethod
    def pick(self) -> Dict[FNode, bool] | None:
        """Returns a model of the encoded formula"""
        pass

    @abstractmethod
    def pick_all_iter(self) -> Iterator[Dict[FNode, bool]]:
        """Returns an iterator over the models of the encoded formula"""
        pass

    @abstractmethod
    def pick_all(self) -> List[Dict[FNode, bool]]:
        """returns a list of all the models in the encoded formula"""
        pass

    @abstractmethod
    def is_sat(self) -> bool:
        """Returns True if the encoded formula is satisfiable"""
        pass

    @abstractmethod
    def is_valid(self) -> bool:
        """Returns True if the encoded formula is valid"""
        pass
