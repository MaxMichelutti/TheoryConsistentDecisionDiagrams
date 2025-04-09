"""theory BDD module"""

import json
import time
import os
import logging
from typing import Dict, List
from collections.abc import Iterator
from pysmt.fnode import FNode
import pydot
from dd import cudd as cudd_bdd
from theorydd import formula
from theorydd.util._dd_dump_util import change_bbd_dot_names as _change_bbd_dot_names
from theorydd.util._string_generator import SequentialStringGenerator
from theorydd.util._utils import (
    cudd_dump as _cudd_dump,
    cudd_load as _cudd_load,
    get_solver as _get_solver,
)
from theorydd.solvers.solver import SMTEnumerator
from theorydd.formula import get_atoms
from theorydd.walkers.walker_bdd import BDDWalker
from theorydd.solvers.lemma_extractor import find_qvars
from theorydd.constants import SAT
from theorydd.tdd.theory_dd import TheoryDD


class TheoryBDD(TheoryDD):
    """Class to generate and handle T-BDDs

    TBDDs are BDDs with a mixture of boolean atoms and T-atoms
    in which every branch represents a T-consistent truth
    assignment to the atoms of the encoded formula"""

    bdd: cudd_bdd.BDD
    root: cudd_bdd.Function
    qvars: List[FNode]
    abstraction: Dict[FNode, str]
    refinement: Dict[str, FNode]
    logger: logging.Logger
    ordering: List[FNode]
    structure_name: str

    def __init__(
        self,
        phi: FNode,
        solver: str | SMTEnumerator = "total",
        tlemmas: List[FNode] | None = None,
        load_lemmas: str | None = None,
        sat_result: bool | None = None,
        use_ordering: List[FNode] | None = None,
        folder_name: str | None = None,
        computation_logger: Dict = None,
    ) -> None:
        """Builds a T-BDD. The construction requires the
        computation of All-SMT for the provided formula to
        extract T-lemmas and the subsequent construction of
        a BDD of phi & lemmas

        Args:
            phi (FNode) : a pysmt formula
            solver (str | SMTEnumerator) ["total"]: specifies which solver to use for All-SMT computation.
                Valid solvers are "partial", "total" and "extended_partial", or you can pass an instance of a SMTEnumerator
            tlemmas (List[Fnode] | None): use previously computed tlemmas.
                This skips the All-SMT computation
            load_lemmas (str | None) [None]: specify the path to a file from which to load the tlemmas.
                This skips the All-SMT computation
            sat_result (bool | None) [None]: the result of the All-SMT computation. This value is overwritten if t-lemmas are not provided!!!
            use_ordering (List[FNode] | None) [None]: the ordering of the variables in the BDD.
            folder_name (str | None) [None]: the path to a folder where data to load the T-BDD is stored.
                If this is not None, then all other parameters are ignored
            computation_logger (Dict | None) [None]: a dictionary that will be updated to store computation info.
        """
        if not hasattr(self, "logger"):
            self.logger = logging.getLogger("theorydd_bdd")
        super().__init__()
        if folder_name is not None:
            if not isinstance(solver, SMTEnumerator):
                solver = None
            self._load_from_folder(folder_name, normalization_solver=solver)
            return
        if not hasattr(self, "structure_name"):
            self.structure_name = "T-BDD"
        if computation_logger is None:
            computation_logger = {}
        if computation_logger.get(self.structure_name) is None:
            computation_logger[self.structure_name] = {}

        # NORMALIZE PHI
        if isinstance(solver, str):
            smt_solver = _get_solver(solver)
        else:
            smt_solver = solver
        phi = self._normalize_input(
            phi, smt_solver, computation_logger[self.structure_name]
        )

        # LOAD LEMMAS
        tlemmas, sat_result = self._load_lemmas(
            phi,
            smt_solver,
            tlemmas,
            load_lemmas,
            sat_result,
            computation_logger[self.structure_name],
        )

        # COMPUTE PHI AND LEMMAS
        phi_and_lemmas = formula.get_phi_and_lemmas(phi, tlemmas)

        # FIND QVARS
        self.qvars = find_qvars(
            phi,
            phi_and_lemmas,
            computation_logger=computation_logger[self.structure_name],
        )

        # THESE ATOMS SHOULD ALREADY BE NORMALIZED
        # SINCE THEY COME FROM A NORMALIZED FORMULA
        atoms = get_atoms(phi_and_lemmas)

        # CREATING VARIABLE MAPPING
        self.abstraction = self._compute_mapping(
            atoms, computation_logger[self.structure_name]
        )
        self.refinement = {v: k for k, v in self.abstraction.items()}

        # PREPARE FOR BUILDING
        start_time = time.time()
        self.logger.info("starting T-BDD preparation phase...")
        # compute the ordering
        if use_ordering is not None:
            # define ordering with the provided ordering after the qvars
            # to make existential quantification more efficient
            use_ordering = [
                formula.get_normalized(atom, smt_solver.get_converter())
                for atom in use_ordering
            ]
            self.ordering = self._complete_ordering(atoms, use_ordering)
        else:
            self.ordering = self._compute_ordering(atoms)
        # declare all variables
        self.bdd = cudd_bdd.BDD()
        ordering_abstraction = [self.abstraction[atom] for atom in self.ordering]
        self.bdd.declare(*ordering_abstraction)
        # set the correct ordering
        bdd_ordering = {}
        for i, item in enumerate(ordering_abstraction):
            bdd_ordering[item] = i
        cudd_bdd.reorder(self.bdd, bdd_ordering)
        # build walker
        walker = BDDWalker(self.abstraction, self.bdd)
        elapsed_time = time.time() - start_time
        self.logger.info(
            "BDD preparation phase completed in %s seconds", str(elapsed_time)
        )
        computation_logger[self.structure_name]["DD preparation time"] = elapsed_time

        if sat_result is None or sat_result == SAT:
            self.root = self._build(
                phi, tlemmas, walker, computation_logger[self.structure_name]
            )
        else:
            self.root = self._build_unsat(
                walker, computation_logger[self.structure_name]
            )

    def _compute_ordering(self, atoms: List[FNode]) -> List[FNode]:
        """computes the ordering of the variables

        Args:
            atoms (List[FNode]): the atoms of phi & tlemmas"""
        appended_values = set()
        order = []
        for atom in self.qvars:
            appended_values.add(atom)
            order.append(atom)
        for atom in atoms:
            if not atom in appended_values:
                order.append(atom)
        return order

    def _complete_ordering(
        self, atoms: List[FNode], use_ordering: List[FNode]
    ) -> List[FNode]:
        """completes the ordering provided by the user"""
        remaining_items = set(atoms)
        order = []
        # put qvars at the front
        for qvar in self.qvars:
            order.append(qvar)
            remaining_items.remove(qvar)
        # put requested order in the middle
        for item in use_ordering:
            order.append(item)
            remaining_items.remove(item)
        # put remaining items at the end
        for item in remaining_items:
            order.append(item)
        return order

    def _compute_mapping(
        self, atoms: List[FNode], computation_logger: dict
    ) -> Dict[FNode, str]:
        """computes the mapping"""
        start_time = time.time()
        self.logger.info("Creating mapping...")
        mapping = {}

        string_generator = SequentialStringGenerator()
        for atom in atoms:
            mapping[atom] = string_generator.next_string()
        elapsed_time = time.time() - start_time
        self.logger.info("Mapping created in %s seconds", str(elapsed_time))
        computation_logger["variable mapping creation time"] = elapsed_time
        return mapping

    def _enumerate_qvars(
        self, tlemmas_dd: object, mapped_qvars: List[object]
    ) -> object:
        return cudd_bdd.and_exists(tlemmas_dd, self.bdd.true, mapped_qvars)

    def __len__(self) -> int:
        """returns the number of nodes in the T-BDD"""
        return len(self.root)

    def count_nodes(self) -> int:
        """returns the number of nodes in the T-BDD"""
        return len(self)

    def count_vertices(self) -> int:
        """returns the number of nodes in the T-BDD"""
        return len(self) * 2

    def count_models(self) -> int:
        """returns the amount of models in the T-BDD"""
        try:
            total = self.root.count(
                nvars=len(self.abstraction.keys()) - len(self.qvars)
            )
        except RuntimeError:
            # sometimes CUDD throws a RuntimeError when counting models
            # when it runs out of memory
            total = -1
        return total

    def graphic_dump(
        self,
        output_file: str,
        dump_abstraction: bool = False,
    ) -> None:
        """Save the T-SDD on a file with Graphviz

        Args:
            output_file (str): the path to the output file
            dump_abstraction (bool) [False]: set it to True to dump a DD
                with the names of the abstraction of the atoms instead of the
                full names of atoms
        """
        temporary_dot = "bdd_temporary_dot.dot"
        reverse_mapping = self.refinement
        if output_file.endswith(".dot"):
            self.bdd.dump(output_file, filetype="dot", roots=[self.root])
            if not dump_abstraction:
                _change_bbd_dot_names(output_file, reverse_mapping)
        elif output_file.endswith(".svg"):
            self.bdd.dump(temporary_dot, filetype="dot", roots=[self.root])
            if not dump_abstraction:
                _change_bbd_dot_names(temporary_dot, reverse_mapping)
            with open(temporary_dot, "r", encoding="utf8") as dot_content:
                (graph,) = pydot.graph_from_dot_data(dot_content.read())
                graph.write_svg(output_file)
            os.remove(temporary_dot)
        else:
            self.logger.info("Unable to dump T-BDD file: format not unsupported")
            return

    def get_ordering(self) -> List[FNode]:
        """Returns the ordering of the variables"""
        return self.ordering

    def is_sat(self) -> bool:
        """Returns True if the encoded formula is satisfiable"""
        return self.root != self.bdd.false

    def _get_care_vars(self) -> List[str]:
        dont_care_vars = set([self.abstraction[qvar] for qvar in self.qvars])
        all_vars = set(self.abstraction.values())
        care_vars = all_vars.difference(dont_care_vars)
        return care_vars

    def is_valid(self) -> bool:
        """Returns True if the encoded formula is valid

        Raises:
            QueryError: if the model counting fails
        """
        return self.root == self.bdd.true

    def pick(self) -> Dict[FNode, bool] | None:
        """Returns a partial model of the encoded formula,
        None if the formula is unsatisfiable"""
        if not self.is_sat():
            return None
        return self._convert_assignment(self.root.pick())

    def _convert_assignment(self, assignment):
        return {self.refinement[var]: truth for var, truth in assignment.items()}

    def pick_all(self) -> List[Dict[FNode, bool]]:
        """Returns all partial models of the encoded formula"""
        if not self.is_sat():
            return []
        care_vars = self._get_care_vars()
        items = list(self.bdd.pick_iter(self.root, care_vars))
        return [self._convert_assignment(i) for i in items]

    def pick_all_iter(self) -> Iterator[Dict[FNode, bool]]:
        """Returns all partial models of the encoded formula"""
        if not self.is_sat():
            return
        care_vars = self._get_care_vars()
        for item in self.bdd.pick_iter(self.root, care_vars):
            yield self._convert_assignment(item)

    def condition(self, condition: str) -> None:
        """Condition the T-BDD over a given atom

        Args:
            condition (str): the label of atom over which to condition
        """
        negated = False
        if condition.startswith("-"):
            negated = True
            condition = condition[1:]
        condition_bdd = self.bdd.add_expr(condition)
        if negated:
            condition_bdd = ~condition_bdd
        self.root = self.root & condition_bdd

    def save_to_folder(self, folder_path: str) -> None:
        """Save all the T-BDD data inside files in the specified folder

        Args:
            file_path (str): the path to the output file
        """
        # CHECK IF FOLDER EXISTS AND CREATE IT IF NOT
        if not os.path.exists(folder_path):
            os.makedirs(folder_path)
        # SAVE MAPPING
        formula.save_abstraction_function(
            self.abstraction, f"{folder_path}/abstraction.json"
        )
        # SAVE QVARS
        qvars_indexes = [self.abstraction[qvar] for qvar in self.qvars]
        with open(f"{folder_path}/qvars.qvars", "w", encoding="utf8") as out:
            json.dump(qvars_indexes, out)
        # SAVE DD
        _cudd_dump(self.root, f"{folder_path}/tbdd_data")

    def _load_from_folder(
        self, folder_path: str, normalization_solver: SMTEnumerator | None = None
    ) -> None:
        """Load a T-BDD from a folder

        Args:
            folder_path (str): the path to the folder where the data is stored
            normalization_solver (SMTEnumerator | None) [None]: the solver to use for normalization
        """
        if not os.path.exists(folder_path):
            raise FileNotFoundError(
                f"Cannot load T-BDD: Folder {folder_path} does not exist, cannot load T-BDD"
            )
        if not os.path.isfile(f"{folder_path}/abstraction.json"):
            raise FileNotFoundError(
                f"Cannot load T-BDD: File {folder_path}/abstraction.json does not exist"
            )
        if not os.path.isfile(f"{folder_path}/qvars.qvars"):
            raise FileNotFoundError(
                f"Cannot load T-BDD: File {folder_path}/qvars.qvars does not exist"
            )
        if normalization_solver is None:
            normalization_solver = _get_solver("total")
        abstraction = formula.load_abstraction_function(
            f"{folder_path}/abstraction.json"
        )
        self.abstraction = {
            formula.get_normalized(k, normalization_solver.get_converter()): v
            for k, v in abstraction.items()
        }
        self.refinement = {v: k for k, v in self.abstraction.items()}
        self.bdd = cudd_bdd.BDD()
        self.root, ordering_dict = _cudd_load(f"{folder_path}/tbdd_data", self.bdd)
        self.ordering = [0] * len(ordering_dict)
        for k, v in ordering_dict.items():
            self.ordering[v] = self.refinement[k]
        # load qvars
        with open(f"{folder_path}/qvars.qvars", "r", encoding="utf8") as input_data:
            qvars_indexes = json.load(input_data)
            self.qvars = [self.refinement[qvar_id] for qvar_id in qvars_indexes]


def tbdd_load_from_folder(
    folder_path: str, normalizer_solver: SMTEnumerator | None = None
) -> TheoryBDD:
    """Load a T-BDD from a file

    Args:
        file_path (str): the path to the file
        normalizer_solver (SMTEnumerator | None) [None]: the solver to use for normalization

    Returns:
        TheoryBDD: the T-BDD loaded from the file
    """
    if normalizer_solver is None:
        normalizer_solver = _get_solver("total")
    return TheoryBDD(None, folder_name=folder_path, solver=normalizer_solver)
