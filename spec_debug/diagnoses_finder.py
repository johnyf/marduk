##  ===========================================================================
##  Author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
##
##  Copyright (c) 2009, 2010 by Graz University of Technology
##
##  This is free software; you can redistribute it and/or
##  modify it under the terms of the GNU Lesser General Public
##  License as published by the Free Software Foundation; either
##  version 2 of the License, or (at your option) any later version.
##
##  This software is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
##  Lesser General Public License for more details.
##
##  You should have received a copy of the GNU Lesser General Public
##  License along with this library; if not, write to the Free Software
##  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.
##
##  For more information about this software see <http://rat.fbk.eu/ratsy>
##  or email to the RATSY Team <ratsy@list.fbk.eu>.
##  Please report bugs to <ratsy@list.fbk.eu>.
##
##  ===========================================================================

"""
Contains a classes that are able to compute diagnoses for unrealizable specs.
"""

from spec_debug_utils import PLog
import time
from random import shuffle

class DiagnosesFinder(object):
    """
    Computes diagnoses for unrealizable specifications.

    This class is able to compute diagnoses for unrealizable specifications as
    suggested in 'R. Reiter: A Theory of Diagnosis from First Principles'.
    It uses the class L{ConflictFinder} to compute minimal conflicts, i.e.,
    (locally) minimal sets of guarantees and output signals that cannot all be
    correctly specified. If one assumes that all elements of a conflict are
    correct, then this gives an unrealizable specification. This class builds
    a hitting set tree in order to find minimal hitting sets for the set of
    minimal conflicts. Every such minimal hitting set is a diagnosis in the
    following sense: if all elements of a diagnosis are assumed to be incorrect,
    then this explains the unrealizability of the specification. So every
    diagnosis is a set of guarantees/outputs which are likely to be incorrect.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, utils, minimizer, min_target, max_elements,
                 max_diagnoses):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        @param minimizer: A class that implements a minimization algorithm. It
               is used for the computation of minimal conflicts.
        @type minimizer: L{Minimizer}
        @param min_target: Some implementation of the interface L{MinTarget}.
               It represents a specification and can be minimized by the
               minimizer.
        @type min_target: L{MinTarget}
        @param max_elements: The maximal number of elements in any diagnosis or
               None if there is no upper bound on the number of elements in a
               diagnosis.
        @type max_elements: int
        @param max_diagnoses: The maximal number diagnoses to compute of None
               if all diagnoses should be computed.
        @type max_diagnoses: int
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: The maximal number of elements in any diagnosis.
        #:
        #: The maximal number of elements in any diagnosis or None if there is
        #: no upper bound for the number of elements in diagnoses.
        #: @type: int
        self.__max_elements = max_elements

        #: The maximal number of diagnoses to compute.
        #:
        #: The maximal number of diagnoses to compute or None if all diagnoses
        #: should be computed.
        #: @type: int
        self.__max_diagnoses = max_diagnoses

        #: Some implementation of the interface L{MinTarget}.
        #:
        #: It represents a specification and can be minimized by the minimizer.
        #: @type: L{MinTarget}
        self.__min_target = min_target

        #: The set of diagnoses computed so far.
        #: @type: list<list<int>>
        self.__diagnoses = []

        #: The hitting set tree nodes that still have to be processed.
        #:
        #: All tree nodes that still have to be analyzed for children. (The tree
        #: is computed in a breath first search.)
        #: @type: list<HSTreeNode>
        self.__nodes_to_process = []

        #: All nodes of the hitting set tree that have been computed so far.
        #: @type: list<HSTreeNode>
        self.__all_nodes = []

        #: All sets of conflict elements already covered by a tree path.
        #: @type: list<list<int>>
        self.__already_covered = []

        #: A module which is able to compute minimal conflicts.
        #: @type: L{ConflictFinder}
        self.__conflict_finder = ConflictFinder(minimizer, min_target)

    def start(self):
        """
        Performs the computation of a hitting set tree to obtain diagnoses.

        This method uses the class L{ConflictFinder} to compute minimal
        conflicts, i.e., (locally) minimal sets of guarantees and output
        signals that cannot all be correctly specified. It builds a hitting set
        tree in order to find minimal hitting sets for the set of minimal
        conflicts. Every such minimal hitting set is a diagnosis.
        """

        # cleaning up the result of all previous computations:
        self.__diagnoses = []
        self.__all_nodes = []
        self.__already_covered = []
        self.__nodes_to_process = []

        # If we only compute single fault diagnoses, we could do that in a
        # performance optimized way. However, non of the following
        # optimization really resulted in an improvement.  I leave the code
        # as a comment for further experiments:
        #if self.__max_elements == 1:
        #    self._compute_signlefault_only()
        #    self._compute_signlefault_only2()
        #    return


        starttime = time.clock()

        # computing the first conflict
        conflict = self.__conflict_finder.compute_conflict_not_containing([])
        time_first_conflict = time.clock() - starttime
        checks_first_conflict = self.__min_target.get_check_statistics()

        # creating the root node of the hitting set tree:
        root_node = HSTreeNode(None)
        root_node.name = "n%d" % len(self.__all_nodes)
        root_node.node_type = HSTreeNode.INNER
        root_node.conflict = conflict
        self.__nodes_to_process.append(root_node)
        self.__all_nodes.append(root_node)

        # perform breath first search for children:
        msg = " Some statistics:\n"
        while self.__nodes_to_process != []:
            current_node = self.__nodes_to_process.pop(0)
            if self.__max_elements and \
               current_node.get_depth() >= self.__max_elements:
                msg += "  Aborted HSTree computation as all further diagnoses "
                msg += "would have more than %d " % self.__max_elements
                msg += "elememts.\n"
                break
            if not self._compute_children(current_node):
                msg += "  Aborted HSTree computation as the desired number of "
                msg += "%d diagnoses has already been " % self.__max_diagnoses
                msg += "obtained.\n"
                break

        # logging some statistics:
        msg += "  Computation of first conflict took "
        msg += "%.2f seconds\n" % time_first_conflict
        msg += "  For the first conflict:\n" + checks_first_conflict
        msg += "  %d diagnoses found\n" % len(self.__diagnoses)
        msg += "  Diagnoses computation took "
        msg += "%.2f seconds\n" % (time.clock() - starttime)
        msg += self.__conflict_finder.get_statistics()
        msg += self.__min_target.get_check_statistics()
        PLog.log(msg)

    def write_hstree_dot(self, filename):
        """
        Writes the obtained hitting set tree in DOT format into a file.

        This method writes the obtained hitting set tree in DOT format into a
        file. Pictures of the tree can then be produced by typing
        'dot -Tpdf -o ./picture.pdf ./filename'
        for example.

        @param filename: The name of the file to write the HSTree to.
        @type filename: string
        """
        dot_file = open(filename , 'w')
        dot_file.write("digraph G {\n")
        dot_file.write("  node [shape = record];\n")
        dot_file.write("  subgraph cluster1 {\n")

        # creating the description of the nodes:
        dot_file.write("    subgraph cluster11 {\n")
        dot_file.write("      A[label = \"{node name | node type | ")
        dot_file.write("conflict}\"];\n")
        dot_file.write("      label = \"Node Contents\";\n")
        dot_file.write("    }\n")

        # creating the translation of the numbers:
        dot_file.write("    B[label = \"{Abbreviations:|{")
        raw_conflicts = self.__conflict_finder.get_raw_conflicts()
        all_elements = set([])
        for conflict in raw_conflicts:
            all_elements = all_elements | set(conflict)
        all_elements_list = list(all_elements)
        all_elements_list.sort()
        for count in range(0,len(all_elements_list)):
            if count != 0 and count % 4 == 0:
                dot_file.write(" | ")
            name = self.__min_target.get_string_rep([all_elements_list[count]])
            name = name.replace("{", " ").replace("}", " ")
            dot_file.write(" %d = %s\\n" %(all_elements_list[count], name))
        dot_file.write("}}\"];\n")
        dot_file.write("    label = \"Explanation\";\n")
        dot_file.write("    color=blue;\n")
        dot_file.write("  }")

        # creating the tree itself:
        dot_file.write("  subgraph cluster2 {\n")
        for node in self.__all_nodes:
            dot_file.write(node.to_dot())
        dot_file.write("  }\n")
        dot_file.write("  B -> n0[color=white];")
        dot_file.write("}\n")
        dot_file.close()

    def use_conflict(self, conflict_index):
        """
        Informs the L{MinTarget} about the final solution of a minimization.

        This method informs the L{MinTarget} about the final solution of a
        particular minimization, i.e., about a particular minimal conflict.
        Each minimal conflict is an unrealizable core. The L{MinTarget} can
        store this final solution if desired so that it can be used for all
        further steps.

        @param conflict_index: The index of the conflict to be used and stored
               as unrealizable core.
        @type conflict_index: int
        """

        self.__conflict_finder.use_conflict(conflict_index)

    def get_diagnoses(self):
        """
        Returns the computed diagnoses in human readable form.

        This method returns the computed diagnoses in human readable form, i.e.,
        all guarantees or outputs are referred to with their name rather than
        their index.

        @return: The computed diagnoses in human readable form.
        @rtype: list<list<string>>
        """

        res = []
        for diagnosis in self.__diagnoses:
            res.append(self.__min_target.get_string_rep(diagnosis))
        return res

    def get_conflicts(self):
        """
        Returns the computed minimal conflicts in human readable form.

        This method returns the computed minimal conflicts in human readable
        form, i.e., all guarantees or outputs are referred to with their name
        rather than their index. Each minimal conflict is an unrealizable core.

        @return: The computed minimal conflicts in human readable form.
        @rtype: list<list<string>>
        """

        return self.__conflict_finder.get_conflicts()

    def write_diagnoses(self, filename):
        """
        Writes the computed diagnoses in human readable form into a file.

        This method writes the computed diagnoses in human readable form into
        a file. Human readable means: all guarantees or outputs are referred to
        with their name rather than their index.

        @param filename: The name of the file to write to.
        @type filename: string
        """

        diagnoses_file = open(filename , 'w')
        for diagnosis in self.get_diagnoses():
            diagnoses_file.write(str(diagnosis) + "\n")
        diagnoses_file.close()

    def write_conflicts(self, filename):
        """
        Writes the computed minimal conflicts in human readable form to a file.

        This method writes the computed minimal conflicts in human readable
        form into a file. Human readable means: all guarantees or outputs are
        referred to with their name rather than their index. Each minimal
        conflict is an unrealizable core.

        @param filename: The name of the file to write to.
        @type filename: string
        """

        conflicts_file = open(filename , 'w')
        count = 0
        for conflict in self.get_conflicts():
            conflicts_file.write("%d: %s\n" % (count,str(conflict)))
            count += 1
        conflicts_file.close()

    def _compute_signlefault_only2(self):
        """
        Computes single fault diagnoses in a performance optimized way.

        This method computes single fault diagnoses in a performance optimized
        way. A minimal conflict is computed first. Then one conflict element
        after the other is taken away from the specification to see if there is
        still a conflict. If not, then a diagnosis is found. Otherwise we
        compute another minimal conflict. The second conflict is intersected
        with the first one to rule out diagnosis candidates. This is done
        because computing a minimal conflict is often faster than doing one
        realizability check. Additionally, there is the change of ruling out
        lots of diagnosis candidates at once. However, experiments show that
        the intersection with the second conflict does not really improve
        the performance. This method is never called. It is left in the code
        for future experiments.
        """

        starttime = time.clock()

        # computing the first conflict
        finder = self.__conflict_finder
        conflict = finder.compute_conflict_not_containing([])
        time_first_conflict = time.clock() - starttime
        time_second_conflict = 0.0
        checks_first_conflict = self.__min_target.get_check_statistics()

        # removing one conflict element after the other from the specification:
        msg = " Some statistics:\n"
        elements_to_check = conflict[:]
        done_once = False # intersection with second conflict is done only once
        elems_before = 0
        elems_after = 0
        while len(elements_to_check) > 0:
            elem = elements_to_check.pop(0)
            if self.__max_diagnoses and \
               len(self.__diagnoses) >= self.__max_diagnoses:
                msg += "  Aborted single fault diagnosis computation as the "
                msg += "desired number of %d diagnoses " % self.__max_diagnoses
                msg += "has already been obtained.\n"
                break
            if not finder.exists_conflict_not_containing([elem]):
                # if we remove the element, the spec is realizable
                # --> the element is a diagnosis:
                self.__diagnoses.append([elem])
            elif done_once == False and len(elements_to_check) >= 3:
                # otherwise we compute a second minimal conflict (if we have
                # not already done so):
                done_once = True
                elems_before = len(elements_to_check)
                st = time.clock()
                new_confl = finder.compute_conflict_not_containing([elem])
                time_second_conflict = time.clock() - st
                for e in elements_to_check[:]:
                    if e not in new_confl:
                        elements_to_check.remove(e)
                elems_after = len(elements_to_check)

        # logging some statistics:
        msg += "  Computation of the first conflict took "
        msg += "%.2f seconds\n" % time_first_conflict
        msg += "  For the first conflict:\n"
        msg += checks_first_conflict
        if done_once:
            msg += "  Intersection with second conflict: %d " % elems_before
            msg += "--> %d diagnosis candidates.\n" % elems_after
            msg += "  Computation of the second conflict took "
            msg += "%.2f seconds\n" % time_second_conflict
        msg += "  %d diagnoses found\n" % len(self.__diagnoses)
        msg += "  Diagnoses computation took "
        msg += "%.2f seconds\n" % (time.clock() - starttime)
        msg += self.__conflict_finder.get_statistics()
        msg += self.__min_target.get_check_statistics()
        PLog.log(msg)



    def _compute_signlefault_only(self):
        """
        Computes single fault diagnoses in a performance optimized way.

        This method computes single fault diagnoses in a performance optimized
        way. Instead of computing one minimal conflict, 3 minimal conflicts
        are computed and intersected. This is done because computing a minimal
        conflict is often faster than doing one realizability check.
        Additionally, there is the change of ruling out lots of diagnosis
        candidates at once. However, experiments show that the intersection
        with the additional conflicts does not really improve the performance.
        This method is never called. It is left in the code for future
        experiments.
        """

        starttime = time.clock()
        _starttime = time.time()
        # computing the first conflict
        finder = self.__conflict_finder
        #self.__utils.disable_dyn_reordering()
        (conflicts, times) = finder.compute_some_conflicts()
        #self.__utils.enable_dyn_reordering()
        checks_first_conflicts = self.__min_target.get_check_statistics()
        time_first_conflicts = time.clock() - starttime

        inter12 = set(conflicts[0]) & set(conflicts[1])
        inter13 = set(conflicts[0]) & set(conflicts[2])
        inter123 = set(conflicts[0]) & set(conflicts[1]) & set(conflicts[2])
        msg = " Some statistics:\n"
        msg += "Time 1 %.2f\n" % times[0]
        msg += "Time 2 %.2f\n" % times[1]
        msg += "Time 3 %.2f\n" % times[2]
        msg += "Inter with 2: %d --> %d\n" %(len(conflicts[0]), len(inter12))
        msg += "Inter with 3: %d --> %d\n" %(len(conflicts[0]), len(inter13))
        msg += "Inter with both: %d --> %d\n" %(len(conflicts[0]), len(inter123))

        for elem in inter123:
            if self.__max_diagnoses and \
               len(self.__diagnoses) >= self.__max_diagnoses:
                msg += "  Aborted single fault diagnosis computation as the "
                msg += "desired number of %d diagnoses " % self.__max_diagnoses
                msg += "has already been obtained.\n"
                break
            if not finder.exists_conflict_not_containing([elem]):
                # if we remove the element, the spec is realizable
                # --> the element is a diagnosis:
                self.__diagnoses.append([elem])

        # logging some statistics:
        msg += "  Computation of the first conflicts took "
        msg += "%.2f seconds\n" % time_first_conflicts
        msg += "  For the first conflicts:\n"
        msg += checks_first_conflicts
        msg += "  %d diagnoses found\n" % len(self.__diagnoses)
        msg += "  Diagnoses computation took "
        msg += "%.2f seconds\n" % (time.clock() - starttime)
        msg += "  Diagnoses computation took "
        msg += "%d seconds\n" % (time.time() - _starttime)
        msg += self.__conflict_finder.get_statistics()
        msg += self.__min_target.get_check_statistics()
        PLog.log(msg)



    def _compute_children(self, current_node):
        """
        Computes all children of a hitting set tree node.

        This method computes all children of a hitting set tree node. The
        children are appended to the list of all nodes self.__all_nodes. New
        inner nodes are furthermore added to the list self.__nodes_to_process of
        nodes which still have to be analyzed for children in the future. If a
        child node turns out to represent a diagnosis, the conflict is stored in
        the list self.__diagnoses of diagnoses. The method returns True if
        everything went fine and False if the maximum number of diagnoses to
        compute has been reached, in which case the computation can be aborted.

        @param current_node: The node to compute all childs for.
        @type current_node: HSTreeNode
        @return: True if the breath-first search should continue and False if
                 the maximum number of diagnoses to compute has been reached
                 and the computation should be aborted.
        @rtype: bool
        """

        # check if we can abort:
        if self.__max_diagnoses and \
            len(self.__diagnoses) >= self.__max_diagnoses:
            return False

        # computing the conflicts:
        if current_node.conflict == None:
            cov = current_node.get_all_covered_conflict_elements()
            confl = self.__conflict_finder.compute_conflict_not_containing(cov)
            current_node.conflict = confl

        for conflict_element in current_node.conflict:

            # check if we can abort:
            if self.__max_diagnoses and \
               len(self.__diagnoses) >= self.__max_diagnoses:
                return False

            # creating a new tree node:
            new_node = HSTreeNode(current_node)
            current_node.children.append(new_node)
            new_node.name = "n%d" % len(self.__all_nodes)
            new_node.covered_conflict_element = conflict_element
            self.__all_nodes.append(new_node)

            # pruning:
            covered_elements = new_node.get_all_covered_conflict_elements()
            if self._can_prune(covered_elements):
                # if one of the pruning rules applies, we mark the new node as
                # LEAF_PRUNE node and do not add it to self.__nodes_to_process:
                new_node.node_type = HSTreeNode.LEAF_PRUNE
            else:
                # If no pruning rule applies:
                if self.__conflict_finder.exists_conflict_not_containing(
                   covered_elements):
                    # we have an inner node of the tree:
                    new_node.node_type = HSTreeNode.INNER
                    self.__nodes_to_process.append(new_node)
                    self.__already_covered.append(covered_elements)
                else:
                    # no such conflict exists, we have a diagnose:
                    new_node.node_type = HSTreeNode.LEAF_HS
                    self.__diagnoses.append(covered_elements)

        return True

    def _can_prune(self, elements):
        """
        Checks if the hitting set tree can be pruned at a certain node.

        This method checks if one of the pruning rules proposed in
        'R. Reiter: A Theory of Diagnosis from First Principles'
        applies. If a pruning rule applies, then the node can be closed, i.e.,
        its successors do not have to be analized. Pruning rule 3 is not
        implemented because the L{ConflictFinder} is assumed to return only
        minimal conflicts.

        @param elements: The set of conflict elements covered by the hitting
               set tree node.
        @type element: list<int>
        @return: True if a pruning rule applies and the node can be closed,
                 False otherwise.
        @rtype: bool
        """

        # Pruning rule 1:
        # If the conflict elements covered by the node are a superset of an
        # already computed diagnose, we can stop because the set of covered
        # elements can only get larger and we are only interested in minimal
        # diagnoses.
        for diagnose in self.__diagnoses:
            if set(diagnose) <= set(elements):
                return True

        # Pruning rule 2:
        # If the conflict elements covered by the node are equal to the conflict
        # elements covered by some other node, we can close the second node
        # because it would not give any new diagnosis.
        for covered in self.__already_covered:
            if set(covered) == set(elements):
                return True

        # Pruning rule 3 is not implemented because the ConflictFinder is
        # assumed to return only minimal conflicts.

        # No Pruning rule applies:
        return False

class ConflictFinder(object):
    """
    This class is able to compute minimal conflicts.

    This class is able to compute minimal conflicts. Abstractly speaking a
    minimal conflict is a minimal set of elements which fails the method
    'test' of the class L{MinTarget}. Such a minimal set is computed by an
    instance of a L{Minimizer}. In our case, a set represents a specification.
    A set fails the test iff this specification is unrealizable. So computing
    a minimal conflict means computing an unrealizable core.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, minimizer, min_target):
        """
        Constructor.

        @param minimizer: A class that implements a minimization algorithm. It
               is used for the computation of minimal conflicts.
        @type minimizer: L{Minimizer}
        @param min_target: Some implementation of the interface L{MinTarget}.
               It represents a specification and can be minimized by the
               minimizer.
        @type min_target: L{MinTarget}
        """

        #: A class that implements a minimization algorithm.
        #:
        #: It is used for the computation of minimal conflicts.
        #: @type: L{Minimizer}
        self.__minimizer = minimizer

        #: Some implementation of the interface L{MinTarget}.
        #:
        #: It represents a specification and can be minimized by the minimizer.
        #: @type: L{MinTarget}
        self.__min_target = min_target

        #: The set of all elements of the min_target which can be minimized.
        #: @type: list<int>
        self._all_elements = min_target.get_elements_to_minimize()


        #: The set of minimal conflicts obtained so far.
        #: @type: list<list<int>>
        self.__conflicts = []

        #: A counter counting all requests for conflicts.
        #: @type: int
        self.__request_count = 0

        #: A counter counting the cases where no conflict existed.
        #: @type: int
        self.__request_consistent_count = 0

        #: A counter for how often an already computed conflict could be reused.
        #: @type: int
        self.__conflict_reuse_count = 0

        # We do not want to produce log messages while minimizing:
        self.__min_target.set_log_file(None)


    def exists_conflict_not_containing(self, must_not_contain):
        """
        Checks if a conflict exists which does not contain certain elements.

        @param must_not_contain: The set of elements which must not be
               contained in the conflict.
        @type must_not_contain: list<int>
        @return: True if a conflict exists which does not contain the specified
                 elements, False otherwise.
        @rtype: bool
        """

        # The set to be minimized must not contain elements of must_not_contain:
        set_to_minimize = self._all_elements[:]
        for elem in must_not_contain:
            if elem in set_to_minimize:
                set_to_minimize.remove(elem)

        # Searching for an already computed conflict that matches the request:
        conflict = self._search_computed_conflicts(must_not_contain)
        if conflict:
            return True

        # Checking if a conflict exists which does not contain elements of
        # must_not_contain:
        if self.__min_target.test_approx_first(set_to_minimize,0) == True:
            self.__request_consistent_count += 1
            return False
        return True

    def compute_conflict_not_containing(self, must_not_contain, rand = False,
                                        lookup = True):
        """
        Computes a conflict not containing a certain set of elements.

        This method computes a conflict not containing a certain set of
        elements. It implicitly assumes that such a conflict exists (i.e.,
        that the existance has been checked by calling
        exists_conflict_not_containing before).

        @param must_not_contain: The set of elements which must not be
               contained in the resulting conflict.
        @type must_not_contain: list<int>
        @param rand: True if the list of elements should be randomized before
               minimization, False otherwise.
        @type rand: bool
        @param lookup: True if already computed conflicts should be reused,
               False if a new conflict should be computed.
        @type lookup: bool
        @return: A minimal conflict not containing the specified elements or
                 None if no such conflict could be found.
        @rtype: list<int>
        """
        self.__request_count += 1

        # The set to be minimized must not contain elements of must_not_contain:
        set_to_minimize = self._all_elements[:]
        for elem in must_not_contain:
            if elem in set_to_minimize:
                set_to_minimize.remove(elem)

        if lookup:
            # Searching for an already computed conflict that matches the
            # request:
            conflict = self._search_computed_conflicts(must_not_contain)
            if conflict:
                self.__conflict_reuse_count += 1
                return conflict

        # Otherwise we have to compute a minimal conflict:
        if rand:
            shuffle(set_to_minimize)
        conflict =  self.__minimizer.minimize(set_to_minimize)
        self.__conflicts.append(conflict)
        return conflict


    def compute_some_conflicts(self):
        """
        Computes three conflicts and returns them.

        This method computes three conflict and returns them. It is actually
        never called. It is left in the code for future experiments.

        @return: A tuple consisting of two elements. The first element is
                 a list of conflicts. The second element is a list of floats,
                 each representing the time for the computation of the
                 corresponding conflict.
        @rtype: (list<list<int>>, list<float>)
        """

        self.__request_count += 1

        # The set to be minimized must not contain elements of
        # must_not_contain:
        set_to_minimize = self._all_elements[:]

        st1 = time.clock()
        conflict1 =  self.__minimizer.minimize(set_to_minimize)
        time1 = time.clock() - st1
        self.__conflicts.append(conflict1)

        set_to_minimize.reverse()
        st2 = time.clock()
        conflict2 =  self.__minimizer.minimize(set_to_minimize)
        time2 = time.clock() - st2
        self.__conflicts.append(conflict2)

        chunks = self.split_seq(set_to_minimize, 4)
        shuffled = chunks[1][:]
        shuffled.extend(chunks[3])
        shuffled.extend(chunks[0])
        shuffled.extend(chunks[2])
        st3 = time.clock()
        conflict3 =  self.__minimizer.minimize(shuffled)
        time3 = time.clock() - st3
        self.__conflicts.append(conflict3)

        return ([conflict1,conflict2,conflict3],[time1, time2, time3])


    def split_seq(self, seq, num_pieces):
        """
        Splits a list into a defined number of parts.

        @param seq: The list to split.
        @type seq: list<some type>
        @param num_pieces: The number of pieces to split the list into.
        @type num_pieces: int
        @return: The parts of the list into which the list is split.
        @return: list<list<some type>>
        """

        list_parts = []
        start = 0
        for i in xrange(num_pieces):
            stop = start + len(seq[i::num_pieces])
            list_parts.append(seq[start:stop])
            start = stop
        return list_parts


    def get_conflicts(self):
        """
        Returns the computed minimal conflicts in human readable form.

        This method returns the computed minimal conflicts in human readable
        form, i.e., all guarantees or outputs are referred to with their name
        rather than their index. Each minimal conflict is an unrealizable core.

        @return: The computed minimal conflicts in human readable form.
        @rtype: list<list<string>>
        """

        res = []
        for conflict in self.__conflicts:
            res.append(self.__min_target.get_string_rep(conflict))
        return res

    def get_raw_conflicts(self):
        """
        Returns the computed minimal conflicts as sets of integers.

        This method returns the computed minimal conflicts as sets of integers.
        Each minimal conflict is an unrealizable core.

        @return: The computed minimal conflicts as sets of integers.
        @rtype: list<list<int>>
        """
        return self.__conflicts

    def use_conflict(self, conflict_index):
        """
        Informs the L{MinTarget} about the final solution of a minimization.

        This method informs the L{MinTarget} about the final solution of a
        particular minimization, i.e., about a particular minimal conflict.
        Each minimal conflict is an unrealizable core. The L{MinTarget} can
        store this final solution if desired so that it can be used for all
        further steps.

        @param conflict_index: The index of the conflict to be used and stored
               as unrealizable core.
        @type conflict_index: int
        """

        self.__min_target.set_final_solution(self.__conflicts[conflict_index])

    def get_statistics(self):
        """
        Returns some statistics reguarding the computed conflicts.

        @return: Some statistics reguarding the computed conflicts.
        @rtype: string
        """

        msg = "  %d" % self.__request_consistent_count
        msg += " times, no conflict existed\n"
        msg += "  %d" % self.__request_count
        msg += " conflicts had to be computed\n"
        msg += "  %d" % self.__conflict_reuse_count
        msg += " conflicts could be reused\n"
        msg += "  %d" % len(self.__conflicts)
        msg += " conflicts really had to be computed\n"
        return msg

    def _search_computed_conflicts(self, must_not_contain):
        """
        Searches the already computed conflicts for one that matches.

        This method searches the already computed conflicts for one that matches
        the request. If a conflict could be found which does not contain any
        element of must_not_contain, it is returned. Otherwise None is returned.

        @param must_not_contain: The set of elements which must not be
               contained in the conflict.
        @type must_not_contain: list<int>
        @return: A minimal conflict not containing the specified elements or
                 None if no such conflict could be found in the list of already
                 computed conflicts.
        @rtype: list<int>
        """

        for conflict in self.__conflicts:
            if (set(conflict) & set(must_not_contain)) == set([]):
                return conflict
        return None

class HSTreeNode(object):
    """
    This class represents a node in the HSTree.

    This class represents a node in the hitting set tree. It stores all
    information corresponding to a node and is able to transform itself into
    DOT format.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    #: A constant for the type of an inner node of the tree.
    #: @type: string
    INNER = "INNER NODE"

    #: A constant for the type of a leaf due to pruning.
    #: @type: string
    LEAF_PRUNE = "LEAF PRUNE"

    #: A constant for the type of a leaf representing a minimal hitting set.
    #: @type: string
    LEAF_HS = "LEAF HS"

    def __init__(self, node_parent):
        """
        Constructor.

        @param node_parent: The parent of the node or None if this is going to
               be the root node of the tree.
        @type node_parent: L{HSTreeNode}
        """

        #: The name of the node.
        #: @type: string
        self.name = None

        #: The parent of the node or None if this is the root node.
        #: @type: L{HSTreeNode}
        self.parent = node_parent

        #: All children of the node.
        #: @type: list<L{HSTreeNode}>
        self.children = []

        #: The conflict element covered by this node.
        #: @type: int
        self.covered_conflict_element = None

        #: The conflict with which this node is labelled.
        #: @type: list<int>
        self.conflict = None

        #: The type of the node.
        #:
        #: Either HSTreeNode.INNER, HSTreeNode.LEAF_PRUNE, or
        #: HSTreeNode.LEAF_HS.
        #: @type: string
        self.node_type = None

    def get_all_covered_conflict_elements(self):
        """
        Returns all conflict elements covered by this node.

        This method returns all conflict elements covered by this node. This is
        the conflict element covered by exactly this node together with the
        conflict elements covered by all parants. It corresponds to H(n) in the
        paper.

        @return All conflict elements covered by this node.
        @rtype: list<int>
        """

        if self.parent:
            res = self.parent.get_all_covered_conflict_elements()
            res.append(self.covered_conflict_element)
            return res

        # The root node does not cover anything:
        return []

    def get_depth(self):
        """
        Returns the depth of the node in the tree.

        @return the depth of the node in the tree.
        @rtype: int
        """
        if self.parent:
            return self.parent.get_depth() + 1
        return 0


    def to_dot(self):
        """
        Returns a DOT representation of the tree node.

        @return: A DOT representation of the tree node.
        @rtype: string
        """
        dot_string = "  " + self.name
        dot_string += "[label = \"{" + self.name + " | "
        dot_string += self.node_type + "  | "
        dot_string += str(self.conflict) + "}\"];\n"
        if self.parent:
            dot_string += "  " + self.parent.name + " -> "+ self.name
            dot_string += "[label = \"" + str(self.covered_conflict_element)
            dot_string += "\"];\n"
        return dot_string
