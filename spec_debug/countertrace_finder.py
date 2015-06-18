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
Contains a class to heuristically search for a countertrace.
"""

from bddwrap import BDD
from writer import Writer

class CountertraceFinder(object):
    """
    Heuristically searches for a countertrace.

    This module is able to heuristically search for a countertrace, i.e.,
    for a FIXED sequence of input values, so that the system is not able
    to fulfill the specification no matter how it behaves. Of course
    such a fixed sequence of inputs is a much simpler explanation for
    unrealizability than a sequence of inputs which is dependent on
    previous outputs.

    Computing a countertrace is expensive. We could existentially
    quantify all outputs in the automaton representing the specification,
    complement the automaton and check for emptyness. However,
    complementing a nondeterministic automaton causes an exponential
    blow up of the state space. Thus we define a heuristic. If no
    countertrace could be found with this heuristic, this does not mean,
    that no such trace exists. If a countertrace could be found, it is
    written into the file 'spec_debug_results/countertrace.txt'.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """
    def __init__(self, utils):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: A utility class that allows us to print the countertrace.
        #: @type: L{Writer}
        self.__writer = Writer(utils)

    def compute_countertrace(self, counterstrategy, abort = 100):
        """
        Heuristically searches for a countertrace.

        This method is able to heuristically search for a countertrace, i.e.,
        for a FIXED sequence of input values, so that the system is not able
        to fulfill the specification no matter how it behaves. Of course
        such a fixed sequence of inputs is a much simpler explanation for
        unrealizability than a sequence of inputs which is dependent on
        previous outputs.

        The heuristic works in the following way:
        For every time step, we compute a set of states which might be
        visited in exactly this time step:
         - set0 = all states which might be visited in step 0 (initial states)
         - set1 = all states which might be visited in step 1, so
           all possible successors of set0
         - and so on
        For every set we now try to find one next input which is winning for
        the environment from all states of the set (which is conforming to
        the counterstrategy from all states of the set). If no next input
        could be found for at least one of the sets, our heuristic gives up.

        @param counterstrategy: the (interactive, system dependent)
               counterstrategy.
        @type counterstrategy: L{BDD}
        @param abort: The number of iterations after which the heuristic aborts
               without success. The default value is 100.
        @type abort: 100
        @return: A countertrace.
        @rtype: L{InfiniteTraceOfBdds}
        """

        utils = self.__utils

        if utils.init.isZero() or utils.trans.isZero():
            # we won't find a countertrace in these cases:
            return None

        itcount = 0
        list_of_sets = []
        countertrace = []
        repeat_index = None
        irrelevant_output_cube = BDD.ONE(self.__utils.dd_mgr)
        for out in utils.output_vars:
            irrelevant_output_cube *= out.ps * out.ns
        for out in utils.relevant_out_vars:
            irrelevant_output_cube = irrelevant_output_cube.exists(out.ps)
            irrelevant_output_cube = irrelevant_output_cube.exists(out.ns)

        current_states = utils.all_present_vars_cube

        # we start in the initial state:
        current_set_of_states = utils.init_ix_jx

        countertrace.append(utils.keep_only_present_inputs(utils.init))

        # while we did not already examine a superset of the current set of
        # states:
        while not self.get_index_of_superset_in_list(list_of_sets, \
                                                     current_set_of_states):
            list_of_sets.append(current_set_of_states)
            #print "------------   iteration %d  ------------------" % itcount
            itcount += 1
            if abort != None and abort > 0 and itcount >= abort:
                return None

            # computing all next inputs conforming to the counterstrategy:
            state_plus_input_ix_jx = current_set_of_states * counterstrategy
            state_plus_input_ix_jx = \
                      state_plus_input_ix_jx.exists(irrelevant_output_cube)
            state_plus_input = \
                      utils.remove_next_ix_jx_outputs(state_plus_input_ix_jx)

            # now we compute all next inputs, which are OK (winning for the
            # environment) for all states of current_set_of_states:
            state_occurs = utils.keep_only_present(state_plus_input)
            system_indep_next_inputs = \
                   ((~state_occurs) + state_plus_input).forall(current_states)

            if system_indep_next_inputs.isZero():
                # if we could not find one, we give up
                # TODO: maybe try something else in a previous step to
                # avoid this certain current_set_of_states.
                return None

            # we choose one of these inputs:
            concrete_next_input = \
                        utils.choose_all_next_inputs(system_indep_next_inputs)

            trace_elem = utils.swap_present_next(concrete_next_input)
            countertrace.append(utils.keep_only_present_inputs(trace_elem))

            # the new current_set_of_states is the set of next states (if
            # concrete_next_input is used as input):
            state_plus_input_ix_jx *= concrete_next_input
            next_states = state_plus_input_ix_jx * utils.sys_trans
            next_states = utils.swap_present_next(next_states)
            current_set_of_states = utils.keep_only_present(next_states)


        # If we are here, we found an input for every time step.
        repeat_index = self.get_index_of_superset_in_list(list_of_sets, \
                                                     current_set_of_states) + 1
        trace = InfiniteTraceOfBdds(utils, countertrace, repeat_index)

        return trace
        
    def print_trace(self, countertrace):
        """
        Prints a countertrace into the file
        ./spec_debug_results/countertrace.txt.

        @param countertrace: A sequence of inputs so that the system is forced
               to violate its specification.
        @type countertrace: L{InfiniteTraceOfBdds}
        """

        # write the inputs according to the countertrace:
        for input_bdd in countertrace.get_trace():
            for var in self.__utils.input_vars:
                symb = self.__utils.get_val_as_string(input_bdd, var, False)
                self.__writer.set_chosen_input(var.name, symb)
            self.__writer.start_next_time_step()

        # finally we define where the trace repeats:
        self.__writer.set_repeat_indices(countertrace.repeat_index, \
                                     countertrace.length_stem_plus_loop - 1)

        # and write the file:
        self.__writer.write_to_file("./spec_debug_results/countertrace.txt")
        self.__writer.clear()

    def is_graph_system_independent(self, graph_nodes):
        """
        Checks if the inputs in a graph are system independent.

        This method checks if the inputs in the graph computed by the class
        L{PathFinder} are system independent. If this is the case, a
        countertrace can be read directly from this graph. If the graph was
        generated from a countertrace, the inputs in this graph will always
        be system independent (i.e., independent of the moves of the system).

        This method is only used to check if the methods compute_countertrace
        and make_strategy_system_independent work correctly.

        @param graph_nodes: A set of graph nodes.
        @type graph_nodes: list<L{GraphNode}>
        @return: True if the graph is system independent, False otherwise
        @rtype: bool
        """

        # The first current state is the initial state:
        current_nodes = [graph_nodes[0]]
        current_nodes_bdd = graph_nodes[0].bdd
        list_of_sets = []
        while list_of_sets.count(current_nodes_bdd) == 0:
            list_of_sets.append(current_nodes_bdd)

            # check if all inputs are equal:
            input_intersection = BDD.ONE(self.__utils.dd_mgr)
            for node in current_nodes:
                inputs = self.__utils.keep_only_present_inputs(node.bdd)
                input_intersection *= inputs
            
            if input_intersection.isZero():
                print "Graph is NOT system independent !\n"
                return False

            # compute list of successor states:
            next_nodes = []
            for node in current_nodes:
                next_nodes.extend(node.successors)
            # we remove multiple elements:
            current_nodes = list(set(next_nodes))

            # compute a bdd that contains all nodes:
            current_nodes_bdd = BDD.ZERO(self.__utils.dd_mgr)
            for node in current_nodes:
                current_nodes_bdd += node.bdd

        # If we are here, the graph is system independent, i.e., the inputs
        # used in the graph are independent of the moves of the system.
        print "graph IS system independent!!!"
        return True


    def make_strategy_system_independent(self, counterstrategy):
        """
        Heuristically tries to make a counterstrategy system independent.

        A counterstrategy is system independent if choices on
        next inputs do not depend on previous choices of outputs in all time
        steps. Hence, a system independent counterstrategy can be used to
        compute a countertrace, i.e. a FIXED sequence of inputs, so that the
        system is always forced to violate its specification no matter how it
        behaves. Basically a system independent counterstrategy is a
        countertrace in the shape of a counterstrategy (in the shape of a
        relation rather than a list of inputs).

        This method is never used, it is just experimental. Use the method
        compute_countertrace instead. compute_countertrace will find
        countertraces in more cases, since there is no restriction that the
        result has to be in the shape of a counterstrategy. So in the method
        compute_countertrace, different behaviours from the same state
        (inputs,outputs,ix,jx content) are possible dependent on the step
        count while this is not the case for make_strategy_system_independent.

        The heuristic works in the following way:
        For every time step, we compute a set of states which might be
        visited in exactly this time step:
         - set0 = all states which might be visited in step 0 (initial states)
         - set1 = all states which might be visited in step 1, so
           all possible successors of set0
         - and so on
        For every set we now try to find one next input which is winning for
        the environment from all states of the set (which is conforming to
        the counterstrategy from all states of the set). If such an input is
        found, the counterstrategy must take this next input from all states
        of the set. In the counterstrategy we disallow all other inputs from
        these states. When the counterstrategy changes, we restart the
        computation (we perform another iteration) as the change might affect
        previous time steps as well. If no next input could be found for at
        least one of the sets, our heuristic gives up.

        @param counterstrategy: The (interactive, system dependent)
               counterstrategy.
        @type counterstrategy: L{BDD}
        @return: A system independent counterstrategy or None if no system
                independent counterstrateg could be found with the heuristic.
        @rtype: L{BDD}
        """

        # The initial system independent counterstrategy (=SIC) is the
        # interactive counterstrategy:
        sic = counterstrategy.copy()

        continue_iterating = 1
        while continue_iterating:
            (sic, continue_iterating) = self._make_sic_iteration(sic)

        return sic


    def _make_sic_iteration(self, counterstrategy):
        """
        Implements one iteration to make a counterstrategy system independent.

        It works in the following way:
        For every time step, we compute a set of states which might be
        visited in exactly this time step:
         - set0 = all states which might be visited in step 0 (initial states)
         - set1 = all states which might be visited in step 1, so
           all possible successors of set0
         - and so on
        For every set we now try to find one next input which is winning for
        the environment from all states of the set (which is conforming to
        the counterstrategy from all states of the set). If such an input is
        found, the counterstrategy must take this next input from all states
        of the set. In the counterstrategy we disallow all other inputs from
        these states. When the counterstrategy changes, we abort the iteration
        and request another one (with continue_iterating=0).

        @param counterstrategy: A counterstrategy which is not yet fully
               system independent.
        @type counterstrategy: L {BDD}
        @return: A tuple (sic, continue_iterating) where:
                 - sic is the counterstrategy which is a bit more system
                   independent than the passed one.
                 - continue_iterating is True, if another iteration has to be
                   performed to make the sic fully system independent.
        @rtype: (L{BDD}, bool)
        """
        sic = counterstrategy.copy()

        itcount = 0
        list_of_sets = []
        list_of_chosen_next_inputs = []
        current_states = self.__utils.all_present_vars_cube

        # we start in the initial state:
        current_set_of_states = self.__utils.init_ix_jx

        # while we did not already examine the current set of states:
        while list_of_sets.count(current_set_of_states) == 0:
            list_of_sets.append(current_set_of_states)
            print "------------   iteration %d  ------------------" % itcount
            itcount += 1

            # computing all next inputs conforming to the counterstrategy:
            state_plus_input_ix_jx = current_set_of_states * counterstrategy
            state_plus_input = \
                self.__utils.remove_next_ix_jx_outputs(state_plus_input_ix_jx)

            # now we compute all next inputs, which are OK (winning for the
            # environment) for all states of current_set_of_states:
            state_occurs = self.__utils.keep_only_present(state_plus_input)
            system_indep_next_inputs = \
                   ((~state_occurs) + state_plus_input).forall(current_states)

            if system_indep_next_inputs.isZero():
                # if we could not find one, we give up
                # TODO: maybe try something else in a previous step to avoid
                # this certain current_set_of_states.
                print "Failed!"
                return (None, False)


            # Whenever we are in a state of current_set_of_states, the next
            # input must be a system_indep_next_inputs:
            forbidden_transitions = current_set_of_states * \
                                    (~system_indep_next_inputs)
            new_sic = sic * (~forbidden_transitions)
            if new_sic != sic:
                # whenever the counterstrategy changed, we start again, because
                # the change might effect one of the previous sets of states as
                # well. Hence it might be the case, that not all states of
                # current_set_of_states are reachable any more.
                return (new_sic, True)


            # now we choose a concrete next input and compute all next states
            # again in current_set_of_states:
            concrete_next_input = \
                  self.__utils.choose_all_next_inputs(system_indep_next_inputs)
            list_of_chosen_next_inputs.append(concrete_next_input)
            state_plus_input_ix_jx *= concrete_next_input
            next_states = state_plus_input_ix_jx * self.__utils.sys_trans
            next_states = self.__utils.swap_present_next(next_states)
            current_set_of_states = self.__utils.keep_only_present(next_states)

        # We now know, that applying the counterstrategy in sic together
        # with the heuristic for choosing inputs as implementd in
        # choose_all_next_inputs() leads to complete system independence. Thus
        # we finally add the heuristic for choosing inputs as implementd in
        # choose_all_next_inputs() to the counterstrategy to really have a
        # system independent counterstrategy.
        for i in range(0, len(list_of_chosen_next_inputs)):
            set_of_states = list_of_sets[i]
            next_input = list_of_chosen_next_inputs[i]
            forbidden_transitions = set_of_states * (~next_input)
            sic *= ~forbidden_transitions
        return (sic, False)

    def get_index_of_superset_in_list(self, list, bdd):
        """
        Searches for a superset in a list.

        This method searches through a list of bdds to find a superset of
        a specific bdd and returns the index of the superset in the
        list or None if the list does not contain a superset of the bdd.

        @param list: A list of bdds.
        @type list: list<L{BDD}>
        @param bdd: A bdd where we want to find a superset for.
        @type bdd: L{BDD}
        @return: the index of a superset of in the list or None
        @rtype: int
        """
        for i in range(0,len(list)):
            if bdd <= list[i]:
                return i
        return None


class InfiniteTraceOfBdds(object):
    """
    Contains an infinite trace of Bdds.

    This class is a helper that represents a trace of Bdds. It also
    offers some methods to handle such traces conveniently.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """
    def __init__(self, utils, trace, repeat_index):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        @param trace: The trace of bdds itself.
        @type trace: list<L{BDD}>
        @param repeat_index: The index in the list where the trace repeats
               ([0..repeat_index-1] = finite stem,
               [repeat_index .. endOfList] = loop)
        @type repeat_index: int
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: The trace of bdds itself.
        #: @type: list<L{BDD}>
        self.__trace = trace

        #: The index in the list self.__trace where the trace repeats.
        #:
        #:  - [0..repeat_index-1] = finite stem
        #:  - [repeat_index .. endOfList] = loop)
        #: @type: int
        self.__repeat_index = repeat_index

    def get_finite_stem_length(self):
        """
        Returns the length of the finite stem of the trace.

        @return: the length of the finite stem of the trace.
        @rtype: int
        """
        return (self.__repeat_index)

    #: The length of the finite stem of the trace.
    #: @type: int
    stem_length = property(get_finite_stem_length)

    def get_loop_length(self):
        """
        Returns the length of the loop of the trace.

        @return: the length of the loop of the trace.
        @rtype: int
        """
        return (len(self.__trace) - self.__repeat_index)

    #: The length of the loop of the trace.
    #: @type: int
    loop_length = property(get_loop_length)

    def get_length_stem_plus_loop(self):
        """
        Returns the length of the stem plus the length of the loop.

        @return: the length of the stem plus the length of the loop.
        @rtype: int
        """
        return len(self.__trace)

    #: The length of the stem plus the length of the loop.
    #: @type: int
    length_stem_plus_loop = property(get_length_stem_plus_loop)

    def get_trace(self):
        """
        Returns the trace of bdds itself.

        @return: the trace of bdds.
        @rtype: list<L{BDD}>
        """
        return self.__trace

    #: The trace of bdds itself.
    #: @type: list<L{BDD}>
    trace = property(get_trace)

    def get_repeat_index(self):
        """
        Returns the index in the list self.__trace where the trace repeats.

         - [0..repeat_index-1] = finite stem
         - [repeat_index .. endOfList] = loop)
        @return: the index in the list self.__trace where the trace repeats.
        @rtype: int
        """
        return self.__repeat_index

    #: The index in the list self.__trace where the trace repeats.
    #: @type: int
    repeat_index = property(get_repeat_index)

    def get_bdd_to_step(self, step_count):
        """
        Returns the bdd given a certain step count.

        @param step_count: The current value of the step counter.
        @type step_count: int
        @return: the bdd given a certain step count.
        @rtype: L{BDD}
        """
        index = step_count
        if step_count >= len(self.__trace):
            # the step_count minus length of finite stem ...
            index = step_count - self.get_finite_stem_length()
            # ... modulo the length of the infinite loop ...
            index = index % self.get_loop_length()
            # ... plus the length of the finite stem
            index += self.get_finite_stem_length()
            # ... gives the index in the list.
        return self.__trace[index].copy()

    def get_signal_to_step(self, step, var, current_next):
        """
        Returns the value of a certain variable at a certain step count.

        @param var: The variable to check.
        @type var: L{Variable}
        @param step_count: The current value of the step counter.
        @type step_count: int
        @param current_next: False to get the current value and True to get the
               next value.
        @type current_next: bool
        @return: the value of a certain variable at a certain step count.
        @rtype: int
        """
        bdd = self.get_bdd_to_step(step)
        (can_be_1, can_be_0) = self.__utils.get_val(bdd, var, current_next)
        return int(can_be_1)
