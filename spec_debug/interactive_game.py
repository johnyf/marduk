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
Contains a class that implements an interactive debugging game.
"""

import sys
from bddwrap import BDD
from writer import Writer

class InteractiveGame(object):
    """
    Implements an interactive debugging game.

    This class implements an interactive game between the computer in
    the role of the environment and the user in the role of the system.
    In every time step, the environment first gives next inputs to the
    system. Then the user is asked to choose the next values of the
    output variables. The play is won for the user if she manages to
    fulfill all the fairness conditions of the system infinitely often
    or if the environment does not fulfill all its fairness constraints.
    The play is won for the environment if the user looses, so if the
    environment manages to find inputs to the system, so that the user is
    not able to fulfill all fairness conditions infinitely often while
    the environment is able to do so.

    If the specification is not realizable a strategy to determine the
    next inputs to the system so that the system loses every play
    exists. This strategy is called a 'counterstrategy'. In the game
    implemented in this class, this counterstrategy is used to find the
    inputs for the system. To make it easier for the user to find outputs
    of the system which are feasible according to the transition relation of
    the system, the possible values for all output variables are calculated.
    The computer will also print the index of the fairness constraint of the
    system it tries to evade. Thus the user can concentrate on fulfilling this
    constraint only. A summary of all input variables and all output
    variables in all steps is finally written into the file
    'spec_debug_results/log.txt'.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """
    def __init__(self, utils, counterstrategy, z_array, countertrace):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        @param counterstrategy: A counterstrategy, i.e., a strategy for the
               environment to find inputs so that the system is forced to
               violate the specification.
        @type counterstrategy: L{BDD}
        @param z_array: z_array[a] contains the intermediate results of the
               fixpoint computation in the variable Z of the computation of
               the winning region for the environment. 'a' counts the
               iterations of the fixpoint computation in Z. It is used to
               figure out how often the value of jx might still change in the
               future of the play. (If the play is in z_array[a], jx might
               change at most a-1 times.)
        @type z_array: list<L{BDD}>
        @param countertrace: A sequence of inputs so that the system is forced
               to violate its specification.
        @type countertrace: L{InfiniteTraceOfBdds}
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: A winning strategy for the environment.
        #: @type: L{BDD}
        self.__counterstrategy = counterstrategy

        #: Intermediate results of the fixpoint computation in the variable Z.
        #: @type: list<L{BDD}>
        self.__z_array = z_array

        #: A sequence of inputs so that the system is forced to violate its
        #: specification.
        #: @type: L{InfiniteTraceOfBdds}
        self.__countertrace = countertrace

        #: A utility class that allows us to print the summary of the play.
        #: @type: L{Writer}
        self.__writer = Writer(utils)

    def interact(self):
        """
        Implements an interactive debugging game.

        This method implements an interactive game between the computer in
        the role of the environment and the user in the role of the system.
        In every time step, the environment first gives next inputs to the
        system. Then the user is asked to choose the next values of the
        output variables. The play is won for the user if she manages to
        fulfill all the fairness conditions of the system infinitely often
        or if the environment does not fulfill all its fairness constraints.
        The play is won for the environment if the user looses, so if the
        environment manages to find inputs to the system, so that the user is
        not able to fulfill all fairness conditions infinitely often while
        the environment is able to do so. The counterstrategy is used to find
        the inputs for the system.

        To make it easier for the user to find outputs of the system which
        are feasible according to the transition relation of the system, the
        possible values for all output variables are calculated. The computer
        will also print the index of the fairness constraint of the system
        it tries to evade. Thus the user can concentrate on fulfilling this
        constraint only. A summary of all input variables and all output
        variables in all steps is finally written into the file
        'spec_debug_results/log.txt'.
        """

        # The first current state is the initial state:
        current_state = self.__utils.init_ix_jx

        step_count = 0
        while True:

            # We now print the current state:
            # (The method _print_current_state also logs the current state to
            # the file 'spec_debug_results/log.txt'.)
            self._print_current_state(current_state)
            #current_state.print_minterm()

            # a concrete next input is chosen either according to the
            # counterstrategy or according to the countertrace:
            next_input = self.__utils.get_next_inputs(current_state, \
                                             step_count, \
                                             self.__counterstrategy, \
                                             self.__countertrace)

            # print the next inputs:
            self._print_next_inputs(next_input)

            # Choose the next jx variables (rho2 may allow more than one):
            for jx_var in self.__utils.jx_variables:
                (val, next_input) = self.__utils.choose_val( \
                                        next_input, jx_var, True)

            # computing all possible next outputs:
            possible_next_outputs = next_input * self.__utils.sys_trans

            # we read the next output variables (entered by the user):
            (outvar_bdd, quit) = self._read_out_vars(possible_next_outputs)
            if quit:
                return
            next_state = possible_next_outputs * outvar_bdd

            # and assign the next state to current_state:
            next_state = self.__utils.swap_present_next(next_state)
            current_state = self.__utils.keep_only_present(next_state)
            step_count += 1

    def _print_current_state(self, current_state):
        """
        Prints the current state.

        This method prints the current state in the interactive game between
        the environment and the system to STDOUT. In addition to that, the
        state is written to the log file 'spec_debug_results/log.txt' with
        the help of the L{Writer}.

        @param current_state: The state to print.
        @type current_state: L{BDD}
        """

        print "current state:"

        # print the input variables:
        for in_var in self.__utils.input_vars:
            symb = self.__utils.get_val_as_string(current_state, in_var, False)
            print "current " + in_var.name + " is: " + symb
            self.__writer.set_chosen_input(in_var.name, symb)

        # print the output variables:
        for out_var in self.__utils.relevant_out_vars:
            symb = self.__utils.get_val_as_string(current_state, out_var, False)
            print "current " + out_var.name + " is: " + symb
            self.__writer.set_chosen_output(out_var.name, symb);

        # print the ix-variables:
        ix_value = self.__utils.get_decimal_ix_val(current_state, False)
        if ix_value != None:
            print "The environment tries to fulfill fairness condition nr",
            print str(ix_value) + " next";
            self.__writer.set_chosen_aux("ix", str(ix_value))
        else:
            print "The environment has not decided yet which fairness",
            print "condition it will try to reach next"
            self.__writer.set_chosen_aux("ix","?")

        # print the jx-variables:
        nr_changes = self.__utils.how_often_may_jx_change(current_state, \
                                                          self.__z_array)
        self.__writer.set_chosen_aux("jx changes", str(nr_changes))
        jx_value = self.__utils.get_decimal_jx_val(current_state, False);
        if jx_value != None:
            print "I try to keep the system from fulfilling fairness",
            print "condition nr: " + str(jx_value)
            print "I reserve the right to change my opinion on that at most",
            print str(nr_changes) + " times from now"
            self.__writer.set_chosen_aux("jx", str(jx_value))
        else:
            print "I have not decided yet which fairness condition of the",
            print "system I will try to evade";
            self.__writer.set_chosen_aux("jx","?")

        self.__writer.start_next_time_step()


    def _print_next_inputs(self, next_inputs):
        """
        Prints all next inputs in a bdd.

        @param next_inputs: A bdd containing the next inputs.
        @type next_inputs: L{BDD}
        """

        for in_var in self.__utils.input_vars:
            symb = self.__utils.get_val_as_string(next_inputs, in_var, True)
            print "next " + in_var.name + " is: " + symb

    def _read_out_vars(self, possible_outputs):
        """
        Reads all next output values from STDIN.

        This method asks the user to enter the next values of the output
        variables of the system. It also resolves all restrictions on the
        variables (due to the transition relation of the system and previously
        entered variables) and displays possible values for the variable
        in brackets:
         - enter next hgrant0 (1): means only 1 is allowed for the next hgrant0
         - enter next hgrant0 (0): means only 0 is allowed for the next hgrant0
         - enter next hgrant0 (0,1): means that you can pick whatever you want

        The user is only allowed to enter '0', '1' or 'Q' if she wants to
        quit the game.

        @param possible_outputs: A bdd with all possible next outputs.
        @type possible_outputs: L{BDD}
        @return: A tuple (outvar_bdd, quit) where:
                  - outvar_bdd is a bdd with all next output variables set to
                    the values entered by the user
                  - quit is True if the user wants to quit and False otherwise.
        @rtype: (L{BDD}, bool)
        """

        # While the user enters variable values that are not allowed by
        # the transition relation of the system (if valid values are entered,
        # we jump out of the loop with a return):
        while True:
            all_outvars_bdd = BDD.ONE(self.__utils.dd_mgr)
            for out_var in self.__utils.relevant_out_vars:
                (out_bdd, quit) = self._read_single_out_var(out_var, \
                                           all_outvars_bdd * possible_outputs)
                if quit:
                    return (None, True)
                all_outvars_bdd *= out_bdd

            # check if the entered values are possible according to the
            # transition relation of the system (which is already part of
            # $possible_outputs)

            if (possible_outputs * all_outvars_bdd).isNotZero():
                return (all_outvars_bdd, False)
            print "this is not possible according to the transition relation"
            print "try again"
   

    def _read_single_out_var(self, out_var, possible_next_outputs):
        """
        Reads one single next output value from STDIN.

        This method asks the user to enter the next value of one single output
        variables of the system. It also resolves all restrictions on the
        variable (due to the transition relation of the system and previously
        entered variables) and displays possible values for the variable
        in brackets:
         - enter next hgrant0 (1): means only 1 is allowed for the next hgrant0
         - enter next hgrant0 (0): means only 0 is allowed for the next hgrant0
         - enter next hgrant0 (0,1): means that you can pick whatever you want

        The user is only allowed to enter '0', '1' or 'Q' if she wants to
        quit the game.

        @param out_var: The output variable to choose.
        @type out_var: L{Variable}
        @param possible_next_outputs: A bdd with all possible next outputs.
        @type possible_next_outputs: L{BDD}
        @return: A tuple (outvar_bdd, quit) where:
                  - outvar_bdd is a bdd with all next output variables set to
                    the values entered by the user
                  - quit is True if the user wants to quit and False otherwise.
        @rtype: (L{BDD}, int)
        """

        # while the user enteres invalid values (otherwise we jump out of
        # the loop with the return):
        while True:
            print "enter next " + out_var.name,
            self._print_possible_values_for(out_var, possible_next_outputs)
            input_line = sys.stdin.readline()

            if input_line == "Q\n" or input_line == "q\n":
                print "quit by user";
                self.__writer.write_to_file("./spec_debug_results/log.txt")
                self.__writer.clear()
                return (None, True)
            if input_line == "1\n":
                return (out_var.ns, False)
            elif input_line == "0\n":
                return (~out_var.ns, False)
            print "enter '1' or '0' or 'Q' to quit"

    def _print_possible_values_for(self, out_var, restrictions):
        """
        Prints all values which are possible for a certain output.

        This method prints all possible values for a certain output variable
        to STDOUT and also writes the values to a file
        'spec_debug_results/log.txt'.
        Writing to the file is done with the L{Writer} which formats
        the output in a nice way.

        @param out_var: The variable to print the possible values for.
        @type out_var: L{Variable}
        @param restrictions: A bdd with all restrictions on the next output
               variables.
        @type restrictions: L{BDD}
        """

        (can_be_1, can_be_0) = self.__utils.get_val(restrictions, out_var, True)

        if can_be_1 and can_be_0:
            sys.stdout.write(" (0,1): ")
            self.__writer.set_possibilities(out_var.name, "(0,1)")
        elif can_be_1:
            sys.stdout.write(" (1): ")
            self.__writer.set_possibilities(out_var.name, "( 1 )")
        elif can_be_0:
            sys.stdout.write(" (0): ")
            self.__writer.set_possibilities(out_var.name, "( 0 )")
        else:
            sys.stdout.write(" (): ")
            self.__writer.set_possibilities(out_var.name, "(   )")

