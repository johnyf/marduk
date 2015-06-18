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
Contains a class that checks for satisfiability.
"""

from bddwrap import BDD

class SatSolver(object):
    """
    Able to check if a specification is satisfiable.

    A specification is satisfiable if a sequence of inputs and outputs
    exists, so that the specification is fulfilled. A GR(1) specification
    is fulfilled if all sets of accepting states of the system are
    visited infinitely often, or if not all sets of accepting states of
    the environment are visited infinitely often.

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



    def is_satisfiable(self):
        """
        Checks if a specification is satisfiable.

        A specification is satisfiable if a sequence of inputs and outputs
        exists, so that the specification is fulfilled. A GR(1) specification
        is fulfilled if all sets of accepting states of the system are visited
        infinitely often, or if not all sets of accepting states of the
        environment are visited infinitely often.

        @return: True if the specification is satisfiable and False otherwise.
        @rtype: bool
        """

        if self.__utils.init.isZero():
            # A specification with an empty set of initial states is
            # unsatisfiable:
            return False

        sat = False

        # The question is: can
        # (AND_i GF(env_fairness[i])) -> (AND_j GF(sys_fairness[j]))
        #   = !(AND_i GF(env_fairness[i])) OR (AND_j GF(sys_fairness[j]))
        #   = (OR_i !GF(env_fairness[i])) OR (AND_j GF(sys_fairness[j]))
        #   = (OR_i FG(!env_fairness[i])) OR (AND_j GF(sys_fairness[j]))
        # be satisfied???

        # Part 1 of the question:
        # Can (OR_i FG(!env_fairness[i])) be satisfied ?
        finally_globally_not_env_fair = self._finally_globally_not_env_fair()
        if (self.__utils.init * finally_globally_not_env_fair).isNotZero():
            print "FG(!assumption[i]) can be satisfied for some i"
            sat = True

        # Part 2 of the question:
        # Can (AND_j GF(sys_fairness[j])) be satisfied ?
        globally_finally_all_sys_fair = self._globally_finally_all_sys_fair()
        if (self.__utils.init * globally_finally_all_sys_fair).isNotZero():
            print "GF(guarantee[j]) can be satisfied for all j"
            sat = True
        
        return sat




    def _globally_finally_all_sys_fair(self):
        """
        Computes the cooperative winning region for fulfilling all fairness constraints of the system.

        This method computes all states from which there exists a sequence of
        inputs and outputs so that all sys_fairness[j] are visited infinitely
        often.

        @return: All states from which there exists a sequence of inputs and
                 outputs so that all sys_fairness[j] are visited infinitely
                 often.
        @rtype: L{BDD}
        """

        n = len(self.__utils.guarantees)
        # First of all we compute the cooperative winning region of a
        # generalized buechi game. This is basically equal to the computation
        # of the winning region of a buechi game, only the operator EX is
        # used instead of MX (instead of coax).
        Y = BDD.ONE(self.__utils.dd_mgr)
        Y_old = BDD.ZERO(self.__utils.dd_mgr)
        while Y != Y_old:
            Y_old = Y
            tmp = BDD.ONE(self.__utils.dd_mgr)
            for j in range(0, n):
                Z = BDD.ZERO(self.__utils.dd_mgr)
                Z_old = BDD.ONE(self.__utils.dd_mgr)
                while Z != Z_old:
                    Z_old = Z
                    Z = Y * (self.__utils.guarantees[j] + self._ex(Z))
                tmp *= self._ex(Z)
            Y = tmp
        # The result is now in Y.

        # Finally we compute all states from which one of the previously
        # computed states Y can be reached:
        R = BDD.ZERO(self.__utils.dd_mgr)
        R_old = BDD.ONE(self.__utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = Y + self._ex(R)
        
        # The result is in R.
        return R
        


    def _finally_globally_not_env_fair(self):
        """
        Computes the cooperative winning region for evading a fairness
        constraint of the environment.

        This method computes all states from which there exists a sequence of
        inputs and outputs so that not all env_fairness[i] are visited
        infinitely often.

        @return: All states from which there exists a sequence of inputs and
                outputs so that not all env_fairness[i] are visited
                infinitely often.
        @rtype: L{BDD}
        """
        m = len(self.__utils.assumptions)

        # First of all we compute a region, in which one of the
        # env_fairness[i] is never fulfilled while there exist a sequence of
        # inputs and outputs so that this region is never left again:
        globally_not_env_fair = BDD.ZERO(self.__utils.dd_mgr)
        for i in range(0, m):
            Y = BDD.ONE(self.__utils.dd_mgr)
            Y_old = BDD.ZERO(self.__utils.dd_mgr)
            while Y != Y_old:
                Y_old = Y
                Y = (~self.__utils.assumptions[i]) * self._ex(Y)
            globally_not_env_fair += Y
        # The result is now in globally_not_env_fair.

        # Finally we compute all states from which one of the previously
        # computed states globally_not_env_fair can be reached:
        R = BDD.ZERO(self.__utils.dd_mgr)
        R_old = BDD.ONE(self.__utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = globally_not_env_fair + self._ex(R)

        # The result is now in R.
        return R
        

    def _ex(self, states):
        """
        Computes all predecessors of a set of states.

        This method computs all states from which 'states' can be reached in
        one step (i.e., there exists an input and an output, so that the next
        state is from 'states').

        @param states: A set of states.
        @type states: L{BDD}
        @return: All states from which 'states' can be reached in one step.
        @rtype: L{BDD}
        """
        vars = self.__utils.next_out_var_cube * self.__utils.next_in_var_cube
        swapped_states = self.__utils.swap_present_next(states)
        result = swapped_states.andExists(self.__utils.trans, vars)
        return result
        
