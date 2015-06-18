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
Contains a class to compute a counterstrategy.
"""

from bddwrap import BDD
import math
from nusmv import dd
from marduk_utils import Variable
from marduk_utils import VariableType

class CounterstrategyComputer(object):
    """
    Able to compute a counterstrategy for an unrealizable specification.

    A counterstrategy is a strategy for the environment.
    If the environment adheres to it, no behaviour of the system can
    implement the specification. The counterstrategy is computed in two
    steps. First, the winning region for the environment is computed. The
    winning region contains all states, from which a winning strategy for
    the environment exists. Second, a winning strategy for the
    environment is derived from the intermediate results in the
    computation of the winning region.
    
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


    def winm_env(self, early_abort = False):
        """
        Computes a winning region for the environment.

        This method computes a winning region for the environment to win a
        game against the system. The game is won for the environment if it
        manages to fulfill all its fairness constraints infinitely often
        while the system does not. This method computes all states from which
        it is possible to derive a strategy to win always (no matter how the
        system behaves). The method also returns some intermediate results
        which are necessary to derive a strategy for the environment to win
        the game.

        This method implements the mu-calculus formula:

        Z = \n
        leastFixpoint(Z)\n
        ..union(j=1..n)\n
        ....greatestFixpoint(Y)\n
        ......intersection(i=1..m)\n
        ........leastFixpoint(Y)\n
        ..........(!sys_fairness[j] union MX(Z))\n
        .................intersection\n
        ..........(MX(Y))\n
        .................intersection\n
        ..........(sys_fairness[i] union MX(X))\n
        ........ENDleastFixpoint(Y)\n
        ......ENDintersection(i=1..m)\n
        ....ENDgreatestFixpoint(Y)\n
        ..ENDunion(j=1..n)\n
        ENDleastFixpoint(Z)\n

        This is just the complementation of the mu-calculus formula defining
        the winning region of the system.

        @see: L{WinningRegion}, L{Strategy}


        @param early_abort: True if the computation should be aborted as soon
               as the initial state is contained in the winning region for the
               environment, False if the full winning region should be computed.
        @type early_abort: bool
        @return: A tuple (Z, z_array, y_array, x_array) where:
                 - Z are the winning states, i.e., the state from which it
                   is possible to derive a strategy for the environment to win
                   always.
                 - z_array[a] are the intermediate results of the fixpoint
                   computation in the variable Z. 'a' counts the iteration of
                   the fixpoint computation in Z.
                 - y_array[a][j] are the final results of the fixpoint
                   computation in the variable Y for the different a and j.
                 - x_array[a][j][i][c] are the intermediate results of the
                   fixpoint computation in the variable X for the different a,
                   j, and i. 'c' counts the iteration of the fixpoint
                   computation in X.
        @rtype: (L{BDD},
                1 dimensional array of L{BDD} objects,
                2 dimensional array of L{BDD} objects,
                4 dimensional array of L{BDD} objects,
                )
        """


        guarantees = self.__utils.guarantees
        assumptions = self.__utils.assumptions

        z_array = [] # 1 dimensional array in [a]
        y_array = [] # 2 dimensional array in [a][j]
        x_array = [] # 4 dimensional array in [a][j][i][c]
        m = len(assumptions)
        n = len(guarantees)

        Z = BDD.ZERO(self.__utils.dd_mgr)
        Z_old = BDD.ONE(self.__utils.dd_mgr)
        a = 0
        self.__utils.set_element_1d(z_array, a, Z) # z_array[a] = Z
        a += 1
        while Z != Z_old:
            Z_old = Z
            unionY = BDD.ZERO(self.__utils.dd_mgr)
            coax_env_Z = self._coax_env(Z)

            for j in range(0, n):
                Y = BDD.ONE(self.__utils.dd_mgr)
                Y_old = BDD.ZERO(self.__utils.dd_mgr)

                const_for_y_loop = (~guarantees[j]) + coax_env_Z

                while Y != Y_old:
                    Y_old = Y
                    interX = BDD.ONE(self.__utils.dd_mgr)

                    const_for_i_loop = const_for_y_loop * self._coax_env(Y)

                    for i in range(0, m):
                        X = BDD.ZERO(self.__utils.dd_mgr)
                        X_old = BDD.ONE(self.__utils.dd_mgr)
                        c = 0
                        # x_array[a][j][i][c] = X:
                        self.__utils.set_element_4d(x_array, a, j, i, c, X)
                        c += 1

                        while X != X_old:
                            X_old = X
                            X =  const_for_i_loop * \
                                (assumptions[i] + self._coax_env(X))
                            # x_array[a][j][i][c] = X:
                            self.__utils.set_element_4d(x_array, a, j, i, c, X)
                            c += 1
                        interX *= X
                    Y = interX
                #y_array[a][j] = Y:
                self.__utils.set_element_2d(y_array, a, j, Y)
                unionY += Y
            Z = unionY
            #z_array[a] = Z:
            self.__utils.set_element_1d(z_array, a, Z)
            if early_abort and self.__utils.init <= Z:
                return (Z, z_array, y_array, x_array)
            a += 1
        return (Z, z_array, y_array, x_array)



    def strategy_env(self, z_array, y_array, x_array):
        """
        Computes a counterstrategy.

        This method computes a counterstrategy, i.e., a strategy for the
        environment to win a game against the system. The game is won for the
        environment if it manages to fulfill all its fairness constraints
        infinitely often while the system does not. We introduce a finite
        memory as the value of the variables ix and jx. ix={0..m-1} stores
        the index of the set of accepting states of the environment
        (env_fairness[ix]) which will be reached next. jx={0..n} stores the
        index of the set of accepting states of the system
        (env_fairness[jx+1]) which the environment tries to evade. The
        special value jx=0 is used to indicate, that the environment has not
        yet commited to a certain jx. If the play is in z_array[a], the value
        of jx might change at most a-1 times.
        
        The strategy is derived from intermediate results of the calculation
        of the winning region for the environment. The strategy consists of
        4 parts:
        
         - rho1: This part of the strategy is applied if the play is in
           z_array[a], and the environment can force the play into a state
           of z_array[a-1]. If the play is in z_array[a], the system can
           not fulfill one of its fairness condition. The only exception
           for the system is to make a move so that a state of
           z_array[a-1] is reached next. z_array[1] will be reached
           eventually. In z_array[1] the system will never visit at least
           one of its sets of accepting states again.
         - rho2: This part of the strategy is applied if rho1 was applied in
           the previous step. In rho1, the next value of jx might depend on
           the move of the system, so rho1 can not set jx properly. rho1
           sets jx to the special value '0'. rho2 is applied if jx=0. It
           sets jx to the value of j if the play reached a state of Y[a][j]
           (maybe due to the move of the system which can not be forseen
           in rho1).
         - rho3: This part of the strategy is applied if a state of
           env_fairness[ix] is reached. In this case the value of ix is
           updated to (ix+1) mod m, so the next goal of the strategy is to
           reach a state of env_fairness[(ix+1) mod m].
         - rho4: This part of the strategy is applied if a state of
           env_fairness[ix] is not yet reached. rho3 is an attractor
           strategy that tries to get ever closer to env_fairness[ix] by
           forcing the game from x_array[a][j][i][c] into a state of
           x_array[a][j][i][c-1] until env_fairness[ix] is reached in
           x_array[a][j][i][1].
        
        @param z_array: z_array[a] contains the intermediate results of the
               fixpoint computation in the variable Z. 'a' counts the
               iteration of the fixpoint computation in Z.
        @type z_array: 1 dimensional array of L{BDD} objects
        @param y_array: y_array[a][j] contains the final results of the
               fixpoint computation in the variable Y for the different a
               and j.
        @type y_array: 2 dimensional array of L{BDD} objects
        @param x_array: x_array[a][j][i][c] contains the intermediate results
               of the fixpoint computation in the variable X for the different
               values of a, j, and i. c counts the iteration of the fixpoint
               computation in X.
        @type x_array: 4 dimensional array of L{BDD} objects
        @return: A counterstrategy, i.e., a strategy for the environment to
                 win every game against the system.
        @rtype: L{BDD}
        """

        guarantees = self.__utils.guarantees
        assumptions = self.__utils.assumptions
        env_transition = self.__utils.env_trans
        m = len(assumptions)
        n = len(guarantees)

        # generating ix and jx variables:
        (ix_mod_trans, ix_zero, all_ix_vars) = self._moduloInc(m, "ix")
        # n+1, as 0 is used as special value
        (jx_mod_trans, jx_zero, all_jx_vars) = self._moduloInc(n+1, "jx")

        self.__utils.jx_variables = all_jx_vars
        self.__utils.ix_variables = all_ix_vars

        jxnext_equal_0 = self.__utils.swap_present_next(jx_zero)
        countertrategy = BDD.ZERO(self.__utils.dd_mgr)

        #--------------------------------------------------------------------
        #rho1
        #--------------------------------------------------------------------
        rho1 = BDD.ZERO(self.__utils.dd_mgr)
        ip1 = ix_zero
        jp1 = jx_zero
        for i in range(0, m):
            ix_equal_i = ip1
            ixnext_equal_i = self.__utils.swap_present_next(ip1)
            for a in range(1, len(z_array)):
                tmp = (ix_equal_i * ixnext_equal_i
                      * jxnext_equal_0
                      * z_array[a]
                      * (~z_array[a-1])
                      * self._coax_env_input(z_array[a-1])
                      * env_transition)
                rho1 += tmp

            #ip1 = ip1+1 mod m:
            ip1 = ix_mod_trans / ip1
            ip1 = self.__utils.swap_present_next(ip1)

        countertrategy += rho1

        #--------------------------------------------------------------------
        #rho2
        #--------------------------------------------------------------------
        rho2 = BDD.ZERO(self.__utils.dd_mgr)
        for a in range(1, len(z_array)):
            jp1 = jx_zero
            # jx_zero is reserved as special value, so we start with
            # jp1 = (jp1+1)mod n = (0+1)mod n = 1:
            jp1 = jx_mod_trans / jp1
            jp1 = self.__utils.swap_present_next(jp1)
            for j in range(0, n):
                jxnext_equal_j = self.__utils.swap_present_next(jp1)

                ip1 = ix_zero
                for i in range(0, m):
                    ix_equal_i = ip1
                    ixnext_equal_i = self.__utils.swap_present_next(ip1)

                    tmp = (ix_equal_i * ixnext_equal_i
                          * jx_zero * jxnext_equal_j
                          * z_array[a]
                          * (~z_array[a-1])
                          * self._coax_env_input(y_array[a][j])
                          * ~self._coax_env(z_array[a-1])
                          * env_transition)
                    rho2 += tmp

                    #ip1 = ip1+1 mod m:
                    ip1 = ix_mod_trans / ip1
                    ip1 = self.__utils.swap_present_next(ip1)

                #jp1 = jp1+1 mod n:
                jp1 = jx_mod_trans / jp1
                jp1 = self.__utils.swap_present_next(jp1)

        countertrategy += rho2

        #--------------------------------------------------------------------
        #rho3
        #--------------------------------------------------------------------
        rho3 = BDD.ZERO(self.__utils.dd_mgr)
        for a in range(1, len(z_array)):
            jp1 = jx_zero
            # jx_zero is reserved as special value, so we start with
            # jp1 = (jp1+1)mod n = (0+1)mod n = 1:
            jp1 = jx_mod_trans / jp1
            jp1 = self.__utils.swap_present_next(jp1)
            for j in range(0, n):
                jx_equal_j = jp1
                jxnext_equal_j = self.__utils.swap_present_next(jp1)

                ip1 = ix_zero
                for i in range(0, m):
                    ix_equal_i = ip1
                    ip1 = ix_mod_trans / ip1
                    ixnext_equal_i_plus1 = ip1

                    tmp = (ix_equal_i * ixnext_equal_i_plus1
                          * jx_equal_j * jxnext_equal_j
                          * assumptions[i]
                          * z_array[a]
                          * (~z_array[a-1])
                          * self._coax_env_input(y_array[a][j])
                          * ~self._coax_env(z_array[a-1])
                          * env_transition)
                    rho3 += tmp


                    #ip1 = ip1+1 mod m:
                    ip1 = self.__utils.swap_present_next(ip1)

                #jp1 = jp1+1 mod n:
                jp1 = jx_mod_trans / jp1
                jp1 = self.__utils.swap_present_next(jp1)

        countertrategy += rho3

        #--------------------------------------------------------------------
        #rho4
        #--------------------------------------------------------------------
        rho4 = BDD.ZERO(self.__utils.dd_mgr)
        for a in range (1, len(z_array)):
            jp1 = jx_zero
            # jx_zero is reserved as special value, so we start with
            # jp1 = (jp1+1)mod n = (0+1)mod n = 1:
            jp1 = jx_mod_trans / jp1
            jp1 = self.__utils.swap_present_next(jp1)
            for j in range(0, n):
                jx_equal_j = (jp1)
                jxnext_equal_j = self.__utils.swap_present_next(jp1)

                ip1 = ix_zero
                for i in range(0, m):
                    ix_equal_i = ip1
                    ixnext_equal_i = self.__utils.swap_present_next(ip1)

                    for c in range(1, len(x_array[a][j][i])):
                        tmp = (ix_equal_i * ixnext_equal_i
                            * jx_equal_j * jxnext_equal_j
                            * x_array[a][j][i][c]
                            * ~(x_array[a][j][i][c-1])
                            * z_array[a]
                            * (~z_array[a-1])
                            * self._coax_env_input(x_array[a][j][i][c-1])
                            * ~self._coax_env(z_array[a-1])
                            * env_transition)
                        rho4 += tmp

                    #ip1 = ip1+1 mod m:
                    ip1 = ix_mod_trans / ip1
                    ip1 = self.__utils.swap_present_next(ip1)

                #jp1 = jp1+1 mod n:
                jp1 = jx_mod_trans / jp1
                jp1 = self.__utils.swap_present_next(jp1)

        countertrategy += rho4

        return countertrategy




    def strategy_env_fast(self, z_array, y_array, x_array, restrict = True):
        """
        Computes a counterstrategy.

        This method computes a counterstrategy, i.e., a strategy for the
        environment to win a game against the system. The method is equal to
        the method strategy_env, but it is faster (and less easy to read).
        The counterstrategy computation is restricted to reachable states
        (unless deactivated). The intermediate results in y_array and x_array
        are freed as soon as possible to increase the chance of finding a good
        variable ordering.

        @note: The elements in y_array and x_array can not be used after
               executing this method! They are destroyed in this method.

        The strategy is derived from intermediate results of the calculation
        of the winning region for the environment. The strategy consists of
        4 parts:

         - rho1: This part of the strategy is applied if the play is in
           z_array[a], and the environment can force the play into a state
           of z_array[a-1]. If the play is in z_array[a], the system can
           not fulfill one of its fairness condition. The only exception
           for the system is to make a move so that a state of
           z_array[a-1] is reached next. z_array[1] will be reached
           eventually. In z_array[1] the system will never visit at least
           one of its sets of accepting states again.
         - rho2: This part of the strategy is applied if rho1 was applied in
           the previous step. In rho1, the next value of jx might depend on
           the move of the system, so rho1 can not set jx properly. rho1
           sets jx to the special value '0'. rho2 is applied if jx=0. It
           sets jx to the value of j if the play reached a state of Y[a][j]
           (maybe due to the move of the system which can not be forseen
           in rho1).
         - rho3: This part of the strategy is applied if a state of
           env_fairness[ix] is reached. In this case the value of ix is
           updated to (ix+1) mod m, so the next goal of the strategy is to
           reach a state of env_fairness[(ix+1) mod m].
         - rho4: This part of the strategy is applied if a state of
           env_fairness[ix] is not yet reached. rho3 is an attractor
           strategy that tries to get ever closer to env_fairness[ix] by
           forcing the game from x_array[a][j][i][c] into a state of
           x_array[a][j][i][c-1] until env_fairness[ix] is reached in
           x_array[a][j][i][1].

        @param z_array: z_array[a] contains the intermediate results of the
               fixpoint computation in the variable Z. 'a' counts the
               iteration of the fixpoint computation in Z.
        @type z_array: 1 dimensional array of L{BDD} objects
        @param y_array: y_array[a][j] contains the final results of the
               fixpoint computation in the variable Y for the different a
               and j.
        @type y_array: 2 dimensional array of L{BDD} objects
        @param x_array: x_array[a][j][i][c] contains the intermediate results
               of the fixpoint computation in the variable X for the different
               values of a, j, and i. c counts the iteration of the fixpoint
               computation in X.
        @type x_array: 4 dimensional array of L{BDD} objects
        @return: A counterstrategy, i.e., a strategy for the environment to
                 win every game against the system.
        @rtype: L{BDD}
        """

        guarantees = self.__utils.guarantees
        assumptions = self.__utils.assumptions
        env_transition = self.__utils.env_trans
        m = len(assumptions)
        n = len(guarantees)

        # generating ix and jx variables:
        (ix_mod_trans, ix_zero, all_ix_vars) = self._moduloInc(m, "ix")
        # n+1, as 0 is used as special value
        (jx_mod_trans, jx_zero, all_jx_vars) = self._moduloInc(n+1, "jx")

        self.__utils.jx_variables = all_jx_vars
        self.__utils.ix_variables = all_ix_vars

        jxnext_equal_0 = self.__utils.swap_present_next(jx_zero)

        reachable = BDD.ONE(self.__utils.dd_mgr)
        if restrict:
            reachable = self._compute_reachable_states()

        countertrategy = BDD.ZERO(self.__utils.dd_mgr)

        for a in range (1, len(z_array)):

            also_needed_for_rho1 = z_array[a] * (~z_array[a-1]) * env_transition
            force_z_a_1 = self._coax_env(z_array[a-1])
            # We cannot remove z_array[a-1] here, since we need it to know how
            # often jx will change in the future
            const_for_j_loop = (also_needed_for_rho1 * (~force_z_a_1))
            const_for_j_loop //= reachable

            const_for_rho1_loop = (also_needed_for_rho1
                                * self._coax_env_input(z_array[a-1])
                                * jxnext_equal_0)
            const_for_rho1_loop //= reachable

            del force_z_a_1
            del also_needed_for_rho1
            ip1 = ix_zero
            for i in range(0, m):
                ix_equal_i = ip1
                ixnext_equal_i = self.__utils.swap_present_next(ip1)

                tmp_rho1 = (ix_equal_i * ixnext_equal_i
                            * const_for_rho1_loop)
                tmp_rho1 //= reachable
                countertrategy += tmp_rho1
                del tmp_rho1

                #ip1 = ip1+1 mod m:
                ip1 = ix_mod_trans / ip1
                ip1 = self.__utils.swap_present_next(ip1)
            del const_for_rho1_loop



            jp1 = jx_zero
            # jx_zero is reserved as special value, so we start with
            # jp1 = (jp1+1)mod n = (0+1)mod n = 1:
            jp1 = jx_mod_trans / jp1
            jp1 = self.__utils.swap_present_next(jp1)
            for j in range(0, n):
                jx_equal_j = (jp1)
                jxnext_equal_j = self.__utils.swap_present_next(jp1)

                const_for_i_loop = const_for_j_loop * jxnext_equal_j
                const_for_i_loop //= reachable

                const_for_i_loop2 = (const_for_i_loop
                                  * self._coax_env_input(y_array[a][j]))
                const_for_i_loop2 //= reachable
                y_array[a][j] = None
                const_for_i_loop_r2 = const_for_i_loop2 * jx_zero
                const_for_i_loop_r3 = const_for_i_loop2 * jx_equal_j
                del const_for_i_loop2

                ip1 = ix_zero
                for i in range(0, m):
                    ix_equal_i = ip1
                    ixnext_equal_i = self.__utils.swap_present_next(ip1)
                    ip1 = ix_mod_trans / ip1
                    ixnext_equal_i_plus1 = ip1

                    const_for_c_loop = (const_for_i_loop
                                     * ix_equal_i
                                     * jx_equal_j
                                     * ixnext_equal_i)

                    const_for_c_loop //= reachable

                    for c in range(1, len(x_array[a][j][i])):
                        tmp_rho4 = (const_for_c_loop
                                 * x_array[a][j][i][c]
                                 * ~(x_array[a][j][i][c-1])
                                 * self._coax_env_input(x_array[a][j][i][c-1]))
                        x_array[a][j][i][c-1] = None
                        tmp_rho4 //= reachable
                        countertrategy += tmp_rho4
                        del tmp_rho4
                    x_array[a][j][i][len(x_array[a][j][i])-1] = None

                    del const_for_c_loop

                    tmp_rho2 = (ix_equal_i * ixnext_equal_i
                             * const_for_i_loop_r2)
                    tmp_rho2 //= reachable
                    countertrategy += tmp_rho2
                    del tmp_rho2

                    tmp_rho3 = (ix_equal_i * ixnext_equal_i_plus1
                             * const_for_i_loop_r3
                             * assumptions[i])
                    tmp_rho3 //= reachable
                    countertrategy += tmp_rho3
                    del tmp_rho3

                    #ip1 = ip1+1 mod m:
                    ip1 = self.__utils.swap_present_next(ip1)

                del const_for_i_loop
                del const_for_i_loop_r2
                del const_for_i_loop_r3


                #jp1 = jp1+1 mod n:
                jp1 = jx_mod_trans / jp1
                jp1 = self.__utils.swap_present_next(jp1)

            del const_for_j_loop

        return countertrategy


    def _coax_env(self, states):
        """
        Computes the mixed preimage of a set of states.

        This method calculates all states from which it is possible for the
        environment to force the play into 'states' in one step. It is very
        similar to the coax method of the L{WinningRegion}. Basically the input
        variables and the output variables are swapped because the coax
        method in the L{WinningRegion} calculates the states from which the
        system can force a play into 'states'.

        @note: This method does not call self._coax_env_input since
               A.andExists(B,C) is more efficient than (A*b).exists(C).

        @param states: A bdd representing a set of states.
        @type states: L{BDD}
        @return: All states from which it is possible for the environment to
                 force a play into 'states' in one step.
        @rtype: L{BDD}
        """
        env_transitions = self.__utils.env_trans
        sys_transitions = self.__utils.sys_trans
        output_product = self.__utils.next_out_var_cube
        input_product = self.__utils.next_in_var_cube

        swapped_states = self.__utils.swap_present_next(states)
        target_or_forbidden = (~sys_transitions) + swapped_states
        env_moves_to_target = (target_or_forbidden).forall(output_product)
        mixed_preimage = env_moves_to_target.andExists(env_transitions, \
                                                       input_product)
        return mixed_preimage

    def _coax_env_input(self, states):
        """
        Computes the mixed preimage with the according inputs.

        This method calculates all pairs (old_state, next_input) so that
        it is possible for the environment to force the play from old_state
        into 'states' in one step with the next input 'next_input'.
        
        @param states: A bdd representing a set of states.
        @type states: L{BDD}
        @return: A bdd containing all pairs (old_state, next_input) so that
                 it is possible for the environment to force the play from
                 old_state into states in one step with the next input
                 next_input.
        @rtype: L{BDD}
        """
        env_transitions = self.__utils.env_trans
        sys_transitions = self.__utils.sys_trans
        output_product = self.__utils.next_out_var_cube

        swapped_states = self.__utils.swap_present_next(states)
        target_or_forbidden = (~sys_transitions) + swapped_states
        env_moves_to_target = (target_or_forbidden).forall(output_product)
        allowed_env_moves_to_target = env_moves_to_target * env_transitions
        return allowed_env_moves_to_target



    def _generate_vars(self, n, name):
        """
        Generates n variables.

        This method generates n bdd variables. Each variable consists of two
        bdd variables: one for the current state and one for the next state.
        @return: A tuple (present_bdds, next_bdds, all_vars) where:
                 - present_bdds is a list of all current bdd variables.
                 - present_bdds is a list of all next bdd variables.
                 - all_vars is the list of all variables.
        @rtype: (list<L{BDD}>,
                list<L{BDD}>,
                list<L{Variable}>)
        """
        present_bdds = []
        next_bdds = []
        all_vars = []

        for i in range(0,n):
            var_name = name + "_" + str(i)
            tmp = dd.bdd_new_var(self.__utils.dd_mgr)
            present = BDD(tmp, self.__utils.dd_mgr, var_name + "_ps")
            dd.bdd_free(self.__utils.dd_mgr, tmp)
            present_bdds.append(present)
            tmp = dd.bdd_new_var(self.__utils.dd_mgr)
            next = BDD(tmp, self.__utils.dd_mgr, var_name + "_ns")
            dd.bdd_free(self.__utils.dd_mgr, tmp)
            next_bdds.append(next)
            var = Variable(var_name, VariableType.STATE, present, next)
            all_vars.append(var)

        return(present_bdds, next_bdds, all_vars)





    def _moduloInc(self, n, name):
        """
        Creates a transition relation for the state variables in
        the counterstrategy.

        This method creates a transition relation which implements the
        transition "ijx=(ijx+1) mod n". So the transition relation will produce
        ijx = 0, 1, 2, ... n, 0, 1, ... n if applied successively. It also
        creates the variables needed for this transition relation.
        
        @param n: The modulo value.
        @type n: int
        @return: A tuple (trans_relation, start_state, all_vars) where:
                 - trans_relation represents the transition relation
                 - start_state is the start state
                 - all_vars contains all created variables.
        @rtype: (L{BDD}, L{BDD}, list<L{Variable}>)
        """

        if n == 0 :
            print "modulo_inc for 0 does not make sense!"
            return (BDD.ZERO(self.__utils.dd_mgr), \
                    BDD.ZERO(self.__utils.dd_mgr), \
                    BDD.ZERO(self.__utils.dd_mgr), \
                    BDD.ZERO(self.__utils.dd_mgr))

        num_of_bits = int(math.ceil(math.log(n,2)))
        if num_of_bits == 0: #n = 1
            num_of_bits = 1

        (present_vars, next_vars, all_vars) = \
                                        self._generate_vars(num_of_bits, name)
        trans_relation = BDD.ONE(self.__utils.dd_mgr)
        carry = BDD.ONE(self.__utils.dd_mgr)

        for i in range(0, num_of_bits):
            trans_relation *= (~next_vars[i] + (carry ^ present_vars[i])) * \
                              (~(carry ^ present_vars[i]) + next_vars[i])

            carry *= present_vars[i]

        reset_condition = BDD.ONE(self.__utils.dd_mgr)
        reset_state = BDD.ONE(self.__utils.dd_mgr)
        start_state = BDD.ONE(self.__utils.dd_mgr)
        bit_selector = n-1
        for i in range(0,num_of_bits):
            if ((bit_selector & 0x1) == 1):
                reset_condition *= present_vars[i]
            else:
                reset_condition *= ~present_vars[i]

            bit_selector = bit_selector >> 1
            reset_state *= ~next_vars[i]
            start_state *= ~present_vars[i]

        case_increase = reset_condition + trans_relation
        case_reset = ~reset_condition + reset_state

        trans_relation = case_increase * case_reset

        return (trans_relation, start_state, all_vars)


    def _compute_reachable_states(self):
        """
        Computes all states reachable from the initial state.

        This method computes all states reachable from the initial state.
        @return: all states reachable from the initial state.
        @rtype: L{BDD}
        """
        trans = self.__utils.trans
        present_vars_cube = self.__utils.all_present_vars_cube
        reach = self.__utils.init.copy()
        old_reach = BDD.ONE(self.__utils.dd_mgr)
        while not(old_reach == reach):
            old_reach = reach.copy()
            tmp = reach.andExists(trans, present_vars_cube)
            tmp = self.__utils.swap_present_next(tmp)
            reach += tmp

        return reach


    def _add_violatation_of_safety_constraints(self, counterstrategy):
        """
        Gives priority to the violation of safety constraints.

        This function computes another substrategy rho5 which tries to violate
        safety guarantees. It also adds this substrategy to the counterstrategy
        with priority over all other substrategies.

        @note: This function is experimental and not (yet) used.

        @param counterstrategy: The counterstrategy to which the new
               substrategy is added.
        @type counterstrategy: L{BDD}
        @return: The passed counterstrategy enhanced with the additional
                 substrategy.
        @rtype: L{BDD}
        """

        # some aliases to keep the code lines short and readable:
        utils = self.__utils
        sys_trans = utils.sys_trans

        # Step 1:
        # compute a strategy for states in which sys_trans can be forced to
        # be false immediately:
        output_product = utils.next_out_var_cube
        rho5 = (~sys_trans).forall(output_product)

        # Step 2:
        # compute all states from which the play can be forced into a situation
        # for which the strategy obtained in Step1 can be applied:
        sys_tran_can_be_false = utils.keep_only_present(additional_strategy)
        z_array = []
        Z = BDD.ZERO(self.__utils.dd_mgr)
        Z_old = BDD.ONE(self.__utils.dd_mgr)
        while Z != Z_old:
            Z_old = Z
            z_array.append(Z)
            Z = sys_tran_can_be_false + self._coax_env(Z)

        # Step3:
        # compute a counterstrategy that forces the play ever closer to a
        # situation for which the strategy obtained in Step1 can be applied
        # (this is a simple attractor strategy):
        for a in range(2, len(z_array)):
                tmp = (z_array[a] * (~z_array[a-1])
                      * self._coax_env_input(z_array[a-1])
                      * utils.env_trans)
                rho5 += tmp

        # Step 4:
        # Apply the counterstrategy violating fairness constraints only if
        # there is no counterstrategy that violates safety constraints:
        return rho5 + ((~Z) * counterstrategy)



