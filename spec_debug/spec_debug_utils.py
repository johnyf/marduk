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
Contains a utility class needed for various specification debugging features.
"""

import marduk_utils
from nusmv import prop
from nusmv.game import bddfsm
from nusmv import dd
from bddwrap import BDD
import sys

class SpecDebugUtils(object): 
    """
    A utility class needed for various specification debugging features.

    This class has two purposes. On the one hand, it contains data which
    is needed almost everywhere during the different steps of debugging
    an unrealizable specification. During the execution, all data is read
    from this class rather than from the various classes responsible for
    synthesis. This breaks up the dependence on the synthesis classes.
    On the other hand, this class contains a lot of utility functions
    which are needed by various specification debugging features.
    
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """
    def __init__(self, marduk):
        """
        Constructor.

        @param marduk: The main class containing all command line options and
               relevant data.
        @type marduk: L{Marduk}
        """

        #: The dd manager that is used for debugging.
        #: @type: DDManager
        self.__dd_mgr = marduk.dd_mgr

        #: The name of the input file.
        #: @type: string
        self.__input_file = marduk.input_file

        #: A list containing all jx variables.
        #: @type: list<L{Variable}>
        self.__jx_vars = []

        #: A list containing all jx variables.
        #: @type: list<L{Variable}>
        self.__ix_vars = []

        #: A list containing all input variables.
        #: @type: list<L{Variable}>
        self.__input_vars = marduk.input_vars

        #: A list containing all output variables.
        #: @type: list<L{Variable}>
        self.__output_vars = marduk.output_vars

        #: A list containing all variables in the dd manager.
        #: @type: list<L{Variable}>
        self.__vars_in_manager = marduk.vars

        #: A list containing all output variables which are relevant for
        #: unrealizability.
        #:
        #: Some outputs are irrelevant, i.e., removing them by existentially
        #: quantifying them preserves unrealizability.
        #: @type: list<L{Variable}>
        self.__relevant_out_vars = marduk.output_vars

        #: The specification in use.
        #: @type: L{Specification}
        self.__spec = marduk.specification

        #: A bdd representing the transition relation of the environment.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: L{BDD}
        self.__env_trans = None

        #: A bdd representing the transition relation of the system.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: L{BDD}
        self.__sys_trans = None

        #: A bdd representing the transition relation of the specification.
        #:
        #: This is the transition relation of the environment and the system in
        #: conjunction.
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: L{BDD}
        self.__trans = None

        #: A bdd representing the initial condition for the environment.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: L{BDD}
        self.__env_init = None

        #: A bdd representing the initial condition for the system.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: L{BDD}
        self.__sys_init = None

        #: A bdd representing the initial condition for the environment and
        #: the system.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: L{BDD}
        self.__init = None

        #: A list of bdds, each representing a fairness constraint of the
        #: system.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: list<L{BDD}>
        self.__guarantees = None

        #: A list of bdds, each representing a fairness constraint of the
        #: environment.
        #:
        #: It is transferred to the dd manager that is used for debugging on
        #: demand, i.e., if read out for the first time. (Keeping the number of
        #: bdds in the manager small often increases the performance).
        #: @type: list<L{BDD}>
        self.__assumptions = None

        #: A list of bdds, each representing the present state of a certain
        #: variable.
        #: @type: list<L{BDD}>
        self.__present_var_bdds = []

        #: A list of bdds, each representing the next state of a certain
        #: variable.
        #: @type: list<L{BDD}>
        self.__next_var_bdds = []

        #: A cube of all present input variables.
        #: @type: L{BDD}
        self.__present_input_cube = None

        #: A cube of all next input variables.
        #: @type: L{BDD}
        self.__next_input_cube = None

        #: A cube of all present output variables.
        #: @type: L{BDD}
        self.__present_output_cube = None

        #: A cube of all next output variables.
        #: @type: L{BDD}
        self.__next_output_cube = None

        #: A cube of all present ix-variables.
        #: @type: L{BDD}
        self.__present_ix_cube = None

        #: A cube of all next ix-variables.
        #: @type: L{BDD}
        self.__next_ix_cube = None

        #: A cube of all present jx-variables.
        #: @type: L{BDD}
        self.__present_jx_cube = None

        #: A cube of all next jx-variables.
        #: @type: L{BDD}
        self.__next_jx_cube = None

        #: A cube of all present variables.
        #: @type: L{BDD}
        self.__present_cube = None

        #: A cube of all next variables.
        #: @type: L{BDD}
        self.__next_cube = None

        #: The reordering method for dynamic reordering
        #: @type: int
        self.__dyn_reorder_method = marduk.dyn_reorder_method

        #: The reordering method for forced reorderings
        #: @type: int
        self.__reorder_method = marduk.reorder_method

        self._init_cubes()

    def _init_cubes(self):
        """
        Initializes all cubes.
        """
        self.__present_input_cube = BDD.ONE(self.__dd_mgr)
        self.__next_input_cube = BDD.ONE(self.__dd_mgr)
        for in_var in self.__input_vars:
            self.__present_input_cube *= in_var.ps
            self.__next_input_cube *= in_var.ns
            self.__present_var_bdds.append(in_var.ps)
            self.__next_var_bdds.append(in_var.ns)
        self.__present_output_cube = BDD.ONE(self.__dd_mgr)
        self.__next_output_cube = BDD.ONE(self.__dd_mgr)
        for out_var in self.__output_vars:
            self.__present_output_cube *= out_var.ps
            self.__next_output_cube *= out_var.ns
            self.__present_var_bdds.append(out_var.ps)
            self.__next_var_bdds.append(out_var.ns)
        self.__present_ix_cube = BDD.ONE(self.__dd_mgr)
        self.__next_ix_cube = BDD.ONE(self.__dd_mgr)
        for ix_var in self.__ix_vars:
            self.__present_ix_cube *= ix_var.ps
            self.__next_ix_cube *= ix_var.ns
            self.__present_var_bdds.append(ix_var.ps)
            self.__next_var_bdds.append(ix_var.ns)
        self.__present_jx_cube = BDD.ONE(self.__dd_mgr)
        self.__next_jx_cube = BDD.ONE(self.__dd_mgr)
        for jx_var in self.__jx_vars:
            self.__present_jx_cube *= jx_var.ps
            self.__next_jx_cube *= jx_var.ns
            self.__present_var_bdds.append(jx_var.ps)
            self.__next_var_bdds.append(jx_var.ns)
        self.__present_cube = self.__present_input_cube *\
                              self.__present_output_cube *\
                              self.__present_ix_cube *\
                              self.__present_jx_cube
        self.__next_cube = self.__next_input_cube *\
                           self.__next_output_cube *\
                           self.__next_ix_cube *\
                           self.__next_jx_cube


    def get_spec(self):
        """
        Returns specification in use.

        @return: The specification in use.
        @rtype: L{Specification}
        """
        return self.__spec

    #: The specification in use.
    #: @type: L{Specification}
    spec = property(get_spec)

    def get_dd_mgr(self):
        """
        Returns the dd manager that is used for debugging.

        @return: The dd manager that is used for debugging.
        @rtype: DDManager
        """
        return self.__dd_mgr

    #: The dd manager that is used for debugging.
    #: @type: DDManager
    dd_mgr = property(get_dd_mgr)

    def get_input_file_name(self):
        """
        Returns the name of the input file

        @return: The name of the input file.
        @rtype: string
        """
        return self.__input_file

    #: The name of the input file.
    #: @type: string
    input_file = property(get_input_file_name)

    def set_ix_variables(self, ix_vars):
        """
        Sets the list of ix-variables and updates all cubes.

        @param ix_vars: The list of ix-variables.
        @type ix_vars: list<L{Variable}>
        """
        self.__ix_vars = ix_vars
        self._init_cubes()

    def get_ix_variables(self):
        """
        Returns the list of ix-variables.

        @return: The list of ix-variables.
        @rtype: list<L{Variable}>
        """
        return self.__ix_vars

    #: A list containing all ix variables.
    #: @type: list<L{Variable}>
    ix_variables = property(get_ix_variables, set_ix_variables)

    def set_jx_variables(self, jx_vars):
        """
        Sets the list of jx-variables and updates all cubes.

        @param jx_vars: The list of jx-variables.
        @type jx_vars: list<L{Variable}>
        """
        self.__jx_vars = jx_vars
        self._init_cubes()

    def get_jx_variables(self):
        """
        Returns the list of ix-variables.

        @return: The list of ix-variables.
        @rtype: list<L{Variable}>
        """
        return self.__jx_vars

    #: A list containing all jx variables.
    #: @type: list<L{Variable}>
    jx_variables = property(get_jx_variables, set_jx_variables)

    def get_input_vars(self):
        """
        Returns the list of input variables.

        @return: The list of input variables.
        @rtype: list<L{Variable}>
        """
        return self.__input_vars

    #: A list containing all input variables.
    #: @type: list<L{Variable}>
    input_vars = property(get_input_vars)

    def get_output_vars(self):
        """
        Returns the list of output variables.

        @return: The list of output variables.
        @rtype: list<L{Variable}>
        """
        return self.__output_vars

    #: A list containing all output variables.
    #: @type: list<L{Variable}>
    output_vars = property(get_output_vars)

    def get_in_out_vars(self):
        """
        Returns a list containing all input- and output-variables.

        @return: A list containing all input- and output-variables.
        @rtype: list<L{Variable}>
        """
        all_vars = self.__input_vars[:]
        all_vars.extend(self.__output_vars)
        return all_vars

    #: A list containing all input- and output-variables.
    #: @type: list<L{Variable}>
    in_out_vars = property(get_in_out_vars)

    def get_in_rel_out_vars(self):
        """
        Returns a list containing all input- and relevant output-variables.
        Relevant means relevant for unrealizability (some outputs are
        irrelevant, i.e. removing them by existentially quantifying them
        preserves unrealizability).

        @return: A list containing all input- and relevant output-variables.
        @rtype: list<L{Variable}>
        """
        all_vars = self.__input_vars[:]
        all_vars.extend(self.__relevant_out_vars)
        return all_vars

    #: A list containing all input- and relevant output-variables.
    #: @type: list<L{Variable}>
    in_rel_out_vars = property(get_in_rel_out_vars)

    def get_relevant_out_vars(self):
        """
        Returns the list of relevant output variables.

        This method returns a list of output variables which are
        relevant for unrealizability (some outputs are irrelevant, i.e.
        removing them by existentially quantifying them preserves
        unrealizability).

        @return: The list of relevant output variables.
        @rtype: list<L{Variable}>
        """
        return self.__relevant_out_vars

    def set_relevant_out_vars(self, rel_out_vars):
        """
        Sets the list of relevant output variables.

        This method sets a list of output variables which are
        relevant for unrealizability (some outputs are irrelevant, i.e.
        removing them by existentially quantifying them preserves
        unrealizability).

        @param rel_out_vars: The list of relevant output variables.
        @type rel_out_vars: list<L{Variable}>
        """
        self.__relevant_out_vars = rel_out_vars

    #: A list containing all relevant output variables
    #: @type: list<L{Variable}>
    relevant_out_vars = property(get_relevant_out_vars, set_relevant_out_vars)

    def get_env_trans(self):
        """
        Returns the transition relation of the environment.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The transition relation of the environment.
        @rtype: L{BDD}
        """
        if self.__env_trans == None:
            self.__env_trans = self.__spec.get_trans1(self.__dd_mgr)
        return self.__env_trans

    def set_env_trans(self, env_trans):
        """
        Sets the transition relation of the environment.

        @param env_trans: The transition relation of the environment.
        @type env_trans: L{BDD}
        """
        self.__env_trans = env_trans
        if self.__sys_trans != None:
            self.__trans = self.__env_trans * self.__sys_trans

    #: A bdd representing the transition relation of the environment.
    #: @type: L{BDD}
    env_trans = property(get_env_trans, set_env_trans)

    def get_sys_trans(self):
        """
        Returns the transition relation of the system.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The transition relation of the system.
        @rtype: L{BDD}
        """
        if self.__sys_trans == None:
            self.__sys_trans = self.__spec.get_trans2(self.__dd_mgr)
        return self.__sys_trans

    def set_sys_trans(self, sys_trans):
        """
        Sets the transition relation of the system.

        @param sys_trans: The transition relation of the system.
        @type sys_trans: L{BDD}
        """
        self.__sys_trans = sys_trans
        if self.__env_trans != None:
            self.__trans = self.__env_trans * self.__sys_trans

    #: A bdd representing the transition relation of the system.
    #: @type: L{BDD}
    sys_trans = property(get_sys_trans, set_sys_trans)

    def get_trans(self):
        """
        Returns the transition relation.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The transition relation.
        @rtype: L{BDD}
        """
        if self.__trans == None:
            self.__trans = self.__spec.get_trans12(self.__dd_mgr)
        return self.__trans

    #: A bdd representing the transition relation.
    #: @type: L{BDD}
    trans = property(get_trans)

    def get_env_init(self):
        """
        Returns the initial condition for the environment.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The initial condition for the environment.
        @rtype: L{BDD}
        """
        if self.__env_init == None:
            self.__env_init = self.__spec.get_init1(self.__dd_mgr)
        return self.__env_init

    def set_env_init(self, env_init):
        """
        Sets the initial condition for the environment.

        @param env_init: The initial condition for the environment.
        @type env_init: L{BDD}
        """
        self.__env_init = env_init
        if self.__sys_init != None:
            self.__init = self.__env_init * self.__sys_init

    #: A bdd representing the initial condition for the environment.
    #: @type: L{BDD}
    env_init = property(get_env_init, set_env_init)

    def get_sys_init(self):
        """
        Returns the initial condition for the system.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The initial condition for the system.
        @rtype: L{BDD}
        """
        if self.__sys_init == None:
            self.__sys_init = self.__spec.get_init2(self.__dd_mgr)
        return self.__sys_init

    def set_sys_init(self, sys_init):
        """
        Sets the initial condition for the system.

        @param sys_init: The initial condition for the system.
        @type sys_init: L{BDD}
        """
        self.__sys_init = sys_init
        if self.__env_init != None:
            self.__init = self.__env_init * self.__sys_init

    #: A bdd representing the initial condition for the system.
    #: @type: L{BDD}
    sys_init = property(get_sys_init, set_sys_init)

    def get_init(self):
        """
        Returns the initial condition for environment and system.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The initial condition.
        @rtype: L{BDD}
        """
        if self.__init == None:
            self.__init = self.__spec.get_init12(self.__dd_mgr)
        return self.__init

    #: A bdd representing the initial condition.
    #: @type: L{BDD}
    init = property(get_init)

    def get_init_ix_jx(self):
        """
        Returns the initial condition, the ix- and jx-variables initilized too.

        @return: The initial condition with ix- and jx-variables.
        @rtype: L{BDD}
        """
        if self.__init == None:
            self.__init = self.__spec.get_init12(self.__dd_mgr)
        res = BDD.ONE(self.__dd_mgr)
        for ix_var in self.__ix_vars:
            res *= ~(ix_var.ps)
        for jx_var in self.__jx_vars:
            res *= ~(jx_var.ps)
        return res * self.__init

    #: A bdd representing the initial condition including ix- and jx-variables.
    #: @type: L{BDD}
    init_ix_jx = property(get_init_ix_jx)
    
    def get_env_init_ix_jx(self):
        """
        Returns the initial environment condition with ix- and jx-variables.

        @return: The initial condition of the environment with ix- and 
        jx-variables.
        @rtype: L{BDD}
        """
        if self.__env_init == None:
            self.__env_init = self.__spec.get_init1(self.__dd_mgr)
        res = BDD.ONE(self.__dd_mgr)
        for ix_var in self.__ix_vars:
            res *= ~(ix_var.ps)
        for jx_var in self.__jx_vars:
            res *= ~(jx_var.ps)
        return res * self.__env_init

    #: A bdd representing the initial condition including ix- and jx-variables.
    #: @type: L{BDD}
    env_init_ix_jx = property(get_env_init_ix_jx)

    def get_guarantees(self):
        """
        Returns the list of all fairness constraints of the system.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The list of all fairness constraints of the system.
        @rtype: list<L{BDD}>
        """
        if self.__guarantees == None:
            self.__guarantees = self.__spec.get_guarantees(self.__dd_mgr)
        return self.__guarantees

    def set_guarantees(self, guarantees):
        """
        Sets the list of all fairness constraints of the system.

        @param guarantees: The list of all fairness constraints of the system.
        @type guarantees: list<L{BDD}>
        """
        self.__guarantees = guarantees

    #: A list of bdds representing the fairness constraints of the system.
    #: @type: list<L{BDD}>
    guarantees = property(get_guarantees, set_guarantees)

    def get_assumptions(self):
        """
        Returns the list of all fairness constraints of the environment.

        It is transferred to the dd manager that is used for debugging on
        demand, i.e., if read out for the first time. (Keeping the number of
        bdds in the manager small often increases the performance).

        @return: The list of all fairness constraints of the environment.
        @rtype: list<L{BDD}>
        """
        if self.__assumptions == None:
            self.__assumptions = self.__spec.get_assumptions(self.__dd_mgr)
        return self.__assumptions

    def set_assumptions(self, assumptions):
        """
        Sets the list of all fairness constraints of the environment.

        @param assumptions: The list of all fairness constraints of the
               environment.
        @type assumptions: list<L{BDD}>
        """
        self.__assumptions = assumptions

    #: A list of bdds representing the fairness constraints of the environment.
    #: @type: list<L{BDD}>
    assumptions = property(get_assumptions, set_assumptions)

    def get_next_out_var_cube(self):
        """
        Returns a cube of all next output variables.

        @return: A cube of all next output variables.
        @rtype: L{BDD}
        """
        return self.__next_output_cube

    #: A cube of all next output variables.
    #: @type: L{BDD}
    next_out_var_cube = property(get_next_out_var_cube)

    def get_next_in_var_cube(self):
        """
        Returns a cube of all next input variables.

        @return: A cube of all next input variables.
        @rtype: L{BDD}
        """
        return self.__next_input_cube

    #: A cube of all next input variables.
    #: @type: L{BDD}
    next_in_var_cube = property(get_next_in_var_cube)
    
    def get_present_out_var_cube(self):
        """
        Returns a cube of all present output variables.

        @return: A cube of all present output variables.
        @rtype: L{BDD}
        """
        return self.__present_output_cube

    #: A cube of all present output variables.
    #: @type: L{BDD}
    present_out_var_cube = property(get_present_out_var_cube)

    def get_present_in_var_cube(self):
        """
        Returns a cube of all present input variables.

        @return: A cube of all present input variables.
        @rtype: L{BDD}
        """
        return self.__present_input_cube

    #: A cube of all present input variables.
    #: @type: L{BDD}
    present_in_var_cube = property(get_present_in_var_cube)

    def get_all_present_vars_cube(self):
        """
        Returns a cube of all present variables.

        @return: A cube of all present variables.
        @rtype: L{BDD}
        """
        return self.__present_cube

    #: A cube of all present variables.
    #: @type: L{BDD}
    all_present_vars_cube = property(get_all_present_vars_cube)

    def get_present_jx_cube(self):
        """
        Returns a cube of all present jx-variables.

        @return: A cube of all present jx-variables.
        @rtype: L{BDD}
        """
        return self.__present_jx_cube

    #: A cube of all present jx-variables.
    #: @type: L{BDD}
    present_jx_cube = property(get_present_jx_cube)

    def keep_only_present(self, bdd):
        """
        Throws away all restritions on next variables.

        This method throws away all restrictions on the next-values of all
        variables in a given bdd. It does this by applying the existence
        quantifier on all next-values of all variables.
        
        @param bdd: The bdd in which all restrictions on the next-values
               should be thrown away.
        @type bdd: L{BDD}
        @return: The bdd in which all restrictions on the next-values are
               thrown away.
        @rtype: L{BDD}
        """
        return bdd.exists(self.__next_cube)

    def keep_only_next(self, bdd):
        """
        Throws away all restritions on present variables.
        
        This method throws away all restrictions on the present-values of all
        variables in a given bdd. It does this by applying the existence
        quantifier on all present-values of all variables.
        
        @param bdd: The bdd in which all restrictions on the present-values
               should be thrown away.
        @type bdd: L{BDD}
        @return: The bdd in which all restrictions on the present-values are
                 thrown away.
        @rtype: L{BDD}
        """
        return bdd.exists(self.__present_cube)

    def keep_only_present_inputs(self, bdd):
        """
        Removes all variables from a bdd except for present input variables.

        This method removes all variables from a bdd except for present input
        variables by applying the existance quantor.
        
        @param bdd: An arbitrary bdd.
        @type bdd: L{BDD}
        @return: The bdd where all variables except for present inputs are
                 removed.
        @rtype: L{BDD}
        """
        cube =  self.__next_cube * self.__present_ix_cube *\
                self.__present_jx_cube * self.__present_output_cube
        return bdd.exists(cube)

    def keep_only_next_inputs(self, bdd):
        """
        Removes all variables from a bdd except for next input variables.

        This method removes all variables from a bdd except for next input
        variables by applying the existance quantor.
        
        @param bdd: An arbitrary bdd.
        @type bdd: L{BDD}
        @return: The bdd where all variables except for next inputs are
                 removed.
        @rtype: L{BDD}
        """
        cube =  self.__present_cube * self.__next_ix_cube *\
                self.__next_jx_cube * self.__next_output_cube
        return bdd.exists(cube)

    def remove_next_ix_jx_outputs(self, bdd):
        """
        Removes all next ix-, jx-, and output-variables.

        This method removes all next ix-, jx-, and ouput-variables from a
        bdd by applying the existance quantor.
        
        @param bdd: An arbitrary bdd.
        @type bdd: L{BDD}
        @return: The bdd where all next ix-, jx-, and ouput-variables are
                 removed.
        @rtype: L{BDD}
        """
        cube = self.__next_ix_cube * self.__next_jx_cube *\
               self.__next_output_cube
        return bdd.exists(cube)

    def swap_present_next(self, bdd):
        """
        Swaps all present and all next variables.

        This method swaps the present state variables and the next state
        variables in the passed bdd.
        
        @param bdd: The bdd where the state variables should be swapped.
        @type bdd: L{BDD}
        @return: A bdd where the state variables are swapped.
        @rtype: L{BDD}
        """
        return bdd.swapVariables(self.__present_var_bdds, self.__next_var_bdds)

    def choose_val(self, bdd, var, current_next):
        """
        Chooses the value of a variable in a bdd.

        This method chooses one of the possible values of a variable of a
        bdd. If the bdd allows the variable only to be 0, 0 is chosen. If the
        bdd allows the variable only to be 1, 1 is chosen. If the bdd allows
        both, 1 is chosen. The method returns the chosen value for the
        variable (0 or 1) together with the new bdd where the variable is
        already set to the chosen value. With the parameter current_next
        it is possible to choose either the current value of the variable
        (current_next=False) or the next value (current_next=True).
        
        @param bdd: The bdd in which we choose a variable.
        @type bdd: L{BDD}
        @param var: The variable to choose
        @type var: L{Variable}
        @param current_next: False to choose the current value and True to
               choose the next value.
        @type current_next: bool
        @return: The chosen value of the variable (so either 0 or 1) togehter
                 with the new bdd where the variable is set to the chosen
                 value.
        @rtype: (int, L{BDD})
        """
        (can_be_1, can_be_0) = self.get_val(bdd, var, current_next)
        var_bdd = var.ps
        if current_next:
            var_bdd = var.ns

        if can_be_1 and (not can_be_0):
            # the variable can only be 1, so we set it to 1:
            return (1, bdd * var_bdd)
        if (not can_be_1) and can_be_0:
            # the variable can only be 0, so we set it to 0:
            return (0, bdd * (~var_bdd))
        if (not can_be_1) and (not can_be_0):
            # The variable can't be true or false (i.e. the bdd is already
            # the zero bdd):
            return (None, BDD.ZERO(self.__dd_mgr))
        if can_be_1 and can_be_0:
            # both, 0 and 1 are possible, in this case we choose 1:
            return (1, bdd * var_bdd)

    def get_val(self, bdd, var, current_next):
        """
        Returns possible values for a variable in a bdd.

        This method checks if 0 or 1 are possible for a certain variable in a
        given bdd. A variable value is impossible if the AND interconnection
        with the bdd leads to the zero bdd. With the parameter current_next
        it is possible to check either the current value of the variable
        (current_next=False) or the next value (current_next=True).
        
        @param bdd: The bdd in which we check for possible values for the
               variable.
        @type bdd: L{BDD}
        @param var: The variable to check.
        @type var: L{Variable}
        @param current_next: False to check the current value and True to check
               the next value.
        @type current_next: bool
        @return: (can_be_1, can_be_0) where:
                 - can_be_1: True if the value of the variable can be 1,
                   False otherwise
                 - can_be_0: True if the value of the variable can be 0,
                   False otherwise
        @rtype: (bool, bool)
        """
        var_is_1_bdd = var.ps
        if current_next:
            var_is_1_bdd = var.ns
        can_be_1 = True
        can_be_0 = True
        if (bdd * var_is_1_bdd).isZero():
            # The variable has to be 0. If it would be 1, this would lead to 
            # the zero bdd
            can_be_1 = False
        if (bdd * (~var_is_1_bdd)).isZero():
            # The variable has to be 0. If it would be 1, this would lead to 
            # the zero bdd
            can_be_0 = False
        return (can_be_1, can_be_0)

    def get_val_as_string(self, bdd, var, current_next):
        """
        Returns the value of a variable in a bdd as string.

        Returns "1" if a certain variable in a bdd can only be 1,
        "0" if it can only be 0, "*" if it can be both and "X" if the bdd is
        the Zero-bdd. With the parameter current_next it is possible to check
        either the current value of the variable (current_next=False) or the
        next value (current_next=True).

        @param bdd: The bdd in which we check for possible values for the
               variable.
        @type bdd: L{BDD}
        @param var: The variable to check.
        @type var: L{Variable}
        @param current_next: False to check the current value and True to check
               the next value.
        @type current_next: bool
        @return: The value of the variable in the bdd as string.
        @rtype: string
        """
        (can_be_1, can_be_0) = self.get_val(bdd, var, current_next)
        symb = "*"
        if can_be_1 and (not can_be_0):
            symb = "1"
        elif (not can_be_1) and can_be_0:
            symb = "0"
        elif (not can_be_1) and (not can_be_0):
            symb = "X"
        return symb



    def choose_all_next_inputs(self, possible_next_inputs):
        """
        Chooses all next inputs in a bdd and returns the bdd.
        
        @param possible_next_inputs: A bdd where the next inputs should be
               chosen.
        @type possible_next_inputs: L{BDD}
        @return: The bdd where the next inputs are chosen.
        @rtype: L{BDD}
        """
        next_inputs = possible_next_inputs.copy()
        for in_var in self.__input_vars:
            (val, next_inputs) = self.choose_val(next_inputs, in_var, True)
        return next_inputs

    def get_next_inputs(self, state, step_count, counterstrategy, \
                        countertrace):
        """
        Chooses all next inputs given a certain state.

        This method chooses all next inputs given a certain state. With the
        counterstrategy, all inputs are computed which are winning for the
        environment. If we have not found a countertrace, we choose one of
        these inputs arbitrarily. If a countertrace is available, we choose
        the input conforming to the countertrace. The counterstrategy is used
        in parallel with the countertrace if a countertrace is available,
        since the counterstrategy is also able to define the values for ix
        and jx. The information in ix and jx is not necessary in presence of
        a countertrace, but it might be useful for the user. Using both, the
        counterstrategy and the countertrace in parallel is possible since
        the countertrace can not be in contradiction with the countertrace.
        The countertrace is just more precise.
        
        @param state: A bdd containing the current state, the play is in.
        @type state: L{BDD}
        @param step_count: The current value of the step counter. It is
               needed if the input is chosen according to a countertrace.
        @type step_count: int
        @param counterstrategy: A counterstrategy, i.e., a strategy for the
               environment to find inputs so that the system is forced to
               violate the specification.
        @type counterstrategy: L{BDD}
        @param countertrace: A sequence of inputs so that the system is forced
               to violate its specification.
        @type countertrace: L{InfiniteTraceOfBdds}
        @return: The bdd current_state where all next input variables
               are chosen.
        @rtype: L{BDD}
        """
        next_inputs = state * counterstrategy
  
        # If we have a countertrace, we choose the input conforming to this
        # countertrace:
        if countertrace:
            bdd = countertrace.get_bdd_to_step(step_count + 1)
            return next_inputs * self.swap_present_next(bdd)
  
        # Otherwise we choose the next inputs arbitrary conforming to the
        # counterstrategy:
        return self.choose_all_next_inputs(next_inputs)


    def _get_decimal_value_of_ix_jx(self, state, var_list, current_next):
        """
        Computes the decimal value of the ix- or jx variables.

        This method computes the decimal value of either the ix variables or
        the jx variables dependend on which variables are passed as var_list
        parameter (either self.__ix_vars or self.__jx_vars).
        The calculation works in the following way: Whenever a certain bit is
        set, 2**(position of the bit) is added to the value.
        
        @param state: The state for which you want to calculate the decimal
               value of the ix- or the jx-variables.
        @type state: L{BDD}
        @param var_list: Either self.__ix_vars or self.__jx_vars.
        @type var_list: list<L{Variable}>
        @param current_next: False to get the current value and True to get
               the next value.
        @type current_next: bool
        @return: The decimal value corresponding to the binary values of
                 the jx- or ix-variables.
        @rtype: int
        """
        value = 0
        for var in var_list:
            (can_be_1, can_be_0) = self.get_val(state, var, current_next)
            if can_be_1 and (not can_be_0):
                value += (2**int(var.name[3:]))
            elif (not can_be_1) and can_be_0:
                # nothing to be done here (nothing to add to value)
                pass
            else:
                return None
        return value

    def get_decimal_ix_val(self, state, current_next):
        """
        Computes the decimal value of the ix variables.
        
        @param state: The state for which you want to calculate the decimal
               value of the ix-variables.
        @type state: L{BDD}
        @param current_next: False to get the current value and True to get the
               next value.
        @type current_next: bool
        @return: The decimal value corresponding to the binary values of
                 the ix-variables.
        @rtype: int
        """
        return self._get_decimal_value_of_ix_jx(state, self.__ix_vars, \
                                                current_next)
    def get_decimal_jx_val(self, state, current_next):
        """
        Computes the decimal value of the jx variables.

        This method computes the decimal value of the jx variables. As the
        value jx=0 is reserved, the value corresponding to the jx variables
        is incremented by 1.
        
        @param state: The state for which you want to calculate the decimal
               value of the jx-variables.
        @type state: L{BDD}
        @param current_next: False to get the current value and True to get
               the next value.
        @type current_next: bool
        @return: The decimal value corresponding to the binary values of
                 the jx-variables (+1 as jx=0 is reserved).
        @rtype: int
        """
        val = self._get_decimal_value_of_ix_jx(state, self.__jx_vars, \
                                               current_next)
        if val and val > 0:
            return val - 1 #jx=0 is reserved as invalid value
        return None


    def how_often_may_jx_change(self, state, z_array):
        """
        Finds out, how often jx might change in the further play.

        Returns a-1 if the passed state is in z_array[a] but not
        in z_array[a-1]. This value is maximal number of changes of the
        memory jx of the counterstrategy in the sequel of the play if the
        play is in the state 'state'.
        
        @param state: Some state the play might be in.
        @type state: L{BDD}
        @param z_array: z_array[a] contains the intermediate results of the
               fixpoint computation in the variable Z of the computation of
               the winning region for the environment. 'a' counts the
               iterations of the fixpoint computation in Z. It is used to
               figure out how often the value of jx might still change in the
               future of the play. (If the play is in z_array[a], jx might
               change at most a-1 times.)
        @type z_array: list<L{BDD}>
        @return: The maximal number of changes of jx in the sequal of the play
                 from the state 'state'.
        @rtype: int
        """
        for a in range(1, len(z_array)):
            if (state * z_array[a]).isNotZero():
                return a-1
        return None


    def get_bit(self, number, pos):
        """
        Returns the bit at position pos in number.

        @param number: An integer where we want to know a certain bit.
        @type number: int
        @param pos: The position of the bit we want to know (starting with 0)
        @type pos: int
        @return: The desired bit (so either 0 or 1).
        @rtype: int
        """
        return ((number & (1 << pos)) != 0)


    def secure_transition_relations(self):
        """
        Makes the transition relation water proof.

        This method is just a fix: The grammar allows things like:
        G((var=1) -> FALSE);
        The bdd says nothing about the next values of var, it only says
        that the current value of var must not be 0. This might become a
        problem in games and graph computation. We might have to choose
        the next value of var. The bdd says: 'of course you can set the
        next value of var to 1'. In the next step however it says that
        this was not right. Therefore we add all restrictions on present
        vars to next vars as well.

        @note: When nusmv is used as parser, this method is not necessary.
        """
        if self.__env_trans == None:
            self.__env_trans = self.__spec.get_trans1(self.__dd_mgr)
        if self.__sys_trans == None:
            self.__sys_trans = self.__spec.get_trans2(self.__dd_mgr)
        present_sys_trans = self.keep_only_present(self.__sys_trans)
        self.__sys_trans *= self.swap_present_next(present_sys_trans)
        present_env_trans = self.keep_only_present(self.__env_trans)
        self.__env_trans *= self.swap_present_next(present_env_trans)
        self.__trans = self.__env_trans * self.__sys_trans


    def set_element_1d(self, array, dim1, elem):
        """
        Does: array[dim1] = elem

        This method does array[dim1] = elem. If the list does not contain so
        many elements, the list is extended to that length.

        @param array: An arbitrary one dimensional array.
        @type array: list
        @param dim1: The index in the first dimension.
        @type dim1: int
        @param elem: The element to set.
        @type elem: any type
        """
        while dim1 >= len(array):
            array.append(None)
        array[dim1] = elem

    def set_element_2d(self, array, dim1, dim2, elem):
        """
        Does: array[dim1][dim2] = elem

        This method does array[dim1][dim2] = elem. If the list does not
        contain so many elements, the list is extended to that length.

        @param array: An arbitrary two dimensional array.
        @type array: list
        @param dim1: The index in the first dimension.
        @type dim1: int
        @param dim2: The index in the second dimension.
        @type dim2: int
        @param elem: The element to set.
        @type elem: any type
        """
        while dim1 >= len(array):
            array.append([])
        while dim2 >= len(array[dim1]):
            array[dim1].append(None)
        array[dim1][dim2] = elem

    def set_element_3d(self, array, dim1, dim2, dim3, elem):
        """
        Does: array[dim1][dim2][dim3] = elem

        This method does array[dim1][dim2][dim3] = elem. If the list does not
        contain so many elements, the list is extended to that length.

        @param array: An arbitrary two dimensional array.
        @type array: list
        @param dim1: The index in the first dimension.
        @type dim1: int
        @param dim2: The index in the second dimension.
        @type dim2: int
        @param dim3: The index in the third dimension.
        @type dim3: int
        @param elem: The element to set.
        @type elem: any type
        """
        while dim1 >= len(array):
            array.append([])
        while dim2 >= len(array[dim1]):
            array[dim1].append([])
        while dim3 >= len(array[dim1][dim2]):
            array[dim1][dim2].append(None)
        array[dim1][dim2][dim3] = elem

    def set_element_4d(self, array, dim1, dim2, dim3, dim4, elem):
        """
        Does: array[dim1][dim2][dim3][dim4] = elem

        This method does array[dim1][dim2][dim3][dim4] = elem. If the list
        does not contain so many elements, the list is extended to that length.

        @param array: An arbitrary two dimensional array.
        @type array: list
        @param dim1: The index in the first dimension.
        @type dim1: int
        @param dim2: The index in the second dimension.
        @type dim2: int
        @param dim3: The index in the third dimension.
        @type dim3: int
        @param dim4: The index in the fourth dimension.
        @type dim4: int
        @param elem: The element to set.
        @type elem: any type
        """
        while dim1 >= len(array):
            array.append([])
        while dim2 >= len(array[dim1]):
            array[dim1].append([])
        while dim3 >= len(array[dim1][dim2]):
            array[dim1][dim2].append([])
        while dim4 >= len(array[dim1][dim2][dim3]):
            array[dim1][dim2][dim3].append(None)
        array[dim1][dim2][dim3][dim4] = elem

    def enable_dyn_reordering(self):
        """
        Enables the dynamic reordering of bdds.
        """
        dd.dd_autodyn_enable(self.__dd_mgr, self.__dyn_reorder_method)

    def disable_dyn_reordering(self):
        """
        Disables the dynamic reordering of bdds.
        """
        dd.dd_autodyn_disable(self.__dd_mgr)

    def reorder_bdds(self):
        """
        Triggers a reordering of all bdds.
        """
        dd.dd_reorder(self.__dd_mgr, self.__reorder_method, 0)


    def get_var_ordering(self):
        return marduk_utils.print_variable_ordering(self.__vars_in_manager)

    def set_var_ordering(self, ordering):
        marduk_utils.set_variable_ordering(ordering, self.__vars_in_manager,
                                           self.__dd_mgr)


class PLog(object):
    """
    A logger for performance measures.

    This class is used to log performance measures into a file and to STDOUT.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    #: The log file to write to.
    #: @type: file
    _log_file_name = None

    #: The name of the log file to write to.
    #: @type: string
    _log_file = None

    def _set_log_file(filename):
        """
        Sets the log file to write to.

        This method opens a file with the specified name and uses it for all
        further logging.

        @param filename: The name of the file to be use for logging.
        @type filename: string
        """

        if PLog._log_file:
            PLog._log_file.close()
        PLog._log_file_name = filename
        PLog._log_file = open(filename, 'a')

    #: Sets the log file to write to.
    set_log_file = staticmethod(_set_log_file)

    def _close():
        """
        Closes the file currently used for logging.
        """
        PLog._log_file.close()
        PLog._log_file = None
        PLog._log_file_name = None

    #: Closes the file currently used for logging.
    close = staticmethod(_close)

    def _log(msg):
        """
        Logs a message to the logfile and to STDOUT

        @param msg: A message to be logged.
        @type msg: string
        """
        sys.stdout.write(msg)
        if PLog._log_file:
            PLog._log_file.write(msg)
            PLog._log_file.flush()

    #: Logs a message to the logfile and to STDOUT
    log = staticmethod(_log)


