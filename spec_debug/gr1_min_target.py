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
Contains classes that define a minimization target for GR1 specs.
"""

from spec_debug_utils import PLog
from nusmv import parser
from nusmv.parser import symbols
from xml.dom.minidom import parse, parseString
import time
from bddwrap import BDD
from nusmv import game
from nusmv import cmd
from nusmv import prop
from nusmv.game import bddfsm
from nusmv import dd
from nusmv.enc import bdd
from nusmv import node
from nusmv import enc
import sys
import re
import os

class GR1Sect(object):
    """
    Contains constants for the sections in a GR1 specification.
    """

    #: A constant for the section that contains the input variables.
    #: @type: string
    IN_VARS = "INPUT_VARIABLES"

    #: A constant for the section that contains the initial condition for the
    #: environment.
    #: @type: string
    ENV_INIT = "ENV_INITIAL"

    #: A constant for the section that contains the transition relation for
    #: the environment.
    #: @type: string
    ENV_TRANS = "ENV_TRANSITIONS"

    #: A constant for the section that contains the fairness constraints for
    #: the environment.
    #: @type: string
    ENV_FAIR = "ENV_FAIRNESS"

    #: A constant for the section that contains the output variables.
    #: @type: string
    OUT_VARS = "OUTPUT_VARIABLES"

    #: A constant for the section that contains the initial condition for the
    #: system.
    #: @type: string
    SYS_INIT = "SYS_INITIAL"

    #: A constant for the section that contains the transition relation for
    #: the system.
    #: @type: string
    SYS_TRANS = "SYS_TRANSITIONS"

    #: A constant for the section that contains the fairness constraints for
    #: the environment.
    #: @type: string
    SYS_FAIR = "SYS_FAIRNESS"

    #: A list containing all constants for all sections.
    #: @type: list<string>
    ALL = [IN_VARS, ENV_INIT, ENV_TRANS, ENV_FAIR, \
           OUT_VARS, SYS_INIT, SYS_TRANS, SYS_FAIR]

    def _sect_from_alias(alias):
        """
        Returns the constant for the section, given an alias of a section.

        Given an alias for the name of the section, this method returns the
        constant that represents the section. The alias must contain 'sys' or
        'env' as well as 'init', 'trans', or 'fair', all either upper case
        or lower case to be handled correctly.

        @param alias: An alias of the section name.
        @type alias: string
        @return: The constant representing the section.
        @rtype: string
        """
        alias = alias.lower().strip().rstrip()
        if alias.count("init") > 0 and alias.count("sys") > 0:
            return GR1Sect.SYS_INIT
        if alias.count("init") > 0 and alias.count("env") > 0:
            return GR1Sect.ENV_INIT
        if alias.count("tran") > 0 and alias.count("sys") > 0:
            return GR1Sect.SYS_TRANS
        if alias.count("tran") > 0 and alias.count("env") > 0:
            return GR1Sect.ENV_TRANS
        if alias.count("fair") > 0 and alias.count("sys") > 0:
            return GR1Sect.SYS_FAIR
        if alias.count("fair") > 0 and alias.count("env") > 0:
            return GR1Sect.ENV_FAIR

    #: Returns the constant for the section, given an alias of a section.
    sect_from_alias = staticmethod(_sect_from_alias)


class MinTarget(object):
    """
    An interface for all minimization targets.

    This is an interface that must be implemented by all minimization targets.
    All minimizers use an implementation of this interface for minimization.
    The methods get_elements_to_minimize() and test() must be overridden in
    the class that implements the interface. All other methods can be
    overriden.

    @see: L{SimpleMinimizer}
    @see: L{DeltaDebugger}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self):
        """
        Constructor.
        """
        self.__log_file = None

    def set_log_file(self, log_file):
        """
        Sets a log file.

        This method remembers the passed log file in order to use it for
        logging information. The passed log file must be opened for writing.
        """
        self.__log_file = log_file

    def _log(self, msg, nr_spaces = 0):
        """
        Logs a message.

        This method adds a message to the log file self.__log_file.
        The message is indented by nr_spaces spaces. If no log file was set,
        this method does nothing at all.

        @param msg: The message to log.
        @type msg: string
        @param nr_spaces: The number of spaces to put in front of the message.
        @type nr_spaces: int
        """
        if not self.__log_file:
            #print (" " * nr_spaces) + msg
            return
        self.__log_file.write(" " * nr_spaces)
        self.__log_file.write(msg)
        self.__log_file.write("\n")

    def get_elements_to_minimize(self):
        """
        Returns a list of elements that should be minimized by a minimizer.

        This method returns a list of elements that should be minimized by a
        minimizer. The elements can have an arbitrary type. Each element could
        for instance represent a formula in a specification.

        @note: This method must be overridden in the derived class.
        @return: A list of elements that should be minimized.
        @rtype: list<some type>
        """
        print "ERROR: MinTarget::get_elements_to_minimize called!"
        print "ERROR: Override this method in a derived class!"
        exit(-1)

    def get_string_rep(self, subset):
        """
        Returns the string representation of a list of elements.

        This method returns the string representation of a list of elements.
        If the method is not overridden in the derived class, it simply casts
        the passed list to a string.

        @param subset: A list of elements. It has to contain a subset of the
               elements returned by get_elements_to_minimize.
        @type subset: list<some type>
        @return: The string representation of a list of elements.
        @rtype: string
        """
        return str(subset)

    def test(self, subset, spaces):
        """
        Tests a subset for some property.

        This method tests a subset of the elements produced by
        get_elements_to_minimize for some property.

        @note: This method must be overridden in the derived class.
        @param subset: A list of elements. It has to contain a subset of the
               elements returned by get_elements_to_minimize.
        @type subset: list<some type>
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: True or False.
        @rtype: bool
        """
        print "ERROR: MinTarget::test called!"
        print "ERROR: Override this method in a derived class!"
        exit(-1)

    def set_final_solution(self, result):
        """
        Informs about the final solution of the minimization.

        This method is used by the minimizer to inform about the final
        solution of the minimization. If it is not overridden, the final
        solution is just printed to STDOUT.

        @param result: The final solution of the minimization. It has to
               contain a subset of the elements returned by
               get_elements_to_minimize.
        @type result: list<some type>
        """
        print "Final solution is:", result

class GR1MinTarget(MinTarget):
    """
    A minimization target that represents a GR(1) specification.

    This class represents a GR(1) specification that is minimized. We aim at
    finding a smaller specification that is still unrealizable. Hence the
    method test() checks for realizability.

    The idea is then to find the problem in the (simpler) specification
    much faster, because all formulas that are irrelevant for unrealizability
    have been removed. Only the statements really causing the problem remain.

    Only guarantees of the system (SYS_TRANSITIONS and SYS_FAIRNESS) are
    minimized. Assumptions are not minimized since leaving them out will
    always lead to a specification with is not realizable (even worse than
    before). Output variables which are not involved in the conflict that
    makes the specification unrealizable are removed as well by existential
    quantification in the guarantees. Minimization is done on the granularity
    of LTL formulas.

    The file ./spec_debug/<filename>.xml is created. It contains the minimal
    specification that still is not realizable.

    @see: L{SimpleMinimizer}
    @see: L{DeltaDebugger}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, utils, minimize, use_result, target_file_name):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        @param minimize: A dictionary that maps constants for sections as
               defined in L{GR1Sect} to True if the section should be minimized
               and to False if the section should not be minimized. Sections
               that do not occur in this dictionary are not minimized.
        @type minimize: dictionary<string, bool>
        @param use_result: True if the result of the minimization should be
               stored in self.__utils, False otherwise
        @type use_result: bool
        @param target_file_name: The name of the file for the minimized
               specification or None if it should not be written.
        @type target_file_name: string
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: A dictionary that tells us, which sections should be minimized.
        #:
        #: A dictionary that maps constants for sections as defined in
        #: L{GR1Sect} to True if the section should be minimized and to False
        #: if the section should not be minimized.
        #: @type: dictionary<string, bool>
        self.__minimize = minimize

        #: True if the result of the minimization should be stored in
        #: self.__utils, False otherwise.
        #: @type: bool
        self.__use_result = use_result

        #: The name of the file for the minimized specification.
        #: @type: string
        self.__target_file_name = target_file_name

        # If a section does not occur in self.__minimize, we do not minimize
        # it. To avoid key errors, we map missing sections to 0.
        for section in GR1Sect.ALL:
            if not section in self.__minimize.keys():
                self.__minimize[section] = 0

        #: All parts of all sections.
        #:
        #: A dictionary that maps all constants for sections as defined in
        #: L{GR1Sect} to a list of elements in this section. For the sections
        #: IN_VARS and OUT_VARS, these elements are L{Variable} objects. For
        #: all other sections, the elements are L{BDD} objects, each
        #: representing a formula in the section.
        #: @type: dictionary<string, list<L{BDD}>>
        self.__section_parts = {}

        #: All sizes of all sections.
        #:
        #: A dictionary that maps all constants for sections as defined in
        #: L{GR1Sect} to thier size, i.e. to the number of formulas that
        #: occur in this section.
        #: @type: dictionary<string, int>
        self.__size = {}

        #: The current specification to check for realizability.
        #:
        #: A dictionary that maps all constants for sections as defined in
        #: L{GR1Sect} to bdds representing this section.
        #: @type: dictionary<string, L{BDD}>
        self.__current = {}

        #: A counter, counting the realizability checks.
        #: @type: int
        self.__realizability_checks = 0

        #: A counter, counting all skipped realizability checks.
        #:
        #: A counter, counting the number of realizability checks that do
        #: not really have to be performed as a superset of restrictions
        #: of the system is already realizable.
        #: @type: int
        self.__checks_covered_by_supersets = 0

        #: A list of all specifications that are realizable.
        #:
        #: A list of all specifications that are realizable. All subsets of
        #: a realizable specification are again realizable. This can be
        #: used to reduce the number of realizability checks.
        #: @type: list<set<int>>
        self.__realizable_sets = []

        # For the sections ENV_INIT, SYS_INIT, ENV_TRANS, and SYS_TRANS, we
        # have to get bdds, each representing a certain formula in this
        # section. This is done with the class L{SpecSplitterHack}. It is
        # more of a hack than a solution to get this information out of nusmv,
        # hence the name of the class ;-). Maybe this will be fixed in the
        # future.
        splitter = SpecSplitterHack(self.__utils)
        self.__section_parts[GR1Sect.IN_VARS] = utils.input_vars
        self.__section_parts[GR1Sect.OUT_VARS] = utils.output_vars
        self.__section_parts[GR1Sect.ENV_FAIR] = utils.assumptions
        self.__section_parts[GR1Sect.SYS_FAIR] = utils.guarantees
        self.__section_parts[GR1Sect.ENV_INIT] = splitter.env_init_bdds
        self.__section_parts[GR1Sect.SYS_INIT] = splitter.sys_init_bdds
        self.__section_parts[GR1Sect.ENV_TRANS] = splitter.env_trans_bdds
        self.__section_parts[GR1Sect.SYS_TRANS] = splitter.sys_trans_bdds

        # Computing the size of all sections:
        for section in GR1Sect.ALL:
            self.__size[section] = len(self.__section_parts[section])


    def get_elements_to_minimize(self):
        """
        Returns a list of elements that should be minimized by a minimizer.

        This method returns a list of indices of formulas. This list contains
        the index of every formula that should be minimized.

        @return: A list of indices of formulas that should be minimized.
        @rtype: list<int>
        """
        return self._get_indices_of_formulas_to_minimize()

    def test(self, subset, spaces):
        """
        Checks for realizability.

        This method checks if a certain specification represented by the
        indices of the formulas that are in the specification is realizable.
        It does this by computing the winning region an checking if the
        initial state is in this winning region. It uses the method
        winm_fast for the computation of the winning region. This is basically
        the method calcWinningRegion of the L{WinningRegion}. Only the
        intermediate results that are needed for the computation of the
        strategy are not computed as we just want to know if the spec
        is realizable or not. In order to minimize the number of calls to
        the function winm_fast, we first check if a superset of restrictions
        of the system is already realizable. If this is the case, the
        specification to be checked will be realizable as well. This property
        speeds things up.

        @param subset: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas.
        @type subset: list<int>
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: True if the specification is realizable, False otherwise
        @rtype: bool
        """

        return self._is_realizable(subset, spaces)

    def get_string_rep(self, subset):
        """
        Returns the string representation of a list of formulas.

        This method takes a list of indices of formulas and produced a nice
        to read string containing the names of the formulas.

        @param subset: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas.
        @type subset: list<int>
        @return: A string containing the names of all formulas.
        @rtype: string
        """

        result_string = "";
        for elem in subset:
            result_string += self._get_formula_name(elem) + ","

        #get rid of the last ',':
        result_string = result_string[0:-1]
        return "{" + result_string + "}"

    def set_final_solution(self, result):
        """
        Stores the final minimization result in self.__utils if desired.

        This method is used by the minimizer to inform about the final
        solution of the minimization. If self.__use_result is True, the
        resulting specification is written into self.__utils. All further
        debugging operations read the specification form there, so all further
        debugging operations use the minimized specification. If self.__utils
        is False, the minimized specification is not stored.
        Some performance measures are logged and the minimized specification
        is written to ./spec_debug_results/delta.xml.

        @param result: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas. It is the
               minimal set of formulas so that the specification is
               unrealizable.
        @type result: list<int>
        """

        # writing some statistics into the log file:
        self._log_statistics(result)

        # writing the result into the file ./spec_debug_results/delta.xml
        self._write_configuration(result)

        # Writing all formulas that are listed in result into self.__current:
        self._prepare_configuration(result)

        # If the result of the delta debugging algorithm should be used, we
        # copy the final result from self.__current into self.__utils. The
        # bdds for all further debugging operations are read from there.
        if self.__use_result:
            self.__utils.guarantees = self.__current[GR1Sect.SYS_FAIR]
            self.__utils.assumptions = self.__current[GR1Sect.ENV_FAIR]
            self.__utils.sys_trans = self.__current[GR1Sect.SYS_TRANS]
            self.__utils.env_trans = self.__current[GR1Sect.ENV_TRANS]
            self.__utils.sys_init = self.__current[GR1Sect.SYS_INIT]
            self.__utils.env_init = self.__current[GR1Sect.ENV_INIT]
            rel_out_vars = self._get_relevant_out_vars(result)
            self.__utils.relevant_out_vars = rel_out_vars


    def _get_indices_of_formulas_to_minimize(self):
        """
        Returns a list of formulas that should be minimized by a minimizer.

        This method returns a list of indices of formulas. This list contains
        the index of every formula that should be minimized.

        @return: A list of indices of formulas that should be minimized.
        @rtype: list<int>
        """
        indices = []
        for section in self.__minimize.keys():
            if self.__minimize[section]:
                for i in range(0, self.__size[section]):
                    indices.append(self._get_index_to_formula_nr(i, section))
        return indices

    def _is_realizable(self, subset, spaces):
        """
        Checks for realizability.

        This method checks if a certain specification represented by the
        indices of the formulas that are in the specification is realizable.
        It does this by checking if the initial state is in the winning
        region with the method winm_contains. In order to minimize the number
        of calls to the function winm_contains, we first check if a superset of
        restrictions of the system is already realizable. If this is the case,
        the specification to be checked will be realizable as well. This
        property speeds things up.

        @param subset: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas.
        @type subset: list<int>
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: True if the specification is realizable, False otherwise
        @rtype: bool
        """

        starttime = time.clock()
        self.__realizability_checks += 1

        if self._superset_already_realizable(subset):
            self.__checks_covered_by_supersets += 1
            msg = "checking with " + self.get_string_rep(subset)
            msg += " (superset already realizable)"
            msg += " (%10.3f sec)" % (time.clock() - starttime)
            msg += " -> realizable"
            self._log(msg, spaces)
            return True

        # Writing all formulas that are listed in subset into self.__current:
        self._prepare_configuration(subset)

        # The specification is realizable if all initial states are
        # winning states:
        initial = self.__current[GR1Sect.SYS_INIT] * \
                  self.__current[GR1Sect.ENV_INIT]

        # Checking if the winning region contains the initial state ...
        # This method reads out self.__current:
        realizable = self._winm_contains(initial)

        msg = "checking with " + self.get_string_rep(subset)

        if realizable:
            self.__realizable_sets.append(set(subset))
            msg += "(%10.3f sec) -> realizable" % (time.clock() - starttime)
            self._log(msg, spaces)
            return True
        
        msg +="(%10.3f sec) -> unrealizable" % (time.clock() - starttime)
        self._log(msg, spaces)
        return False

    def _prepare_configuration(self, subset):
        """
        If the according section of the specification is minimized, this
        method:
         - adds all SYS_FAIRNESS-formulas that occur in subset to the
           list self.__current[GR1Sect.SYS_FAIR].
         - adds all ENV_FAIRNESS-formulas that occur in subset to the
           list self.__current[GR1Sect.ENV_FAIR].
         - builds a product bdd of all SYS_TRANSITIONS-formulas that occur in
           subset in self.__current[GR1Sect.SYS_TRANS]
         - builds a product bdd of all ENV_TRANSITIONS-formulas that occur in
           subset in self.__current[GR1Sect.ENV_TRANS]
         - builds a product bdd of all ENV_INITIAL-formulas that occur in
           subset in self.__current[GR1Sect.ENV_INIT]
         - builds a product bdd of all SYS_INITIAL-formulas that occur in
           subset in self.__current[GR1Sect.SYS_INIT]
        Variables that do not occur in subset are existentially quantified
        in the guarantees and forall-quantified in all assumptions.

        @param subset: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas.
        @type subset: list<int>
        """

        vars_to_remove = self._get_vars_to_remove(subset)

        # prepare ENV_INIT:
        self.__current[GR1Sect.ENV_INIT] = self.__utils.env_init

        # prepare ENV_FAIR:
        self.__current[GR1Sect.ENV_FAIR] = []
        for env_fair in self.__section_parts[GR1Sect.ENV_FAIR]:
            env_fair = env_fair.forall(vars_to_remove)
            self.__current[GR1Sect.ENV_FAIR].append(env_fair)

        # prepare ENV_TRANS:
        self.__current[GR1Sect.ENV_TRANS] = BDD.ONE(self.__utils.dd_mgr)
        for env_trans in self.__section_parts[GR1Sect.ENV_TRANS]:
            env_trans = env_trans.forall(vars_to_remove)
            self.__current[GR1Sect.ENV_TRANS] *= env_trans
    

        # prepare SYS_INIT, SYS_TRANS and SYS_FAIR:
        self.__current[GR1Sect.SYS_INIT] = BDD.ONE(self.__utils.dd_mgr)
        self.__current[GR1Sect.SYS_TRANS] = BDD.ONE(self.__utils.dd_mgr)
        self.__current[GR1Sect.SYS_FAIR] = []
        if not self.__minimize[GR1Sect.SYS_INIT]:
            sys_init = self.__utils.sys_init.exists(vars_to_remove)
            self.__current[GR1Sect.SYS_INIT] = sys_init
        if not self.__minimize[GR1Sect.SYS_FAIR]:
            for sys_fair in self.__section_parts[GR1Sect.SYS_FAIR]:
                sys_fair = sys_fair.exists(vars_to_remove)
                self.__current[GR1Sect.SYS_FAIR].append(sys_fair)
        if not self.__minimize[GR1Sect.SYS_TRANS]:
            for sys_trans in self.__section_parts[GR1Sect.SYS_TRANS]:
                sys_trans = sys_trans.exists(vars_to_remove)
                self.__current[GR1Sect.SYS_TRANS] *= sys_trans

        # this is the heart of this method:
        for index in subset:
            (formula_nr, section) = self._get_formula_nr_to_index(index)
            formula_bdd = self.__section_parts[section][formula_nr]

            if section == GR1Sect.SYS_TRANS:
                formula_bdd = formula_bdd.exists(vars_to_remove)
                self.__current[GR1Sect.SYS_TRANS] *= formula_bdd
            elif section == GR1Sect.SYS_FAIR:
                formula_bdd = formula_bdd.exists(vars_to_remove)
                self.__current[GR1Sect.SYS_FAIR].append(formula_bdd)
            elif section == GR1Sect.SYS_INIT:
                formula_bdd = formula_bdd.exists(vars_to_remove)
                self.__current[GR1Sect.SYS_INIT] *= formula_bdd
  

        # empty lists are not allowed for self.__current[GR1Sect.SYS_FAIR] and
        # self.__current[GR1Sect.ENV_FAIR]:
        mgr = self.__utils.dd_mgr
        if len(self.__current[GR1Sect.SYS_FAIR]) == 0:
            self.__current[GR1Sect.SYS_FAIR].append(BDD.ONE(mgr))
        if len(self.__current[GR1Sect.ENV_FAIR]) == 0:
            self.__current[GR1Sect.ENV_FAIR].append(BDD.ONE(mgr))


    def _winm_contains(self, states):
        """
        Checks if all the passed states are winning.
        
        This method checks if all the passed states are contained in the
        winning region of the system for a certain specification. It is
        basically equal to the method calcWinningRegion
        of the L{WinningRegion}. Only the intermediate results that are
        needed for the computation of the strategy are not computed. Also, the
        computation is aborted if it is clear from the intermediate results,
        that the set of states can not be contained.


        @param states: The set of states in question.
        @type states: L{BDD}
        @return: True if the winning region contains the states, False
                 otherwise.
        @rtype: bool
        """

        guarantees = self.__current[GR1Sect.SYS_FAIR]
        assumptions = self.__current[GR1Sect.ENV_FAIR]

        m = len(assumptions)
        n = len(guarantees)

        old_z = BDD.ZERO(self.__utils.dd_mgr)
        z = BDD.ONE(self.__utils.dd_mgr)
        while z != old_z: # GreatestFixpoint(z)
            old_z = z
            for j in range(0, n):
                old_y = BDD.ONE(self.__utils.dd_mgr)
                y = BDD.ZERO(self.__utils.dd_mgr)
                while y != old_y:  # LeastFixpoint(y)
                    old_y = y
                    start = (guarantees[j] * self._coax_fast(z)) + \
                            self._coax_fast(y)
                    y = BDD.ZERO(self.__utils.dd_mgr)
                    for i in range(0, m):
                        old_x = BDD.ZERO(self.__utils.dd_mgr)
                        x = z
                        while x != old_x: # GreatestFixpoint(x)
                            old_x = x
                            x = start + ((~assumptions[i]) \
                                * self._coax_fast(x))
                        y = y + x
                # End -- LeastFixpoint(y)
            z = y
            # z is in a greatest fixpoint, so z can only get smaller. If
            # some intermediate z does not contain the initial state, the
            # final z won't contain the initial state as well. So we can
            # abort.
            if not states <= z:
                return False
            # End -- For (j in 1...n)
        # End -- GreatestFixpoint(z)

        if states <= z:
            return True
        return False

    def _coax_fast(self, states):
        """
        Computes the mixed preimage of a set of states.

        This method calculates the states, from which the system can enforce
        to reach 'states' in one step. It is basically equal to the
        coax-method of the L{WinningRegion}. The difference is, that it works
        on the minimized specification in self.__current.

        @param states: The states where we want to know the mixed preimage.
        @type states: L{BDD}
        @return: All states, from which 'states' can be enforced by the
                 system in one step.
        @rtype: L{BDD}
        """
        env_transitions = self.__current[GR1Sect.ENV_TRANS]
        sys_transitions = self.__current[GR1Sect.SYS_TRANS]
        output_product = self.__utils.next_out_var_cube
        input_product = self.__utils.next_in_var_cube

        swapped_states = self.__utils.swap_present_next(states)
        sys_moves_to_target = swapped_states.andExists(sys_transitions, \
                                                       output_product)
        target_or_forbidden = sys_moves_to_target + (~env_transitions)
        mixed_preimage = target_or_forbidden.forall(input_product)
        return mixed_preimage


    def _get_vars_to_remove(self, subset):
        """
        Computes a cube of all variables that should be removed from a spec.

        This method computes a bdd where all bdd-variables that do not occur
        in the list subset are 1, and all other variables do not occur
        in the bdd (are irrelevant, are don't cares).

        @param subset: A list of integers. Each element is an index of a
               formula or a variable, so the list represents a set of
               formulas and variables.
        @type subset: list<int>
        @return: A bdd where all variables that do not occur in the list
                 'subset' are 1.
        @rtype: L{BDD}
        """

        vars_to_remove = BDD.ONE(self.__utils.dd_mgr)

        if self.__minimize[GR1Sect.OUT_VARS]:
            for i in range(0, len(self.__utils.output_vars)):
                index = self._get_index_to_formula_nr(i, GR1Sect.OUT_VARS)
                if subset.count(index) <= 0:
                    # present and next value of variable is set to 1:
                    vars_to_remove *= self.__utils.output_vars[i].ps
                    vars_to_remove *= self.__utils.output_vars[i].ns

        if self.__minimize[GR1Sect.IN_VARS]:
            for i in range(0, len(self.__utils.input_vars)):
                index = self._get_index_to_formula_nr(i, GR1Sect.IN_VARS)
                if subset.count(index) <= 0:
                    # present and next value of variable is set to 1:
                    vars_to_remove *= self.__utils.input_vars[i].ps
                    vars_to_remove *= self.__utils.input_vars[i].ns

        return vars_to_remove

    def _write_configuration(self, subset):
        """
        Writes the minimized specification into a file.

        This method writes the minimized specification into the file
        ./spec_debug_results/<filename>.xml. The original specification is
        first read with a DOM XML-Parser. All requirements that were thrown
        out by the minimizer are toggled. A comment is also added to the
        'notes'-tag of this requirement. If no target file name was set,
        nothing is done at all.

        @param subset: A list of indices of formulas. The list contains the
               index of every formula that was not thrown out by the minimizer.
        @type subset: list<int>
        """

        if not self.__target_file_name:
            return

        # A dictionary that contains the number of requirements we already
        # saw in the section:
        count = {}
        for section in GR1Sect.ALL:
            count[section] = 0

        # The original specification is read with a DOM parser:
        dom1 = parse(self.__utils.input_file)

        # Requirements:
        for req in dom1.getElementsByTagName("requirement"):
            toggled = req.getElementsByTagName("toggled")[0].firstChild
            name = req.getElementsByTagName("name")[0].firstChild
            section = GR1Sect.sect_from_alias(name.nodeValue)
            if toggled.nodeValue.count("0")>0 or not self.__minimize[section]:
                # if the requirement is already disabled or we did not
                # minimize the according section, we keep it untouched:
                continue
            notes = req.getElementsByTagName("notes")[0].firstChild
            index = self._get_index_to_formula_nr(count[section], section)

            # Otherwise we add its name to the 'notes' tag:
            notes.nodeValue += "  Name during minimization: "
            notes.nodeValue += self._get_formula_name(index) + "\n      "
            if subset.count(index) <= 0:
                # If it was thrown out by the minimizer, we disable it:
                toggled.nodeValue = toggled.nodeValue.replace("1", "0")
                # and add a comment:
                notes.nodeValue += "  TAKEN OUT BY SPEC-MINIMIZER\n      "
            count[section] += 1

        # Signals:
        for sig in dom1.getElementsByTagName("signal"):
            name = sig.getElementsByTagName("name")[0].firstChild
            name_string = name.nodeValue.lstrip().rstrip()

            # First we try to find out the section and the index of the signal:
            section = None
            index = None
            for i in range(0, len(self.__utils.input_vars)):
                if self.__utils.input_vars[i].name == name_string:
                    section = GR1Sect.IN_VARS
                    index = self._get_index_to_formula_nr(i, GR1Sect.IN_VARS)
            for i in range(0, len(self.__utils.output_vars)):
                if self.__utils.output_vars[i].name == name_string:
                    section = GR1Sect.OUT_VARS
                    index = self._get_index_to_formula_nr(i, GR1Sect.OUT_VARS)
            if not self.__minimize[section]:
                # if we did not minimize the according section, we keep the
                # signal untouched:
                continue
            notes = sig.getElementsByTagName("notes")[0].firstChild
            notes.nodeValue += "  Name during minimization: "
            notes.nodeValue += self._get_formula_name(index) + "\n      "
            if subset.count(index) <= 0:
                # If it was thrown out by the minimizer, we mention that:
                notes.nodeValue += "  TAKEN OUT BY SPEC-MINIMIZER\n      "

        # Finally we write the modified specification:
        cfg_file = open(self.__target_file_name, 'w')
        dom1.writexml(cfg_file)
        cfg_file.close()

    def _get_formula_name(self, index):
        """
        Returns a unique name to a formula.

        @param index: The global index of the formula where we want to have
               a name for.
        @type index: int
        @return: A unique name of the formula.
        @rtype: string
        """
        (formula_nr, section) = self._get_formula_nr_to_index(index)
        if section == GR1Sect.IN_VARS:
            return "iv:" + self.__utils.input_vars[formula_nr].name
        elif section == GR1Sect.ENV_INIT:
            return "ei" + str(formula_nr)
        elif section == GR1Sect.ENV_TRANS:
            return "et" + str(formula_nr)
        elif section == GR1Sect.ENV_FAIR:
            return "ef" + str(formula_nr)
        elif section == GR1Sect.OUT_VARS:
            return "iv:" + self.__utils.output_vars[formula_nr].name
        elif section == GR1Sect.SYS_INIT:
            return "si" + str(formula_nr)
        elif section == GR1Sect.SYS_TRANS:
            return "st" + str(formula_nr)
        elif section == GR1Sect.SYS_FAIR:
            return "sf" + str(formula_nr)


    def _get_index_to_formula_nr(self, formula_nr, section):
        """
        Returns the global index of a formula.

        This method returns the global index of a certain formula of a
        certain section. This is the reverse method to the method
        _get_formula_nr_to_index.

        @param formula_nr: The local index of the formula in its section.
        @type formula_nr: int
        @param section: The section where the formula is located.
        @type section: string
        @return: The unique global index of the formula.
        @rtype: int
        """
        index = formula_nr
        for current_section in GR1Sect.ALL:
            if section ==  current_section:
                return index
            index += self.__size[current_section]

        exit(0)

    def _get_formula_nr_to_index(self, index):
        """
        Returns the section and the local index in this sections to a formula.

        This method returns the section and the local index of the formula in
        this section for a formula with a certain global index. This is the
        reverse method to the method _get_index_to_formula_nr.

        @param index: The global index of the formula.
        @type index: int
        @return: A tuple (formula_nr, section) where:
                  - formula_nr is the local index of the formula in its
                    section.
                  - section is the section where the formula is located.
        @rtype: (int, string)
        """
        start = 0
        end = 0
        for section in GR1Sect.ALL:
            start = end;
            end += self.__size[section]
            if index < end:
                return (index - start, section)
        exit(0)

    def _superset_already_realizable(self, subset):
        """
        Checks if a superset of formulas is already realizable.
        
        This method checks if a superset of subset already lead to a
        realizable specification.

        @param subset: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas.
        @type subset: list<int>
        @return: True if a superset of subset is known that is realizable,
                 False otherwise
        @rtype: bool
        """
        for realizable_set in self.__realizable_sets:
            if realizable_set >= set(subset):
                return True
        return False

    def _get_relevant_out_vars(self, result):
        """
        Returns all output vars, that are relevant for unrealizability.

        This method returns a list that contains all output variables that
        are relevant for the conflict causing the specification to be
        unrealizable.

        @param result: A list containing the indices of all formulas and
               output variables that were not thrown away by the minimization
               algorithm.
        @param result: list<int>
        @return: A list containing all relevant output variables.
        @rtype: list<L{Variable}>
        """
        relevant = []

        # if we did not minimize output variables, every output
        # variable is relevant.
        if not self.__minimize[GR1Sect.OUT_VARS]:
            return self.__utils.output_vars


        # for all output variables ...
        for i in range(0, len(self.__utils.output_vars)):
            index = self._get_index_to_formula_nr(i, GR1Sect.OUT_VARS)
            if result.count(index) > 0:
                # the output variable was not thrown away by the minimizer:
                relevant.append(self.__utils.output_vars[i])

        return relevant

    def _log_statistics(self, solution):
        """
        Logs some statistics.

        This method writes some performance measures into the log file. The
        information is also printed to STDOUT.

        @param solution: A list of integers. Each element is an index of a
               formula, so the list represents a set of formulas. The list
               is the result of the minimization.
        @type solution: list<int>
        """

        msg = " Some statistics:\n"

        # computing the new sizes of the sections:
        reduced_size = {}
        for section in GR1Sect.ALL:
            reduced_size[section] = 0
        for index in solution:
            (formula_nr, section) = self._get_formula_nr_to_index(index)
            reduced_size[section] += 1

        # logging the size reductions:
        sum = 0
        sum_reduced = 0
        for section in GR1Sect.ALL:
            if self.__minimize[section]:
                sum += self.__size[section]
                sum_reduced += reduced_size[section]
                msg += "  " + section + ": " + str(self.__size[section])
                msg += " formulas --reduced to--> "
                msg += str(reduced_size[section]) + " formulas\n"


        msg += "  All in all: " + str(sum) + " formulas --reduced to--> "
        msg += str(sum_reduced) + " formulas\n"

        msg += "  "+ str(self.__realizability_checks)
        msg += " checks for realizability had to be done\n"
        msg += "  " + str(self.__checks_covered_by_supersets)
        msg += " checks could be omitted, because a superset was "
        msg += "already realizable\n  -> only "
        msg += str(self.__realizability_checks - self.__checks_covered_by_supersets)
        msg += "  checks were actually carried out\n"

        self._log(msg)
        PLog.log(msg)


class SpecSplitterHack(object):
    """
    Computes BDDs for each formula in the sections ENV_INIT, SYS_INIT,
    ENV_TRANS, and SYS_TRANS.

    For the sections ENV_INIT, SYS_INIT, ENV_TRANS, and SYS_TRANS, we
    have to get bdds, each representing a certain formula in this
    section. This is done with this class. It is more of a hack than a
    solution to get this information out of nusmv, hence the name of the
    class ;-). Maybe this will be fixed in the future.
    """
    def __init__(self, utils):
        """
        Constructor.

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: The BDD encoding in nusmv.
        self.__encoding = enc.Enc_get_bdd_encoding()

        #: A list of bdds representing the formulas in SYS_INIT:
        self.sys_init_bdds = []

        #: A list of bdds representing the formulas in ENV_INIT:
        self.env_init_bdds = []

        #: A list of bdds representing the formulas in SYS_TRANS:
        self.sys_trans_bdds = []

        #: A list of bdds representing the formulas in ENV_TRANS:
        self.env_trans_bdds = []

        self._read_spec_parts()


    def _read_spec_parts(self):
        """
        Computes BDDs for each formula in the sections ENV_INIT, SYS_INIT,
        ENV_TRANS, and SYS_TRANS.
        """

        # Writing the specification into a file:
        tmp_file_name = "./tmp_min"
        tmp_file = open(tmp_file_name, 'w')
        game.CommandWriteFlatModel(tmp_file)
        tmp_file.flush()

        # For some reason flushing does not work proper, so we have to reopen
        # the file:
        tmp_file.close()
        tmp_file = open(tmp_file_name, 'r')

        # we read the file into a list of strings, each containing a line:
        lines = tmp_file.readlines()
        tmp_file.close()

        player = 1
        for i in range(0,len(lines)):
            line = lines[i]
            if line == "PLAYER_1":
                player = 1
            if line == "PLAYER_2\n":
                player = 2
            if line != "INIT\n" and line != "TRANS\n":
                continue

            # If we have a line 'INIT' or 'INIT' we transform the next line
            # into a bdd and store it:
            bdd = self._evaluate_expr(lines[i+1])
            if line == "INIT\n" and player == 1:
                self.env_init_bdds.append(bdd)
            elif line == "INIT\n" and player == 2:
                self.sys_init_bdds.append(bdd)
            elif line == "TRANS\n" and player == 1:
                self.env_trans_bdds.append(bdd)
            elif line == "TRANS\n" and player == 2:
                self.sys_trans_bdds.append(bdd)

        # removing the file again:
        os.remove(tmp_file_name)


    def _evaluate_expr(self, expr):
        """
        Transforms an LTL expression into a BDD.
    
        @param expr: An LTL expression.
        @type expr: string
        @return: A bdd representing the LTL formula.
        @rtype: L{BDD}
        """

        # operator precedence for next operator is not handled correctly, so
        # we add brackets (yes, this is a hack):
        expr = re.sub('(next\([^\)]*\))', r'(\1)', expr)

        # we parse the expression:
        r,n = parser.read_psl_from_string([expr])
        if r: raise ValueError("Formula '" + expr + "' is not valid")

        # in the result, the 'next' operator has a wrong type, so we have to
        # change this type manually (yes, this is a hack):
        self._hack_next(n)

        # finally we transform the parsed expression into a bdd:
        bdd_formula = enc.bdd.expr_to_bdd(self.__encoding, n, node.Nil)
        bdd = BDD(bdd_formula, BDD.dd_mgr)
        dd.bdd_free(BDD.dd_mgr, bdd_formula)
        bdd = bdd.transfer(self.__utils.dd_mgr)
        return bdd

    def _hack_next(self, n):
        """
        Changes the type of all occurances of the 'next' operator, as it is
        not handled correctly.

        @param n: A node as returned by read_psl_from_string
        @type n: node
        """

        # Whenever the method parser.read_psl_from_string processes a 'next'
        # operator, it produces a node with type 1036. enc.bdd.expr_to_bdd
        # only understands parser.symbols.NEXT = 216. Thus we manually change
        # it (bad hack):
        if n.type == 1036 or n.type == 1047:
            n.type = parser.symbols.NEXT

        # We have to change the type in the successor nodes as well. The
        # problem is, that there is no way to find out, how many successor
        # nodes exist. node.cdr() or node.cdr() do not return None in case of
        # no successor nodes (as they should), they return an invalid pointer
        # that causes segmentation faults in nusmv if there are no more
        # successor nodes. Hence, we have to find out the number of successor
        # nodes by hand:
        nr_succ = self._get_nr_successor_nodes(n.type)
        if nr_succ >= 2:
            self._hack_next(node.cdr(n))
        if nr_succ >= 1:
            self._hack_next(node.car(n))


    def _get_nr_successor_nodes(self, node_type):
        """
        Returns the number of child nodes for a node with a given type.

        @param node_type: The type of the node.
        @type node_type: int
        @return: The number of child nodes (0, 1, or 2).
        @rtype: int
        """
        if node_type == parser.symbols.CONTEXT or \
           node_type == parser.symbols.CONS or \
           node_type == parser.symbols.AND or \
           node_type == parser.symbols.OR or \
           node_type == parser.symbols.IMPLIES or \
           node_type == parser.symbols.IFF or \
           node_type == parser.symbols.XOR or \
           node_type == parser.symbols.XNOR or \
           node_type == parser.symbols.EQUAL or \
           node_type == parser.symbols.NOTEQUAL or \
           node_type == parser.symbols.LT or \
           node_type == parser.symbols.GT or \
           node_type == parser.symbols.LE or \
           node_type == parser.symbols.GE or \
           node_type == parser.symbols.PLUS or \
           node_type == parser.symbols.MINUS or \
           node_type == parser.symbols.TIMES or \
           node_type == parser.symbols.DIVIDE or \
           node_type == parser.symbols.MOD or \
           node_type == parser.symbols.LSHIFT or \
           node_type == parser.symbols.RSHIFT or \
           node_type == parser.symbols.LROTATE or \
           node_type == parser.symbols.CONCATENATION or \
           node_type == parser.symbols.BIT_SELECTION or \
           node_type == parser.symbols.COLON or \
           node_type == parser.symbols.UNION or \
           node_type == parser.symbols.SETIN or \
           node_type == parser.symbols.TWODOTS:
            return 2
        elif node_type == parser.symbols.NOT or \
             node_type == parser.symbols.UMINUS or \
             node_type == parser.symbols.NEXT or \
             node_type == parser.symbols.CAST_BOOL or \
             node_type == parser.symbols.CAST_WORD1 or \
             node_type == parser.symbols.CAST_SIGNED or \
             node_type == parser.symbols.CAST_UNSIGNED or \
             node_type == parser.symbols.EXTEND:
            return 1
        else:
            return 0





