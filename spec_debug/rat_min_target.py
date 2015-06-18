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
Contains classes that define a minimization target for RATSY specs.
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
        self._log_file = None

    def set_log_file(self, log_file):
        """
        Sets a log file.

        This method remembers the passed log file in order to use it for
        logging information. The passed log file must be opened for writing.
        """
        self._log_file = log_file

    def _log(self, msg, nr_spaces = 0):
        """
        Logs a message.

        This method adds a message to the log file self._log_file.
        The message is indented by nr_spaces spaces. If no log file was set,
        this method does nothing at all.

        @param msg: The message to log.
        @type msg: string
        @param nr_spaces: The number of spaces to put in front of the message.
        @type nr_spaces: int
        """
        if not self._log_file:
            #print (" " * nr_spaces) + msg
            return
        self._log_file.write(" " * nr_spaces)
        self._log_file.write(msg)
        self._log_file.write("\n")

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

    def test_over_approx(self, subset, spaces):
        """
        An overapproximation of the function test.

        This method has to implement an overapproximation of the functions
        test. Overapproximation means: if test returns true for some subset,
        this method has to return true as well. If test returns false for
        some subset, this method can return whatever it likes.
        If the method is not overridden in the derived class, it simply returns
        true (as the most coarse overapproximation) all the time.

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

        return True

    def test_under_approx(self, subset, spaces):
        """
        An overapproximation of the function test.

        This method has to implement an underapproximation of the functions
        test. Underapproximation means: if test returns false for some subset,
        this method has to return false as well. If test returns true for
        some subset, this method can return whatever it likes.
        If the method is not overridden in the derived class, it simply returns
        false (as the most coarse overapproximation) all the time.

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

        return False

    def test_approx_first(self, subset, spaces):
        """
        The function 'test' where approximations are tried first.

        This method is functional equivalent to the function 'test'. The only
        difference is that several underapproximations and overapproximations
        are tried first. Only if none of the approximations give a verdict,
        the original testing procedure is applied. There is the hope that
        this function is faster than the original function 'test', at least
        for complex specifications. If not overridden, this function simply
        calls 'test'.

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

        return self.test(subset, spaces)

    def test_approx_first_slim(self, subset, spaces):
        """
        Like test_approx_first, only with fewer approximations.

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

        return self.test_approx_first(subset, spaces)

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

    def get_min_statistics(self, solution):
        """
        Returns some statistics about the whole minimization process.

        This method returns some performance measures about the whole
        minimization process as string. If not overwritten, this method returns
        the empty string.

        @param solution: The final solution of the minimization. It has to
               contain a subset of the elements returned by
               get_elements_to_minimize.
        @type solution: list<some type>
        @return: Some statistics about the whole minimization process. If not
                 overwritten, the empty string is returned.
        @rtype: string
        """

        return ""

    def get_reduction_statistics(self, solution):
        """
        Returns some statistics about the amount of reduction.

        This method returns some statistics about the amount of reduction as
        string. If not overwritten, this method returns the empty string.

        @param solution: The final solution of the minimization. It has to
               contain a subset of the elements returned by
               get_elements_to_minimize.
        @type solution: list<some type>
        @return: Some statistics about the amount of reduction. If
                 not overwritten, the empty string is returned.
        @rtype: string
        """

        return ""

    def get_check_statistics(self):
        """
        Returns some statistics about the number of realizability checks.

        This method returns some performance measures about the number of
        realizability checks as string. If not overwritten, this method returns
        the empty string.

        @return: Some statistics about the number of realizability checks. If
                 not overwritten, the empty string is returned.
        @rtype: string
        """

        return ""

class RatMinTarget(MinTarget):
    """
    A minimization target that represents a RAT specification.

    This class represents a RAT specification that is minimized. We aim at
    finding a smaller specification that is still unrealizable. Hence the
    method test() checks for realizability.

    The idea is then to find the problem in the (simpler) specification
    much faster, because all formulas that are irrelevant for unrealizability
    have been removed. Only the statements really causing the problem remain.

    Only guarantees of the system (SYS_INITIAL, SYS_TRANSITIONS and
    SYS_FAIRNESS) can be minimized. Assumptions are not minimized since leaving
    them out will always lead to a specification with is not realizable (even
    worse than before). Output variables which are not involved in the conflict
    that makes the specification unrealizable can be removed as well by
    existential quantification in the guarantees. Minimization is done on the
    granularity of RAT-requirements..

    The file <target_file_name>.xml is created. It contains the minimal
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
               Currently, only the sections GR1Sect.OUT_VARS, GR1Sect.SYS_INIT,
               GR1Sect.SYS_TRANS and GR1Sect.SYS_FAIR can be minimized. All
               other sections are ignored.
        @type minimize: dictionary<string, bool>
        @param use_result: True if the result of the minimization should be
               stored in self._utils, False otherwise.
        @type use_result: bool
        @param target_file_name: The name of the file for the minimized
               specification or None if it should not be written.
        @type target_file_name: string
        """

        MinTarget.__init__(self)

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self._utils = utils

        #: A dictionary that tells us, which sections should be minimized.
        #:
        #: A dictionary that maps constants for sections as
        #: defined in L{GR1Sect} to True if the section should be minimized
        #: and to False if the section should not be minimized. Sections
        #: that do not occur in this dictionary are not minimized.
        #: Currently, only the sections GR1Sect.OUT_VARS, GR1Sect.SYS_INIT,
        #: GR1Sect.SYS_TRANS and GR1Sect.SYS_FAIR can be minimized. All
        #: other sections are ignored.
        #: @type: dictionary<string, bool>
        self._minimize = minimize

        # If a section does not occur in self._minimize, we do not minimize
        # it. To avoid key errors, we map missing sections to 0.
        for section in GR1Sect.ALL:
            if not section in self._minimize.keys():
                self._minimize[section] = False

        #: True if the result of the minimization should be stored in
        #: self._utils, False otherwise.
        #: @type: bool
        self._use_result = use_result

        #: The name of the file for the minimized specification.
        #: @type: string
        self._target_file_name = target_file_name

        #: The current specification to check for realizability.
        #:
        #: A dictionary that maps all constants for sections as defined in
        #: L{GR1Sect} to bdds representing this section.
        #: @type: dictionary<string, L{BDD}>
        self._current = {}

        #: A counter, counting the realizability checks.
        #: @type: int
        self._realizability_checks = 0

        #: Nr of realizability checks skipped because superset is realizable.
        #:
        #: A counter, counting the number of realizability checks that do
        #: not really have to be performed as a superset of restrictions
        #: of the system is already realizable.
        #: @type: int
        self._checks_covered_by_supersets = 0

        #: Nr of realizability checks skipped because subset is unrealizable.
        #:
        #: A counter, counting the number of realizability checks that do
        #: not really have to be performed as a subset of restrictions
        #: of the system is already unrealizable.
        #: @type: int
        self._checks_covered_by_subsets = 0

        #: A list of all specifications that are realizable.
        #:
        #: A list of all specifications that are realizable. All subsets of
        #: a realizable specification are again realizable. This can be
        #: used to reduce the number of realizability checks.
        #: @type: list<set<int>>
        self._realizable_sets = []

        #: A list of all specifications that are unrealizable.
        #:
        #: A list of all specifications that are unrealizable. All supersets of
        #: an unrealizable specification are again unrealizable. This can be
        #: used to reduce the number of realizability checks.
        #: @type: list<set<int>>
        self._unrealizable_sets = []

        # In order to be able to remove parts of the specification, we fist
        # need to split it into its requirements:
        splitter = SpecSplitter(self._utils)

        #: All requirements that occur in the specification.
        #: @type: list<RatRequirement>
        self._all_reqs = splitter.get_requirements()

        #: All guarantees which are not minimized.
        #:
        #: These guarantees are not minimized because the user does not want
        #: them to be minimized.
        #: @type: list<RatRequirement>
        self._fixed_guarantees = []

        # A list of indices of guarantees or outputs that should be minimized.
        #: @type: list<int>
        self._indices_of_things_to_minimize = []

        #: All names of requirements that were not thrown away.
        #: @type: list<string>
        self._remaining_req_names = []

        #: All outputs that were not thrown away.
        #: @type: list<L{Variable}>
        self._remaining_outputs = []

        # In this implementation of a minimization target, the assumptions
        # are not touched. Hence, we can put them into self._current[]. They
        # won't change during the whole minimization algorithm.
        all_assumptions = RatRequirement(self._utils)
        all_assumptions.kind = RatRequirement.ASSUMPTION
        for req in self._all_reqs:
            if req.kind == RatRequirement.ASSUMPTION:
                all_assumptions *= req
                # we do not need the sole assumptions any more:
                # (deleting bdds often improves the performance)
                req.destroy_bdds()
        self._current[GR1Sect.ENV_INIT] = all_assumptions.init_bdd
        self._current[GR1Sect.ENV_FAIR] = all_assumptions.fair_bdds
        self._current[GR1Sect.ENV_TRANS] = all_assumptions.trans_bdd

        # computes self._indices_of_things_to_minimize and
        # self._fixed_guarantees:
        self._compute_indices_of_things_to_minimize()


    def get_elements_to_minimize(self):
        """
        Returns a list of elements that should be minimized by a minimizer.

        This method returns a list of indices of guarantees and outputs. This
        list contains the index of every guarantee or output that should be
        minimized.

        @return: A list of indices of guarantees or outputs that should be
                 minimized.
        @rtype: list<int>
        """
        return self._indices_of_things_to_minimize[:]

    def test(self, subset, spaces):
        """
        Checks for realizability.

        This method checks if a certain specification represented by the
        indices of the guarantees or outputs that are in the specification,
        is realizable. It does this by checking if the initial state is in the
        winning region with the method winm_contains_initial. In order to 
        minimize the number of calls to the function winm_contains, we first 
        check if a superset of restrictions of the system is already realizable. 
        If this is the case, the specification to be checked will be realizable 
        as well. This property speeds things up.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
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
        Returns the string representation of a list of guarantees/outputs.

        This method takes a list of indices of guarantees/outputs and
        produces a nice to read string containing the names.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @return: A string containing the names of all elements.
        @rtype: string
        """

        result_string = "";
        for elem in subset:
            result_string += self._get_element_name(elem) + ","

        #get rid of the last ',':
        result_string = result_string[0:-1]
        return "{" + result_string + "}"

    def set_final_solution(self, result):
        """
        Stores the final minimization result in self._utils if desired.

        This method is used by the minimizer to inform about the final
        solution of the minimization. If self._use_result is True, the
        resulting specification is written into self._utils. All further
        debugging operations read the specification form there, so all further
        debugging operations use the minimized specification. If self._utils
        is False, the minimized specification is not stored.
        Some performance measures are logged and the minimized specification
        is written to self._target_file_name.

        @param result:A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
               It is the minimal set of guarantees/outputs so that the
               specification is unrealizable.
        @type result: list<int>
        """

        # Compute all requirements and outputs that were not thrown away:
        self._compute_remaining(result)

        # writing the result into the file self._target_file_name
        self._write_configuration()

        # Writing all formulas that are listed in result into self._current:
        self._prepare_configuration(result)

        # If the result of the minimization algorithm should be used, we
        # copy the final result from self._current into self._utils. The
        # bdds for all further debugging operations are read from there.
        if self._use_result:
            self._utils.guarantees = self._current[GR1Sect.SYS_FAIR]
            self._utils.assumptions = self._current[GR1Sect.ENV_FAIR]
            self._utils.sys_trans = self._current[GR1Sect.SYS_TRANS]
            self._utils.env_trans = self._current[GR1Sect.ENV_TRANS]
            self._utils.sys_init = self._current[GR1Sect.SYS_INIT]
            self._utils.env_init = self._current[GR1Sect.ENV_INIT]
            self._utils.relevant_out_vars = self._remaining_outputs


    def get_remaining_requirement_names(self):
        """
        Returns the names of all requirements that were not thrown away.

        @return: The names of all requirements that were not thrown away.
        @rtype: list<string>
        """
        return self._remaining_req_names

    def get_min_statistics(self, solution):
        """
        Returns some statistics about the whole minimization process.

        This method returns some performance measures about the whole
        minimization process as string.

        @param solution: A list containing the indices of all guarantees and
               output variables that were not thrown away by the minimization
               algorithm.
        @type solution: list<int>
        @return: Some statistics about the whole minimization process.
        @rtype: string
        """

        msg = self.get_reduction_statistics(solution)
        return msg + self.get_check_statistics()


    def get_reduction_statistics(self, solution):
        """
        Returns some statistics about the amount of reduction.

        This method returns some statistics about the amount of reduction as
        string.

        @param solution: A list containing the indices of all guarantees and
               output variables that were not thrown away by the minimization
               algorithm.
        @type solution: list<int>
        @return: Some statistics about the amount of reduction.
        @rtype: string
        """

        # compute original size:
        size_guarantees = 0
        for elem in self._indices_of_things_to_minimize:
            if elem < len(self._all_reqs):
                size_guarantees += 1

        # compute reduced size:
        reduced_size_guarantees = 0
        reduced_size_outputs = 0
        for index in solution:
            if index < len(self._all_reqs):
                reduced_size_guarantees += 1
            else:
                reduced_size_outputs += 1

        # the size reductions:
        msg = "  guarantees: %d" % size_guarantees
        msg += " formulas --reduced to--> "
        msg += "%d formulas\n" % reduced_size_guarantees
        if self._minimize[GR1Sect.OUT_VARS]:
            msg += "  outputs: %d" % len(self._utils.output_vars)
            msg += " formulas --reduced to--> "
            msg += "%d formulas\n" % reduced_size_outputs
            sum = len(self._utils.output_vars) + size_guarantees
            sum_reduced = reduced_size_outputs + reduced_size_guarantees
            msg += "  All in all: %d formulas --reduced to--> " % sum
            msg += "%d formulas\n" % sum_reduced
        return msg


    def get_check_statistics(self):
        """
        Returns some statistics about the number of realizability checks.

        This method returns some performance measures about the number of
        realizability checks as string.

        @return: Some statistics about the number of realizability checks.
        @rtype: string
        """

        msg = "  %d" % self._realizability_checks
        msg += " checks for realizability had to be done\n"
        msg += "  %d" % self._checks_covered_by_supersets
        msg += " checks could be omitted, because a superset was "
        msg += "already realizable\n"
        msg += "  %d" % self._checks_covered_by_subsets
        msg += " checks could be omitted, because a subset was "
        msg += "already unrealizable\n  -> only "
        done = self._realizability_checks
        done -= self._checks_covered_by_supersets
        done -= self._checks_covered_by_subsets
        msg += "%d checks were actually carried out\n" % done
        return msg

    def _compute_indices_of_things_to_minimize(self):
        """
        Computes a list of elements that should be minimized by a minimizer.

        This method computes a list of indices of guarantees and outputs. This
        list contains the index of every guarantee or output that should be
        minimized. It is stored in self._indices_of_things_to_minimize.
        A list of guarantees that has to be added for every check is written
        to self._fixed_guarantees.
        """
        indices = []
        self._fixed_guarantees = []

        # examine all guarantees if they should be minimized:
        for req_nr in range(0, len(self._all_reqs)):
            req = self._all_reqs[req_nr]
            if req.kind == RatRequirement.ASSUMPTION:
                continue
            # a guarantee is minimized if it contains at least some part that
            # should be minimized:
            if (req.has_init() and self._minimize[GR1Sect.SYS_INIT]) or \
               (req.has_trans() and self._minimize[GR1Sect.SYS_TRANS]) or \
               (req.has_fair() and self._minimize[GR1Sect.SYS_FAIR]):
                indices.append(req_nr)
            else:
                self._fixed_guarantees.append(req)

        # if the outputs should be minimized:
        if self._minimize[GR1Sect.OUT_VARS]:
            for var_nr in range(0, len(self._utils.output_vars)):
                indices.append(var_nr + len(self._all_reqs))

        self._indices_of_things_to_minimize = indices

    def _is_realizable(self, subset, spaces, winm_contains_function = None):
        """
        Checks for realizability.

        This method checks if a certain specification represented by the
        indices of the guarantees or outputs that are in the specification,
        is realizable. It does this by checking if the initial state is in the
        winning region with the method winm_contains_initial. In order to 
        minimize the number of calls to the function winm_contains_initial, we 
        first check if a superset of restrictions of the system is already 
        realizable. If this is the case, the specification to be checked will 
        be realizable as well. This property speeds things up.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: True if the specification is realizable, False otherwise
        @rtype: bool
        """

        starttime = time.clock()
        self._realizability_checks += 1

        if self._superset_already_realizable(subset):
            self._checks_covered_by_supersets += 1
            msg = "checking with " + self.get_string_rep(subset)
            msg += " (superset already realizable)"
            msg += " (%10.3f sec)" % (time.clock() - starttime)
            msg += " -> realizable"
            self._log(msg, spaces)
            return True

        if self._subset_already_unrealizable(subset):
            self._checks_covered_by_subsets += 1
            msg = "checking with " + self.get_string_rep(subset)
            msg += " (subset already unrealizable)"
            msg += " (%10.3f sec)" % (time.clock() - starttime)
            msg += " -> unrealizable"
            self._log(msg, spaces)
            return False

        # Writing all formulas that are listed in subset into self._current:
        self._prepare_configuration(subset)

        # Checking if the winning region contains the initial state ...
        # This method reads out self._current:
        realizable = None
        if winm_contains_function == None:
            realizable = self._winm_contains_initial()
        else:
            realizable = winm_contains_function()

        msg = "checking with " + self.get_string_rep(subset)
        if realizable:
            self._realizable_sets.append(set(subset))
            msg += "(%10.3f sec) -> realizable" % (time.clock() - starttime)
            self._log(msg, spaces)
            return True

        self._unrealizable_sets.append(set(subset))
        msg +="(%10.3f sec) -> unrealizable" % (time.clock() - starttime)
        self._log(msg, spaces)
        return False

    def _prepare_configuration(self, subset):
        """
        Writes a specification into self._current.

        Assumptions are not minimized. Hence they were already written to
        self._current. They remain the same for the whole algorithm. The
        guarantees change. The guarantees in self._fixed_guarantees need to
        be added in any case. All other guarantees are only added if they are
        part of subset. All variables which are not part of subset are removed
        from all guarantees (seperatly, not from the conjunction) if variables
        should be minimized.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        """

        vars_to_remove = self._get_vars_to_remove(subset)

        all_guarantees = RatRequirement(self._utils)
        all_guarantees.kind = RatRequirement.GUARANTEE

        for fixed in self._fixed_guarantees:
            all_guarantees *= fixed.copy().remove_vars(vars_to_remove)

        for index in subset:
            if index < len(self._all_reqs):
                req = self._all_reqs[index].copy().remove_vars(vars_to_remove)
                all_guarantees *= req

        self._current[GR1Sect.SYS_INIT] = all_guarantees.init_bdd
        self._current[GR1Sect.SYS_FAIR] = all_guarantees.fair_bdds
        self._current[GR1Sect.SYS_TRANS] = all_guarantees.trans_bdd

        # empty lists are not allowed for self._current[GR1Sect.SYS_FAIR] and
        # self._current[GR1Sect.ENV_FAIR]:
        mgr = self._utils.dd_mgr
        if len(self._current[GR1Sect.SYS_FAIR]) == 0:
            self._current[GR1Sect.SYS_FAIR].append(BDD.ONE(mgr))
        if len(self._current[GR1Sect.ENV_FAIR]) == 0:
            self._current[GR1Sect.ENV_FAIR].append(BDD.ONE(mgr))


    def _winm_contains_initial(self):
        """
        Checks if the initial states are winning.

        This method checks if the initial states are contained in the
        winning region of the system for a certain specification. It is
        basically equal to the method calcWinningRegion
        of the L{WinningRegion}. Only the intermediate results that are
        needed for the computation of the strategy are not computed. Also, the
        computation is aborted if it is clear from the intermediate results,
        that the set of initial states can not be contained.

        @return: True if the winning region contains the initial states, False
                 otherwise.
        @rtype: bool
        """

        if self._current[GR1Sect.ENV_INIT].isZero() or \
           self._current[GR1Sect.SYS_INIT].isZero():
            return self._can_win_system(BDD.ZERO(self._utils.dd_mgr))

        guarantees = self._current[GR1Sect.SYS_FAIR]
        assumptions = self._current[GR1Sect.ENV_FAIR]

        m = len(assumptions)
        n = len(guarantees)

        old_z = BDD.ZERO(self._utils.dd_mgr)
        z = BDD.ONE(self._utils.dd_mgr)
        while z != old_z: # GreatestFixpoint(z)
            old_z = z
            for j in range(0, n):
                old_y = BDD.ONE(self._utils.dd_mgr)
                y = BDD.ZERO(self._utils.dd_mgr)
                while y != old_y:  # LeastFixpoint(y)
                    old_y = y
                    start = (guarantees[j] * self._coax_fast(z)) + \
                            self._coax_fast(y)
                    y = BDD.ZERO(self._utils.dd_mgr)
                    for i in range(0, m):
                        old_x = BDD.ZERO(self._utils.dd_mgr)
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
                if not self._can_win_system(z):
                    return False
            # End -- For (j in 1...n)
        # End -- GreatestFixpoint(z)

        if self._can_win_system(z):
            return True
        return False

    def _coax_fast(self, states):
        """
        Computes the mixed preimage of a set of states.

        This method calculates the states, from which the system can enforce
        to reach 'states' in one step. It is basically equal to the
        coax-method of the L{WinningRegion}. The difference is, that it works
        on the minimized specification in self._current.

        @param states: The states where we want to know the mixed preimage.
        @type states: L{BDD}
        @return: All states, from which 'states' can be enforced by the
                 system in one step.
        @rtype: L{BDD}
        """

        env_transitions = self._current[GR1Sect.ENV_TRANS]
        sys_transitions = self._current[GR1Sect.SYS_TRANS]
        output_product = self._utils.next_out_var_cube
        input_product = self._utils.next_in_var_cube

        swapped_states = self._utils.swap_present_next(states)
        sys_moves_to_target = swapped_states.andExists(sys_transitions, \
                                                       output_product)
        target_or_forbidden = sys_moves_to_target + (~env_transitions)
        mixed_preimage = target_or_forbidden.forall(input_product)
        return mixed_preimage


    def _can_win_system(self, winning_region_system):
        """
        Checks if the system can win a game.
        
        This method checks if the system can win the game. It does so by 
        checking if for all initial configurations of the inputs there
        exists an initial configuration of the outputs such that the
        thereby formed initial state is contained in the winning region.
        
        @param winning_region_system: The winning region of the system.
        @type winning_region_system: L{BDD}
        @return True if for all initial configurations of the inputs there
                exists an initial configuration of the outputs such that the
                thereby formed initial state is contained in the winning 
                region of the system, False otherwise.
        """

        out_product = self._utils.present_out_var_cube
        in_product = self._utils.present_in_var_cube
        env_init = self._current[GR1Sect.ENV_INIT]
        sys_init = self._current[GR1Sect.SYS_INIT]

        win_and_sys_initial = winning_region_system * sys_init
        can_find_initial_output = win_and_sys_initial.exists(out_product)
        return ((~env_init) + can_find_initial_output).isOne()


    def _can_win_environment(self, winning_region_environment):
        """
        Checks if the environment can win a game.
        
        This method checks if the environment can win the game. It does so by 
        checking if there exists an initial configuration of the inputs 
        such that forall initial configurations of the outputs the
        thereby formed initial state is contained in the winning region of the
        environment.
        
        @param winning_region_environment: The winning region of the 
               environment.
        @type winning_region_environment: L{BDD}
        @return True if there exists an initial configuration of the inputs 
                such that forall initial configurations of the outputs the
                thereby formed initial state is contained in the winning region 
                of the environment.
        """

        return not self._can_win_system(~winning_region_environment)

    def _get_vars_to_remove(self, subset):
        """
        Computes a cube of all variables that should be removed from a spec.

        This method computes a bdd where all bdd-variables that do not occur
        in the list subset are 1, and all other variables do not occur
        in the bdd (are irrelevant, are don't cares).

        @param subset: A list of integers. Each element is an index of a
               guarantee or an output, so the list represents a set of
               guarantees and outputs.
        @type subset: list<int>
        @return: A bdd where all variables that do not occur in the list
                 'subset' are 1.
        @rtype: L{BDD}
        """

        vars_to_remove = BDD.ONE(self._utils.dd_mgr)

        if self._minimize[GR1Sect.OUT_VARS]:
            for i in range(0, len(self._utils.output_vars)):
                index = i + len(self._all_reqs)
                if index not in subset:
                    # present and next value of the variable is set to 1:
                    vars_to_remove *= self._utils.output_vars[i].ps
                    vars_to_remove *= self._utils.output_vars[i].ns
        return vars_to_remove

    def _write_configuration(self):
        """
        Writes the minimized specification into a file.

        This method writes the minimized specification into the file
        self._target_file_name. The original specification is
        first read with a DOM XML-Parser. All requirements that were thrown
        out by the minimizer are toggled. A comment is also added to the
        'notes'-tag of this requirement. If no target file name was set,
        nothing is done at all.
        """

        if not self._target_file_name:
            return

        # The original specification is read with a DOM parser:
        dom = parse(self._utils.input_file)

        # Requirements:
        for req in dom.getElementsByTagName("requirement"):
            toggled = req.getElementsByTagName("toggled")[0].firstChild
            if toggled.nodeValue.count("0") > 0:
                # The requirement is not enabled.
                continue
            name = req.getElementsByTagName("name")[0].firstChild
            name_string = name.nodeValue.lstrip().rstrip()
            if name_string in self._remaining_req_names:
                # The requirement was not removed by minimization.
                continue

            # it was removed: we untoggle it and add a comment
            toggled.nodeValue = toggled.nodeValue.replace("1", "0")
            notes = req.getElementsByTagName("notes")[0].firstChild
            notes.nodeValue += "  TAKEN OUT BY SPEC-MINIMIZER\n      "

        # Signals:
        remaining_out_names = [v.name for v in self._remaining_outputs]
        for sig in dom.getElementsByTagName("signal"):
            kind = sig.getElementsByTagName("kind")[0].firstChild
            if kind.nodeValue.count("E") > 0:
                # The signal is controlled by the environment
                continue

            name = sig.getElementsByTagName("name")[0].firstChild
            name_string = name.nodeValue.lstrip().rstrip()
            if name_string in remaining_out_names:
                # The signal was not removed by minimization.
                continue
            # it was removed: we add a comment
            notes = sig.getElementsByTagName("notes")[0].firstChild
            notes.nodeValue += "  TAKEN OUT BY SPEC-MINIMIZER\n      "

        # Finally we write the modified specification:
        cfg_file = open(self._target_file_name, 'w')
        dom.writexml(cfg_file)
        cfg_file.close()

    def _get_element_name(self, index):
        """
        Returns the name to guarantee or output given its index.

        @param index: The index of the guarantee or output where we want to have
               a name for.
        @type index: int
        @return: The name of the guarantee or output.
        @rtype: string
        """
        if index < len(self._all_reqs):
            return self._all_reqs[index].name
        return self._utils.output_vars[index - len(self._all_reqs)].name


    def _superset_already_realizable(self, subset):
        """
        Checks if a superset of guarantees or outputs is already realizable.

        This method checks if a superset of subset already lead to a
        realizable specification.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @return: True if a superset of subset is known that is realizable,
                 False otherwise.
        @rtype: bool
        """

        for realizable_set in self._realizable_sets:
            if realizable_set >= set(subset):
                return True
        return False

    def _subset_already_unrealizable(self, subset):
        """
        Checks if a subset of guarantees or outputs is already unrealizable.

        This method checks if a subset of 'subset' already lead to a
        realizable specification.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @return: True if a superset of subset is known that is realizable,
                 False otherwise.
        @rtype: bool
        """

        for unrealizable_set in self._unrealizable_sets:
            if set(subset) >= unrealizable_set:
                return True
        return False

    def _compute_remaining(self, result):
        """
        Computes remaining outputs and requirements.

        This method computes remaining outputs and requirements and stores them
        in the fields self._remaining_req_names and self._remaining_outputs.

        @param result: A list containing the indices of all guarantees and
               output variables that were not thrown away by the minimization
               algorithm.
        @param result: list<int>
        """

        # Requirements:
        self._remaining_req_names = []
        for req_nr in range(0, len(self._all_reqs)):
            req = self._all_reqs[req_nr]
            if req.kind == RatRequirement.ASSUMPTION or req_nr in result:
                self._remaining_req_names.append(req.name)
        for req in self._fixed_guarantees:
            self._remaining_req_names.append(req.name)


        # Outputs:
        self._remaining_outputs = []
        # if we did not minimize output variables, every output
        # variable is relevant.
        if not self._minimize[GR1Sect.OUT_VARS]:
            self._remaining_outputs = self._utils.output_vars
            return
        # otherwise:
        for i in range(0, len(self._utils.output_vars)):
            index = i + len(self._all_reqs)
            if result.count(index) > 0:
                # the output variable was not thrown away by the minimizer:
                self._remaining_outputs.append(self._utils.output_vars[i])

class RatMinTargetQuantifyProduct(RatMinTarget):
    """
    Equal to RatMinTarget, only the quantification of signals is different.

    This class is equal to the class L{RatMinTarget} with the one exception
    that the semantics of quantifying outputs from the specification is
    slightly different. While in RatMinTarget outputs are quantified from
    every guarantee seperatly, they are quantified from the product of all
    guarantees in this class. The question which of the two semantics is more
    intuitive for the user is still open. Quantifying from the product as done
    in this class is often faster and often leads to slightly smaller results,
    though.

    @see: L{RatMinTarget}
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
               Currently, only the sections GR1Sect.OUT_VARS, GR1Sect.SYS_INIT,
               GR1Sect.SYS_TRANS and GR1Sect.SYS_FAIR can be minimized. All
               other sections are ignored.
        @type minimize: dictionary<string, bool>
        @param use_result: True if the result of the minimization should be
               stored in self._utils, False otherwise.
        @type use_result: bool
        @param target_file_name: The name of the file for the minimized
               specification or None if it should not be written.
        @type target_file_name: string
        """

        RatMinTarget.__init__(self, utils, minimize, use_result, \
                              target_file_name)


        #: The product of all fixed guarantees.
        #: @type: L{RatRequirement}
        self._fixed_guarantees_product = RatRequirement(self._utils)

        #: A cache for the product of sets of guarantees.
        #:
        #: This cache should provide too much recomputation when conjoining
        #: guarantees.
        #: @type: list<L{CacheElement}>
        self._cache = []

        # We do not need the guarantees in self._fixed_guarantees seperatly,
        # we only need their product now. We precompute this product to speed
        # things up:
        self._fixed_guarantees_product.kind = RatRequirement.GUARANTEE
        for fixed in self._fixed_guarantees:
            self._fixed_guarantees_product *= fixed
            # deleting bdds often improves the performance:
            fixed.destroy_bdds()


    def _prepare_configuration(self, subset):
        """
        Overrides the method of the base class to change its semantics.

        This method overrides the method of the base class to change its
        semantics for the quantification of outputs. Outputs are not quantified
        from every guarantee seperately, but from the product of all guarantees.
        The question which of the two semantics is more intuitive for the
        user is still open. Quantifying from the product as done in this method
        is often faster and often leads to slightly smaller results, though.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        """

        # We have two implementations, one using a cache for products of
        # guarantees that have been computed before, the other one not using
        # a cache. Experiments show that the cache does not pay off in most
        # cases, so we use the normal implementation:
        self._prepare_configuration_normal(subset)
        #self._prepare_configuration_cached(subset)


    def _prepare_configuration_normal(self, subset):
        """
        Implements the _prepare_configuration method without any cache.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        """

        vars_to_remove = self._get_vars_to_remove(subset)
        all_guarantees = self._fixed_guarantees_product.copy()
        for index in subset:
            if index < len(self._all_reqs):
                req = self._all_reqs[index]
                all_guarantees *= req
        all_guarantees.remove_vars(vars_to_remove)
        self._current[GR1Sect.SYS_INIT] = all_guarantees.init_bdd
        self._current[GR1Sect.SYS_FAIR] = all_guarantees.fair_bdds
        self._current[GR1Sect.SYS_TRANS] = all_guarantees.trans_bdd

        # empty lists are not allowed for self._current[GR1Sect.SYS_FAIR] and
        # self._current[GR1Sect.ENV_FAIR]:
        mgr = self._utils.dd_mgr
        if len(self._current[GR1Sect.SYS_FAIR]) == 0:
            self._current[GR1Sect.SYS_FAIR].append(BDD.ONE(mgr))
        if len(self._current[GR1Sect.ENV_FAIR]) == 0:
            self._current[GR1Sect.ENV_FAIR].append(BDD.ONE(mgr))

    def _prepare_configuration_cached(self, subset):
        """
        Implements the _prepare_configuration method with some cache.

        This method implements the _prepare_configuration method maintaining a
        cache of products of guarantees. The cache should avoid too many
        recomputations of products of guarantees.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        """

        # 'subset' is a set of integers each representing a gurantee. We need
        # to compute the product of all these guarantees.
        # We search the cache for some product of guarantees that can be reused.
        # We search for the largest subset of the guarantees we need:
        (guarantees, added, still_to_add) = self._get_closest_subset(subset)

        # we add to the product all guarantees which are not yet added:
        for add_me in still_to_add[:]:
            if add_me < len(self._all_reqs):
                added.append(add_me)
                still_to_add.remove(add_me)
                guarantees *= self._all_reqs[add_me]
                # every product we have is added to the cache:
                self._add_cache_entry(added, guarantees)

        vars_to_remove = self._get_vars_to_remove(still_to_add)
        guarantees.remove_vars(vars_to_remove)

        self._current[GR1Sect.SYS_INIT] = guarantees.init_bdd
        self._current[GR1Sect.SYS_FAIR] = guarantees.fair_bdds
        self._current[GR1Sect.SYS_TRANS] = guarantees.trans_bdd

        # empty lists are not allowed for self._current[GR1Sect.SYS_FAIR] and
        # self._current[GR1Sect.ENV_FAIR]:
        mgr = self._utils.dd_mgr
        if len(self._current[GR1Sect.SYS_FAIR]) == 0:
            self._current[GR1Sect.SYS_FAIR].append(BDD.ONE(mgr))
        if len(self._current[GR1Sect.ENV_FAIR]) == 0:
            self._current[GR1Sect.ENV_FAIR].append(BDD.ONE(mgr))

    def _add_cache_entry(self, subset, guarantee):
        """
        Adds an entry to the cache.

        This method stores the product of guarantees represented by a certain
        set of indices to the cache.

        @param subset: A list of integers. Each element is an index of a
               guarantee, so the list represents a set of guarantees.
        @type subset: list<int>
        @param guarantee: The product of all the guarantees listed in 'subset'.
        @type guarantee: L{RatRequirement}
        """
        elem = CacheElement(subset[:], guarantee.copy())
        self._cache.append(elem)

    def _get_closest_subset(self, subset):
        """
        Returns the product of guarantees which is closest to the desire one.

        In the end, we need the product of all guarantees mentioned in 'subset'.
        This method searches the cache for the product of the largest subset of
        guarantees and returns it.

        @param subset: A list of integers. Each element is an index of a
               guarantee, so the list represents a set of guarantees.
        @type subset: list<int>
        @return: A tuple (guarantees, added, still_to_add), where
         - guarantees: is a product of some guarantees mentioned in subset.
         - added: is the list of guarantees that are contained in 'guarantees'.
         - still_to_add: is the list of guarantees that still have to be added
           to 'guarantees'.
        @rtype: (L{RatRequirement}, list<int>, list<int>)
        """

        found = None
        for cache_elem in self._cache:
            if set(cache_elem.subset) <= set(subset):
                if found == None:
                    found = cache_elem
                elif len(found.subset) < len(cache_elem.subset):
                    found = cache_elem
        if found == None:
            return (self._fixed_guarantees_product.copy(), [], subset[:])
        not_covered = subset[:]
        for elem in found.subset:
            not_covered.remove(elem)
        return (found.req.copy(), found.subset[:], not_covered)


class CacheElement(object):
    """
    A class representing a cache entry for L{RatMinTargetQuantifyProduct}.

    @see: L{RatMinTargetQuantifyProduct}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, subset, req):
        """
        Constructor.

        @param subset: A list of integers. Each element is an index of a
               guarantee, so the list represents a set of guarantees.
        @type subset: list<int>
        @param req: The product of all the guarantees listed in 'subset'.
        @type req: L{RatRequirement}
        """

        #: A list of indices of guarantees.
        #: @type: list<int>
        self.subset = subset

        #: The product of all the guarantees listed in 'subset'.
        #: @type: L{RatRequirement}
        self.req = req

# We could derive from RatMinTargetQuantifyProduct, but I think that the
# quantification of outputs as done in RatMinTarget is more intuitive:
#class RatMinTargetOverApprox(RatMinTargetQuantifyProduct):
class RatMinTargetOverApprox(RatMinTarget):
    """
    Also implements an overapproximation of realizability.

    This class also implements an overapproximation of the test function, i.e.,
    it implements the method test_over_approx. This method gives an
    overapproximation of realizability, which can be computed fast. A minimizer
    can exploit this to compute an unrealizable core faster.

    @see: L{ApproxMinimizer}
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
               Currently, only the sections GR1Sect.OUT_VARS, GR1Sect.SYS_INIT,
               GR1Sect.SYS_TRANS and GR1Sect.SYS_FAIR can be minimized. All
               other sections are ignored.
        @type minimize: dictionary<string, bool>
        @param use_result: True if the result of the minimization should be
               stored in self._utils, False otherwise.
        @type use_result: bool
        @param target_file_name: The name of the file for the minimized
               specification or None if it should not be written.
        @type target_file_name: string
        """

       # We could derive from RatMinTargetQuantifyProduct, but I think that the
       # quantification of outputs as done in RatMinTarget is more intuitive:
       #RatMinTargetQuantifyProduct.__init__(self, utils, minimize, use_result,
       #                                     target_file_name)
        RatMinTarget.__init__(self, utils, minimize, use_result,
                              target_file_name)

        #: A counter, counting the overapproximated realizability checks.
        #: @type: int
        self._realizability_checks_over_approx = 0

        #: Nr of realizability checks skipped because superset is realizable.
        #:
        #: A counter, counting the number of overapproximated realizability
        #: checks that do not really have to be performed as a superset of
        #: restrictions of the system is already approximately realizable.
        #: @type: int
        self._checks_covered_by_supersets_over_approx = 0


        #: Nr of realizability checks skipped because subset is unrealizable.
        #:
        #: A counter, counting the number of overapproximated realizability
        #: checks that do not really have to be performed as a subset of
        #: restrictions of the system is already unrealizable.
        #: @type: int
        self._checks_covered_by_subsets_over_approx = 0

        #: A list of all specifications that are approximately realizable.
        #:
        #: A list of all specifications that are approximately realizable. All
        #: subsets of an approximately realizable specification are again
        #: approximately realizable. This can be used to reduce the number of
        #: realizability checks.
        #: @type: list<set<int>>
        self._realizable_sets_over_approx = []

        #: A list of all specifications that are approximately unrealizable.
        #:
        #: A list of all specifications that are approximately unrealizable. All
        #: supersets of an unrealizable specification are again unrealizable.
        #: This can be used to reduce the number of realizability checks.
        #: @type: list<set<int>>
        self._unrealizable_sets_over_approx = []

    def test_over_approx(self, subset, spaces):
        """
        Computes an overapproximation of a realizability test.

        This method implements an overapproximation of a test for realizability.
        Overapproximation means: if the specification is realizable, this
        function must return true. If the specification is unrealizable, this
        method can return whatever it likes. Put the other way round: if this
        method returns false, the specification is unrealizable for sure; if
        it returns true, it might be realizable or unrealizable.

        This method computes the overapproximation of realizability by computing
        an underapproximation of the winning region for the environment (the
        complement is an overapproximation of the winning region for the
        system) and checking if the initial state is contained.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: True if the specification is approximately realizable, False
                 otherwise.
        @rtype: bool
        """

        return self._is_realizable_over_approx(subset, spaces)

    def test_approx_first(self, subset, spaces):
        """
        The function 'test' where approximations are tried first.

        This method is functional equivalent to the function 'test'. The only
        difference is that several underapproximations and overapproximations
        are tried first. Only if none of the approximations give a verdict,
        the original testing procedure is applied. There is the hope that
        this function is faster than the original function 'test', at least
        for complex specifications.

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

        return self._is_realizable(subset, spaces,
                                   self._winm_contains_initial_approx_first)

    def test_approx_first_slim(self, subset, spaces):
        """
        Like test_approx_first, only with fewer approximations.

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

        return self._is_realizable(subset, spaces,
                                 self._winm_contains_initial_approx_first_slim)

    def get_check_statistics_over_approx(self):
        """
        Returns statistics on the overapproximated realizability checks.

        This method returns some performance measures about the number of
        overapproximated realizability checks as string.

        @return: Some statistics about the number of overapproximated
                 realizability checks.
        @rtype: string
        """

        msg = "  %d" % self._realizability_checks_over_approx
        msg += " checks for realizability had to be done\n"
        msg += "  %d" % self._checks_covered_by_supersets_over_approx
        msg += " checks could be omitted, because a superset was "
        msg += "already realizable\n"
        msg += "  %d" % self._checks_covered_by_subsets_over_approx
        msg += " checks could be omitted, because a subset was "
        msg += "already unrealizable\n  -> only "
        done = self._realizability_checks_over_approx
        done -= self._checks_covered_by_supersets_over_approx
        done -= self._checks_covered_by_subsets_over_approx
        msg += "%d checks were actually carried out\n" % done
        return msg

    def get_check_statistics_exact(self):
        """
        Returns statistics on the exact realizability checks.

        This method returns some performance measures about the number of
        exact realizability checks as string.

        @return: Some statistics about the number of exact realizability checks.
        @rtype: string
        """
        return RatMinTarget.get_check_statistics(self)

    def get_check_statistics(self):
        """
        Returns some statistics about the number of realizability checks.

        This method returns some performance measures about the number of
        realizability checks as string.

        @return: Some statistics about the number of realizability checks.
        @rtype: string
        """

        msg = "  Overapproximated checks:\n"
        msg += self.get_check_statistics_over_approx()
        msg += " Exact checks:\n"
        msg += self.get_check_statistics_exact()
        return msg.replace("\n", "\n ")[0:-1]

    def _is_realizable_over_approx(self, subset, spaces):
        """
        Computes an overapproximation of a realizability test.

        This method implements an overapproximation of a test for realizability.
        Overapproximation means: if the specification is realizable, this
        function must return true. If the specification is unrealizable, this
        method can return whatever it likes. Put the other way round: if this
        method returns false, the specification is unrealizable for sure; if
        it returns true, it might be realizable or unrealizable.

        This method computes the overapproximation of realizability by computing
        an underapproximation of the winning region for the environment (the
        complement is an overapproximation of the winning region for the
        system) and checking if the initial state is contained.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: True if the specification is approximately realizable, False
                 otherwise.
        @rtype: bool
        """

        starttime = time.clock()
        self._realizability_checks_over_approx += 1
        if self._superset_already_realizable_over_approx(subset):
            self._checks_covered_by_supersets_over_approx += 1
            msg = "checking (over-approx) with " + self.get_string_rep(subset)
            msg += " (superset already realizable)"
            msg += " (%10.3f sec)" % (time.clock() - starttime)
            msg += " -> realizable (over-approx)"
            self._log(msg, spaces)
            return True

        if self._subset_already_unrealizable_over_approx(subset):
            self._checks_covered_by_subsets_over_approx += 1
            msg = "checking (over-approx) with " + self.get_string_rep(subset)
            msg += " (subset already unrealizable)"
            msg += " (%10.3f sec)" % (time.clock() - starttime)
            msg += " -> unrealizable"
            self._log(msg, spaces)
            return False

        # Writing all formulas that are listed in subset into self._current:
        self._prepare_configuration(subset)

        # Checking if the overapproximation of the winning region contains the
        # initial state ...
        # This method reads out self._current:
        realizable = self._winm_contains_initial_over_approx()

        msg = "checking (over-approx) with " + self.get_string_rep(subset)
        if realizable:
            self._realizable_sets_over_approx.append(set(subset))
            msg += "(%10.3f sec) -> realizable (over-approx)" % (time.clock() -
                                                                 starttime)
            self._log(msg, spaces)
            return True

        self._unrealizable_sets_over_approx.append(set(subset))
        msg +="(%10.3f sec) -> unrealizable (over-approx)" % (time.clock() -
                                                              starttime)
        self._log(msg, spaces)
        return False


    def _winm_contains_initial_over_approx(self):
        """
        Checks if all the initial states are winning.

        This method checks if the initial states are contained in an
        overapproximation of the winning region of the system.  This is done by
        computing an underapproximation of the winning region for the
        environment and checking if some of the initial states are contained.
        (The complement of the underapproximation of the winning region for
        the system is an overapproximation of the winning region for the
        environment.)

        The underapproximation of the winning region for the environment is
        intented to be both: not too coarse and fast to compute. We therefore
        decided for the following approximation: We compute the set of states
        from which FG(or_j(and_i(env_fair[i]) and not sys_fair[j])) can be
        ensured.

        @return: True if the overapproximation of the winning region for
                 the system contains the initial states, False otherwise.
        @rtype: bool
        """

        if self._current[GR1Sect.ENV_INIT].isZero() or \
           self._current[GR1Sect.SYS_INIT].isZero():
            return self._can_win_system(BDD.ZERO(self._utils.dd_mgr))

        guarantees = self._current[GR1Sect.SYS_FAIR]
        assumptions = self._current[GR1Sect.ENV_FAIR]

        m = len(assumptions)
        n = len(guarantees)

        # computing and_i(env_fair[i]), i.e., the intersection of all sets of
        # env-fair states:
        inter = BDD.ONE(self._utils.dd_mgr)
        for a in assumptions:
            inter = inter * a
        if inter.isZero():
            return True

        win = BDD.ZERO(self._utils.dd_mgr)

        # for all sets of sys-fair states:
        for g in guarantees:
            # computing and_i(env_fair[i]) and not sys_fair[j]
            stay_in = inter * (~g)
            if stay_in.isZero():
                continue
            # a greatest fixpoint to compute all states from which the
            # environment can envorce the play to stay in stay_in (a simple
            # safety game).
            Y = BDD.ONE(self._utils.dd_mgr)
            Y_old = BDD.ZERO(self._utils.dd_mgr)
            while Y != Y_old:
                Y_old = Y
                Y = stay_in * self._coax_env(Y)

            # the result of the safety game is now in Y. The environment needs
            # to win only one such safety game (for one j), so we compute the
            # disjunction of all sets Y in win:
            win = win + Y

            # if the initial states are already contained, we can
            # abort because win can only become larger:
            if self._can_win_environment(win):
                return False

        # Solving a reachability game to see from which states the environment
        # can force a play to a state of 'win':
        R = BDD.ZERO(self._utils.dd_mgr)
        R_old = BDD.ONE(self._utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = win + self._coax_env(R)
            if self._can_win_environment(R):
                return False
        return True


    def _winm_contains_initial_approx_first(self):
        """
        Checks if the initial states are winning.

        This method checks if the initial states are contained in the winning
        region of the system. This method is functionally equivalent to the
        function _winm_contains_initial. The only difference is that several
        overapproximations and underapproximations of the winning region are
        computed. Only if the approximations do not lead to a clear verdict,
        the exact check for realizability is performed. There is the hope that
        this function is faster than the original function 
        _winm_contains_initial, at least for complex specifications.

        @return: True if the winning region for the system contains the 
                 initial states, False otherwise.
        @rtype: bool
        """

        if self._current[GR1Sect.ENV_INIT].isZero() or \
           self._current[GR1Sect.SYS_INIT].isZero():
            return self._can_win_system(BDD.ZERO(self._utils.dd_mgr))

        guarantees = self._current[GR1Sect.SYS_FAIR]
        assumptions = self._current[GR1Sect.ENV_FAIR]

        m = len(assumptions)
        n = len(guarantees)

        # ----------------------------------------------------------------
        # First underapproximation: Is the system able to violate one
        # assumption? If yes: the spec is realizable for sure. If no: we do not
        # know if it is realizable or unrealizable.
        globally_not_env_fair = BDD.ZERO(self._utils.dd_mgr)
        for i in range(0, m):
            Y = BDD.ONE(self._utils.dd_mgr)
            Y_old = BDD.ZERO(self._utils.dd_mgr)
            while Y != Y_old:
                Y_old = Y
                Y = (~assumptions[i]) * self._coax_fast(Y)
            globally_not_env_fair += Y
            del Y
            del Y_old
            if self._can_win_system(globally_not_env_fair):
                return True
        R = BDD.ZERO(self._utils.dd_mgr)
        R_old = BDD.ONE(self._utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = globally_not_env_fair + self._coax_fast(R)
            if self._can_win_system(R):
                return True
        del globally_not_env_fair
        del R_old

        # ----------------------------------------------------------------
        # Next underapproximation: Is the system able to fulfill all
        # guarantees? If yes: the spec is realizable for sure. If no: we do not
        # know if it is realizable or unrealizable.
        # We do not compute all states from which the system can fulfill all
        # guarantees, we only compute an underapproximation thereof: We compute
        # all states from which the system can enforce that the play stays in
        # the intersection of all (buechi)-accepting states.
        inter_g = BDD.ONE(self._utils.dd_mgr)
        for g in guarantees:
            inter_g = inter_g * g
        Y = BDD.ONE(self._utils.dd_mgr)
        Y_old = BDD.ZERO(self._utils.dd_mgr)
        while Y != Y_old:
            Y_old = Y
            Y = inter_g * self._coax_fast(Y)
        del Y_old
        del inter_g
        if self._can_win_system(Y):
            return True

        # here we combine the first two underapproximations:
        won = R + Y
        del R
        del Y
        if self._can_win_system(won):
            return True
        R = BDD.ZERO(self._utils.dd_mgr)
        R_old = BDD.ONE(self._utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = won + self._coax_fast(R)
            if self._can_win_system(R):
                return True
        del R
        del R_old
        del won

        # ----------------------------------------------------------------
        # First overapproximation: Is the environment able to fulfill all
        # assumptions and violate one guarantee? If yes: the spec is
        # unrealizable for sure. If no: we do not know if it is realizable or
        # unrealizable. We do not compute these states exactly, we compute an
        # underapproximation thereof. See _winm_contains_initial_over_approx 
        # for a description.

        inter_a = BDD.ONE(self._utils.dd_mgr)
        for a in assumptions:
            inter_a = inter_a * a
        env_win = BDD.ZERO(self._utils.dd_mgr)
        for g in guarantees:
            stay_in = inter_a * (~g)
            if stay_in.isZero():
                continue
            Y = BDD.ONE(self._utils.dd_mgr)
            Y_old = BDD.ZERO(self._utils.dd_mgr)
            while Y != Y_old:
                Y_old = Y
                Y = stay_in * self._coax_env(Y)
            del Y_old
            del stay_in
            env_win = env_win + Y
            del Y
            if self._can_win_environment(env_win):
                return False
        R = BDD.ZERO(self._utils.dd_mgr)
        R_old = BDD.ONE(self._utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = env_win + self._coax_env(R)
            if self._can_win_environment(R):
                return False
        del R_old
        del env_win

        # ----------------------------------------------------------------
        # If none of the above worked, we compute the exact winning region
        # for the system (see _winm_contains_initial). The complement of the
        # underapproximation of the winning region for the environment is an
        # overapproximation for the winning region of the system. We therefore
        # take it as a starting point for outermost (greatest) fixpoint:
        z = ~R
        del R
        old_z = BDD.ZERO(self._utils.dd_mgr)
        if z.isZero():
            old_z = BDD.ONE(self._utils.dd_mgr)
        while z != old_z: # GreatestFixpoint(z)
            old_z = z
            for j in range(0, n):
                old_y = BDD.ONE(self._utils.dd_mgr)
                y = BDD.ZERO(self._utils.dd_mgr)
                while y != old_y:  # LeastFixpoint(y)
                    old_y = y
                    start = (guarantees[j] * self._coax_fast(z)) + \
                            self._coax_fast(y)
                    y = BDD.ZERO(self._utils.dd_mgr)
                    for i in range(0, m):
                        old_x = BDD.ZERO(self._utils.dd_mgr)
                        x = z
                        while x != old_x: # GreatestFixpoint(x)
                            old_x = x
                            x = start + ((~assumptions[i]) \
                                * self._coax_fast(x))
                        del old_x
                        y = y + x
                        del x
                    del start
                # End -- LeastFixpoint(y)
                del old_y
                z = y
                del y
                # z is in a greatest fixpoint, so z can only get smaller. If
                # some intermediate z does not contain the initial state, the
                # final z won't contain the initial state as well. So we can
                # abort.
                if not self._can_win_system(z):
                    return False
            # End -- For (j in 1...n)
        # End -- GreatestFixpoint(z)
        del old_z
        if self._can_win_system(z):
            return True
        return False

    def _winm_contains_initial_approx_first_slim(self):
        """
        Like _winm_contains_initial_approx_first but with fewer approximations.

        @return: True if the winning region for the system contains the initial
                 states, False otherwise.
        @rtype: bool
        """

        if self._current[GR1Sect.ENV_INIT].isZero() or \
           self._current[GR1Sect.SYS_INIT].isZero():
            return self._can_win_system(BDD.ZERO(self._utils.dd_mgr))

        guarantees = self._current[GR1Sect.SYS_FAIR]
        assumptions = self._current[GR1Sect.ENV_FAIR]

        m = len(assumptions)
        n = len(guarantees)

        # ----------------------------------------------------------------
        # First underapproximation: Is the system able to violate one
        # assumption? If yes: the spec is realizable for sure. If no: we do not
        # know if it is realizable or unrealizable.
        globally_not_env_fair = BDD.ZERO(self._utils.dd_mgr)
        for i in range(0, m):
            Y = BDD.ONE(self._utils.dd_mgr)
            Y_old = BDD.ZERO(self._utils.dd_mgr)
            while Y != Y_old:
                Y_old = Y
                Y = (~assumptions[i]) * self._coax_fast(Y)
            globally_not_env_fair += Y
            del Y
            del Y_old
            if self._can_win_system(globally_not_env_fair):
                return True
        R = BDD.ZERO(self._utils.dd_mgr)
        R_old = BDD.ONE(self._utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = globally_not_env_fair + self._coax_fast(R)
            if self._can_win_system(R):
                return True
        del globally_not_env_fair
        del R_old

        # ----------------------------------------------------------------
        # Next underapproximation: Is the system able to fulfill all
        # guarantees? If yes: the spec is realizable for sure. If no: we do not
        # know if it is realizable or unrealizable.
        # We do not compute all states from which the system can fulfill all
        # guarantees, we only compute an underapproximation thereof: We compute
        # all states from which the system can enforce that the play stays in
        # the intersection of all (buechi)-accepting states.
        inter_g = BDD.ONE(self._utils.dd_mgr)
        for g in guarantees:
            inter_g = inter_g * g
        Y = BDD.ONE(self._utils.dd_mgr)
        Y_old = BDD.ZERO(self._utils.dd_mgr)
        while Y != Y_old:
            Y_old = Y
            Y = inter_g * self._coax_fast(Y)
        del Y_old
        del inter_g
        if self._can_win_system(Y):
            return True

        # here we combine the first two underapproximations:
        won = R + Y
        del R
        del Y
        if self._can_win_system(won):
            return True
        R = BDD.ZERO(self._utils.dd_mgr)
        R_old = BDD.ONE(self._utils.dd_mgr)
        while R != R_old:
            R_old = R
            R = won + self._coax_fast(R)
            if self._can_win_system(R):
                return True
        del R
        del R_old
        del won

        # ----------------------------------------------------------------
        # If none of the above worked, we compute the exact winning region
        # for the system (see _winm_contains_initial). The complement of the
        # underapproximation of the winning region for the environment is an
        # overapproximation for the winning region of the system. We therefore
        # take it as a starting point for outermost (greatest) fixpoint:
        z = BDD.ONE(self._utils.dd_mgr)
        old_z = BDD.ZERO(self._utils.dd_mgr)
        while z != old_z: # GreatestFixpoint(z)
            old_z = z
            for j in range(0, n):
                old_y = BDD.ONE(self._utils.dd_mgr)
                y = BDD.ZERO(self._utils.dd_mgr)
                while y != old_y:  # LeastFixpoint(y)
                    old_y = y
                    start = (guarantees[j] * self._coax_fast(z)) + \
                            self._coax_fast(y)
                    y = BDD.ZERO(self._utils.dd_mgr)
                    for i in range(0, m):
                        old_x = BDD.ZERO(self._utils.dd_mgr)
                        x = z
                        while x != old_x: # GreatestFixpoint(x)
                            old_x = x
                            x = start + ((~assumptions[i]) \
                                * self._coax_fast(x))
                        del old_x
                        y = y + x
                        del x
                    del start
                # End -- LeastFixpoint(y)
                del old_y
                z = y
                del y
                # z is in a greatest fixpoint, so z can only get smaller. If
                # some intermediate z does not contain the initial state, the
                # final z won't contain the initial state as well. So we can
                # abort.
                if not self._can_win_system(z):
                    return False
            # End -- For (j in 1...n)
        # End -- GreatestFixpoint(z)
        del old_z
        if self._can_win_system(z):
            return True
        return False

    def _coax_env(self, states):
        """
        Computes the mixed preimage for the environment of a set of states.

        This method calculates the states, from which the environment can
        enforce to reach 'states' in one step. It is basically equal to the
        method of the L{CounterstrategyComputer}. The difference is, that it
        works on the minimized specification in self._current.

        @param states: The states where we want to know the mixed preimage.
        @type states: L{BDD}
        @return: All states, from which 'states' can be enforced by the
                 environment in one step.
        @rtype: L{BDD}
        """

        env_transitions = self._current[GR1Sect.ENV_TRANS]
        sys_transitions = self._current[GR1Sect.SYS_TRANS]
        output_product = self._utils.next_out_var_cube
        input_product = self._utils.next_in_var_cube

        swapped_states = self._utils.swap_present_next(states)
        target_or_forbidden = (~sys_transitions) + swapped_states
        env_moves_to_target = (target_or_forbidden).forall(output_product)
        mixed_preimage = env_moves_to_target.andExists(env_transitions, \
                                                       input_product)
        return mixed_preimage


    def _superset_already_realizable_over_approx(self, subset):
        """
        Checks if a superset of guarantees or outputs is already realizable.

        This method checks if a superset of subset already lead to a
        approximately realizable specification.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @return: True if a superset of subset is known that is realizable,
                 False otherwise.
        @rtype: bool
        """

        for realizable_set in self._realizable_sets_over_approx:
            if realizable_set >= set(subset):
                return True
        # i guess the following lines might make us lose monotonicity?
        #for realizable_set in self._realizable_sets:
        #    if realizable_set >= set(subset):
        #        return True
        return False

    def _subset_already_unrealizable_over_approx(self, subset):
        """
        Checks if a subset of guarantees or outputs is already unrealizable.

        This method checks if a subset of 'subset' already lead to a
        approximately unrealizable specification.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @return: True if a superset of subset is known that is realizable,
                 False otherwise.
        @rtype: bool
        """

        for unrealizable_set in self._unrealizable_sets_over_approx:
            if set(subset) >= unrealizable_set:
                return True
        return False

    def _subset_already_unrealizable(self, subset):
        """
        Checks if a subset of guarantees or outputs is already unrealizable.

        This method checks if a subset of 'subset' already lead to a
        realizable specification. It overrides the according method of the
        base class. If a specification is unrealizable under
        _is_realizable_over_approx, then it is also unrealizable under
        _is_realizable. Hence, we can also search through
        self._unrealizable_sets_over_approx.

        @param subset: A list of integers. Each element is an index of a
               guarantee or output, so the list represents a specification.
        @type subset: list<int>
        @return: True if a superset of subset is known that is realizable,
                 False otherwise.
        @rtype: bool
        """

        for unrealizable_set in self._unrealizable_sets:
            if set(subset) >= unrealizable_set:
                return True
        for unrealizable_set in self._unrealizable_sets_over_approx:
            if set(subset) >= unrealizable_set:
                return True
        return False


class RatRequirement(object):
    """
    A class that represents a RAT-requirement.

    This class represents a RAT-requirement. It offers various methods for
    combining and manipulating requirements.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """


    #: A constant for requirements representing assumptions.
    #: @type: string
    ASSUMPTION = "A"

    #: A constant for requirements representing guarantees.
    #: @type: string
    GUARANTEE = "G"

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

        #: The name of the requirement.
        #: @type: string
        self.name = None

        #: The kind of the requirement (ASSUMPTION or GUARANTEE).
        #: @type: string
        self.kind = None

        #: The initial condition represented by the requirement.
        #: L{BDD}
        self.init_bdd = BDD.ONE(self.__utils.dd_mgr)

        #: The transition relation represented by the requirement.
        #: L{BDD}
        self.trans_bdd = BDD.ONE(self.__utils.dd_mgr)

        #: The fairness conditions represented by the requirement.
        #: list<L{BDD}>
        self.fair_bdds = []

    def destroy_bdds(self):
        """
        Destroys the bdds of a requirement.

        This method is used to keep the number of alive-BDDs as low as possible,
        which in general improves the performance.
        """

        self.init_bdd = BDD.ONE(self.__utils.dd_mgr)
        self.trans_bdd = BDD.ONE(self.__utils.dd_mgr)
        self.fair_bdds = []

    def has_init(self):
        """
        Returns True if the requirement contains an initial condition.

        @return: True if the requirement contains an initial condition, False
                 otherwise.
        @rtype: bool
        """
        return self.init_bdd.isNotOne()

    def has_trans(self):
        """
        Returns True if the requirement contains a transition relation.

        @return: True if the requirement contains a transition relation, False
                 otherwise.
        @rtype: bool
        """
        return self.trans_bdd.isNotOne()

    def has_fair(self):
        """
        Returns True if the requirement contains fairness conditions.

        @return: True if the requirement contains fairness conditions, False
                 otherwise.
        @rtype: bool
        """
        return (len(self.fair_bdds) > 0)

    def copy(self):
        """
        Returns a (deep) copy of the requirement.

        @return: A (deep) copy of the requirement.
        @rtype: L{RatRequirement}
        """
        res = RatRequirement(self.__utils)
        res.name = self.name
        res.kind = self.kind
        res.init_bdd = self.init_bdd.copy()
        res.trans_bdd = self.trans_bdd.copy()
        for fair in self.fair_bdds:
            res.fair_bdds.append(fair.copy())
        return res

    def remove_vars(self, variables_cube):
        """
        Removes a set of variables from the requirement.

        This method removes a set of variables from the requirement by
        existential quantification in all bdds.

        @return: self, to be used in assignments.
        @rtype: L{RatRequirement}
        """
        self.init_bdd = self.init_bdd.exists(variables_cube)
        self.trans_bdd = self.trans_bdd.exists(variables_cube)
        all_fair_bdds = self.fair_bdds[:]
        self.fair_bdds = []
        for fair in all_fair_bdds:
            new_fair = fair.exists(variables_cube)
            if new_fair.isNotOne():
                self.fair_bdds.append(new_fair)
        return self


    def __mul__(self, other):
        """
        Combines two requirements, overloads: *

        This method combines two RatRequirement. The initial condition and the
        transition relation are intersected. The fairness constraints are
        appended.

        @param other: The second RatRequirement.
        @type other: L{RatRequirement}
        @return: The combination of the two requirements.
        @rtype: L{RatRequirement}
        """
        if not isinstance(other, RatRequirement):
            return NotImplemented
        if self.kind != other.kind:
            return NotImplemented
        res = RatRequirement(self.__utils)
        res.name = "some set of requirements"
        res.kind = self.kind
        res.init_bdd = self.init_bdd * other.init_bdd
        res.trans_bdd = self.trans_bdd * other.trans_bdd
        for fair in self.fair_bdds:
            res.fair_bdds.append(fair.copy())
        for fair in other.fair_bdds:
            res.fair_bdds.append(fair.copy())
        return res

    def __imul__(self, other):
        """
        Combines the requirement with another one, overloads: *=

        This method combines the requirement with another one. The initial
        condition and the transition relation are intersected. The fairness
        constraints are appended.

        @param other: The second RatRequirement.
        @type other: L{RatRequirement}
        @return: self, to be used in assignments.
        @rtype: L{RatRequirement}
        """
        if not isinstance(other, RatRequirement):
            return NotImplemented
        if self.kind != other.kind:
            return NotImplemented
        self.name = "some combination of requirements"
        self.init_bdd = self.init_bdd * other.init_bdd
        self.trans_bdd = self.trans_bdd * other.trans_bdd
        for fair in other.fair_bdds:
            self.fair_bdds.append(fair.copy())
        return self


class SpecSplitter(object):
    """
    Splits a RAT specification into parts.

    This class splits a RAT specification into a set of requirements. For
    every requirement in the specification, a RatRequirement is created which
    contains the BDDs caused by this requirement.

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

        #: A list of RatRequirements that were created from the spec.
        #: @type: list<L{RatRequirement}>
        self.__requirements = []

        #: The name of the temporary file used.
        #: @type: string
        self._tmp_file_name = "./tmp_nusmv_in"

        # we start the computation of the requirements:
        self._compute_requirements()


    def get_requirements(self):
        """
        Returns the requirements that were found in the specification.

        @return: The requirements that were found in the specification.
        @rtype: list<L{RatRequirement}>
        """
        return self.__requirements

    def _compute_requirements(self):
        """
        Creates RatRequirements from the specification.

        This method creates RatRequirements from the specification. It does
        this by writing the specification with all signals but only one
        requirement enabled into a file and parsing it with nusmv. This is
        done for all requirements.
        """


        # parsing the input file:
        dom = parse(self.__utils.input_file)

        # Looking for requirements that are enabled:
        enabled_reqs = []
        for req in dom.getElementsByTagName("requirement"):
            toggled = req.getElementsByTagName("toggled")[0].firstChild
            if toggled.nodeValue.count("1") > 0:
                enabled_reqs.append(req)
            # we also remove all requirments
            req.parentNode.removeChild(req)

        # We need to add a dummy assumption. Otherwise nusmv might see the
        # spec as a definition of a Buechi-game or a Avoid-Deadlock-game and
        # not as a GR(1) game:
        dummy = self._create_dummy_assumption(enabled_reqs[0])
        dom.getElementsByTagName("requirements")[0].appendChild(dummy)

        for enabled_req in enabled_reqs:
            # find out the kind and the name of the requirement:
            kind = enabled_req.getElementsByTagName("kind")[0].firstChild
            if kind.nodeValue.find("G") < 0:
                kind = RatRequirement.ASSUMPTION
            else:
                kind = RatRequirement.GUARANTEE
            name = enabled_req.getElementsByTagName("name")[0].firstChild
            name = name.nodeValue.strip().rstrip()

            # we add one of the enabled requirements:
            dom.getElementsByTagName("requirements")[0].appendChild(enabled_req)

            # turn the requirement into a RatRequirement:
            new = self._dom_to_requirement(dom, kind, name)
            self.__requirements.append(new)

            # and remove it again:
            enabled_req.parentNode.removeChild(enabled_req)

        # reading the orignial spec again just costs time, so we skip it:
        #self._reset_nusmv()
        #self.__utils.spec.readSpecification()
        os.remove(self._tmp_file_name)

    def _dom_to_requirement(self, dom, kind, name):
        """
        Turns a dom into a RatRequirement.

        This method turns a dom into a RatRequirement. It assumes that only
        one requirement is enabled in the passed dom. It writes the dom into
        a file and parses it with nusmv.

        @param dom: The dom where only one requirement is enabled.
        @type dom: xml.dom.minidom
        @param kind: Either RatRequirement.ASSUMPTION or GUARANTEE.
        @type kind: string
        @param kind: The name of the requirement.
        @type kind: string
        @return: The resulting RatRequirement.
        @rtype: L{RatRequirement}
        """

        # writing the requirements into a file:
        cfg_file = open(self._tmp_file_name, 'w')
        dom.writexml(cfg_file)
        cfg_file.close()

        # parsing the file:
        self._reset_nusmv()
        self.__utils.spec.readSpecification(self._tmp_file_name)

        # creating a RatRequirement from the bdds:
        req = RatRequirement(self.__utils)
        req.name = name
        req.kind = kind
        req.init_bdd = self.__utils.spec.get_init12(self.__utils.dd_mgr)
        req.trans_bdd = self.__utils.spec.get_trans12(self.__utils.dd_mgr)

        all_fair = []
        if kind == RatRequirement.ASSUMPTION:
            all_fair = self.__utils.spec.get_assumptions(self.__utils.dd_mgr)
        else:
            all_fair = self.__utils.spec.get_guarantees(self.__utils.dd_mgr)
        for fair in all_fair:
            if fair.isNotOne():
                req.fair_bdds.append(fair)
        return req


    def _reset_nusmv(self):
        """
        Resets nusmv.

        This method resets nusmv. This is necessary in order to be able to
        parse a new specification with nusmv.
        """

        # deleting the bdds in the spec as they were created in the nusmv
        # dd manager:
        self.__utils.spec.clear()

        # removing some commands:
        # (This is done to avioid warnings from nusmv during reset)
        #cmd.Cmd_CommandRemove("read_rat_file")
        #cmd.Cmd_CommandRemove("check_reach_target")
        #cmd.Cmd_CommandRemove("check_reach_deadlock")
        #cmd.Cmd_CommandRemove("check_avoid_target")
        #cmd.Cmd_CommandRemove("check_avoid_deadlock")
        #cmd.Cmd_CommandRemove("check_buchi_game")
        #cmd.Cmd_CommandRemove("check_gen_reactivity")

        # performing the actual reset:
        cmd.Cmd_CommandExecute("reset")
        BDD.dd_mgr = dd.cvar.dd_manager


    def _create_dummy_assumption(self, source):
        """
        Creates a dummy assumption.

        This method creates a dummy assumption. This assumption is added to
        the specification in order to convice nusmv that this is a GR(1)
        specification and no Buechi-spec or a Avoid-Deadlock-spec.

        @param source: A requirement that is used as a copy source.
        @type source: xml.Node
        @return: The dummy assumption.
        @rtype: xml.Node
        """
        dummy = source.cloneNode(True)
        kind = dummy.getElementsByTagName("kind")[0].firstChild
        kind.nodeValue = "A"
        prop = dummy.getElementsByTagName("property")[0].firstChild
        prop.nodeValue = "(G(F(TRUE)))"
        name = dummy.getElementsByTagName("name")[0].firstChild
        name.nodeValue = "dummy_assumption1"
        notes = dummy.getElementsByTagName("notes")[0].firstChild
        notes.nodeValue = "dummy_assumption1"
        return dummy
