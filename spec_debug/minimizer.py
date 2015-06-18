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
Contains classes that implement minimization algorithms.
"""

from spec_debug_utils import PLog
import time
import math

class Minimizer(object):
    """
    Represents an Interface for all minimization algorithms.

    @see: L{SimpleMinimizer}
    @see: L{DeltaDebugger}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, min_target, log_file_name):
        """
        Constructor.

        @param min_target: Some implementation of the interface L{MinTarget}.
               This implementation implements a concrete test() function.
        @type min_target: L{MinTarget}
        @param log_file_name: A file to write log entries to, or None if no
               log file whould be written.
        @type log_file_name: string
        """

        #: Some implementation of the interface L{MinTarget}.
        #: @type: L{MinTarget}
        self._min_target = min_target

        #: The test-function according to which the set should be minimized.
        #: @type: function
        self.test_function = min_target.test

        #: A file to write log messages to.
        #: @type: file
        self._log_file = None

        #: The name of the file to write log messages to.
        #: @type: string
        self._log_file_name = log_file_name

    def minimize(self, all_elements):
        """
        Applies the minimization algorithm to a given set.

        This method applies the minimization algorithm. Given a set of
        elements it returns a subset thereof still failing the test.

        @param all_elements: A list of elements that should be minimized.
        @type all_elements: list<some_type>
        @return: A list containing the minimal subset of all_elements which
                 makes the function test() fail.
        @rtype: list<some_type>
        """

        print "ERROR: Minimizer::minimize called!"
        print "ERROR: Override this method in a derived class!"
        exit(-1)

    def start(self):
        """
        Applies the minimization algorithm to the L{MinTarget}.

        This method applies the minimization algorithm to the L{MinTarget}.
        It asks the L{MinTarget} for a set to be minimized, minimizes it
        and notifies the L{MinTarget} about the result. If a log file name has
        been passed to the constructor, log messages are written into this file
        during the minimization process.
        """

        if self._log_file_name:
            self._log_file = open(self._log_file_name, 'w')
        self._min_target.set_log_file(self._log_file)
        starttime = time.clock()

        # Asking the minimization target for some set of elements that can be
        # minimized:
        all_elements = self._min_target.get_elements_to_minimize()

        # Performing the minimization:
        result = self.minimize(all_elements)

        # Printing the final solution into the log file:
        self._log("Final solution:")
        self._log(" " + self._min_target.get_string_rep(result))

        # Notifying the solution to the minimization target:
        self._min_target.set_final_solution(result)

        # Logging some statistics:
        msg = self._create_log_msg(result, time.clock() - starttime)
        self._log(msg, 0)
        PLog.log(msg)
        if self._log_file:
            self._log_file.close()
            self._log_file = None

    def _log(self, msg, nr_spaces = 0):
        """
        Logs a message.

        This method adds a message to the log file self._log_file.
        The message is indented by nr_spaces spaces. If no log file was
        specified, this method does nothing at all.

        @param msg: The message to log.
        @type msg: string
        @param nr_spaces: The number of spaces to put in front of the message.
        @type nr_spaces: int
        """

        if not self._log_file:
            return
        self._log_file.write(" " * nr_spaces)
        self._log_file.write(msg)
        self._log_file.write("\n")


    def _create_log_msg(self, result, time_needed):
        """
        Creates a log message containing performance measures.

        @param result: The minimization result.
        @type result: list<some_type>
        @param time_needed: The time needed for minimization.
        @type time_needed: float
        @return: A log message containing performance measures.
        @rtype: string
        """

        msg = " Some statistics:\n"
        msg += self._min_target.get_min_statistics(result)
        msg += "  time for minimization: %.2f seconds\n" % time_needed
        return msg

class DeltaDebugger(Minimizer):
    """
    Implements the Delta Debugging algorithm.

    This class implements the Delta Debugging algorithm as introduced in:
     - 'Finding Failure Causes through Automated Testing' by
       Holger Cleve and Andreas Zeller.
    Information can also be found at:
     - www.st.cs.uni-sb.de/dd/

    Delta Debugging can be used to find the minimal input to a function test()
    that still fails the test (i.e., test(input)=false). This class can be
    used with arbitrary inputs and arbitrary implementations of the function
    'test'. The delta debugger works with some implementation of the
    L{MinTarget} interface which implements some concrete test() function.

    We use Delta Debugging to answer the following question:
    'Which formulas of my specification can I leave out while still
    having the same problem in my specification?'
    The idea is then to find the problem in the (simpler) specification
    much faster, because all formulas that are irrelevant for that
    problem have been removed. Only the statements really causing the
    problem remain. In our case the 'problem' is that the specification is not
    realizable.

    If a log_file_name is passed to the constructor, all steps performed by
    the delta debugging algorithm as well as performance measures are witten
    to this file.

    @see: L{MinTarget}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, min_target, log_file_name):
        """
        Constructor

        @param min_target: Some implementation of the interface L{MinTarget}.
               This implementation implements a concrete test() function.
        @type min_target: L{MinTarget}
        @param log_file_name: A file to write log entries to, or None if no
               log file whould be written.
        @type log_file_name: string
        """

        Minimizer.__init__(self, min_target, log_file_name)

    def minimize(self, all_elements):
        """
        Applies the delta debugging algorithm to a given set.

        This method applies the delta debugging algorithm. Given a set of
        elements it returns a subset thereof still failing the test.

        @param all_elements: A list of elements that should be minimized.
        @type all_elements: list<some_type>
        @return: A list containing the minimal subset of all_elements which
                 makes the function test() fail.
        @rtype: list<some_type>
        """

        return self._ddmin(all_elements)

    def _ddmin(self, all_elements):
        """
        Implements the 'ddmin' operation.

        This method implements the 'ddmin' operation as defined in the Delta
        Debugging algorithm in:
         - 'Finding Failure Causes through Automated Testing'
            by Holger Cleve and Andreas Zeller
        ddmin2 is called with granularity 2. Logging information that allows
        to trace what the algorithm actually did is written to the log file.

        @param all_elements: A list of elements that should be minimized.
        @type all_elements: list<some_type>
        @return: A list containing the minimal subset of all_elements which
                 makes the function test() fail.
        @rtype: list<some_type>
        """

        # starting the search with granularity 2:
        result = self._ddmin2(all_elements, 2, 0)

        return result

    def _ddmin2(self, elements, n, spaces):
        """
        Implements the 'ddmin2' operation.

        This method implements the 'ddmin2' operation as defined in the Delta
        Debugging algorithm in:
         - 'Finding Failure Causes through Automated Testing'
            by Holger Cleve and Andreas Zeller
        A set of elements is passed. This set is first split into subsets in
        the try_subsets method. If one of the subsets fails the test (i.e.
        test(subset) == false), this subset is taken as new starting point and
        ddmin2 is called on this subset. If none of the subsets fail the
        test, all complementary subsets are examined in the same way. If this
        does not lead to a smaller amount of elements which fail the test,
        the granularity is increased. If this does not help either, we simply
        return the elements we got as minimal subset.

        @param elements: A list of elements that should be minimized.
        @type elements: list<some_type>
        @param n: The current granularity. It determines the size of the
               subsets when the incoming set is divided in try_subsets and
               try_complements.
        @type n: int
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: A list containing a subset of all_elements which makes the
                 function test() fail.
        @rtype: list<some_type>
        """

        # Printing some logging information:
        msg = "processing ddmin2("
        msg += self._min_target.get_string_rep(elements) + ", %d)" % n
        self._log(msg, spaces)

        # If the granularity is already greater than the number
        # of elements we examine, we can return the set we got, since
        # we have already examined the smallest possible subsets:
        if (n > len(elements)):
            self._log(" (can't divide into %d parts -> abort)" % n, spaces)
            return elements
        

        # First we apply the 'reduce to subsets'-operation:
        result = self._try_subsets(elements, n, spaces + 2)
        if result:
            return result

        # If there were no subsets that failed the test, we apply the
        #'reduce to complement'-operation. We don't do this if n<=2 because
        # in this case the complements are equal to the subsets:
        if n > 2:
            result = self._try_complements(elements, n, spaces + 2)
        else:
            self._log(" (We can skip the complements, because for n=2", spaces)
            self._log(" the complements are equal to the subsets)", spaces)
        if result:
            return result
        

        # If none of the above worked and if n < len(elements) we increase the
        # granularity:
        if n < len(elements):
            self._log(" increase the granularity:", spaces)
            gran = min(2 * n, len(elements))
            return self._ddmin2(elements, gran, spaces + 2)
        

        # otherwise we return the set we got.
        self._log(" (can't increase granularity any further -> abort)", spaces)
        return elements

    def _try_subsets(self, elements, nr_of_subsets, spaces):
        """
        Implements the 'reduce to subset' operation.

        This method implements the 'reduce to subset' operation as defined in
        the Delta Debugging algorithm in:
         - 'Finding Failure Causes through Automated Testing'
            by Holger Cleve and Andreas Zeller
        The set of elements passed is divided into nr_of_subsets equally
        sized subsets. (If nr_of_subsets does not divide the number of
        elements without remainder, the first r subsets have one element more
        than the other subsets if r is the remainder.)
        For each subset, we check if it still fails the test. If it still 
        fails the test, the subset is our new starting point and we call
        ddmin2 with this subset. ddmin2 tries to reduce the subset
        further. If all subsets pass the test we return 'None', indicating
        this fact to the caller.

        @param elements: A list of elements that should be minimized.
        @type elements: list<some_type>
        @param nr_of_subsets: This method divides the passed set of elements
               into nr_of_subsets parts.
        @type nr_of_subsets: int
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: 'None' if all of the subsets passed the test, so if trying
                 all subsets failed, otherwise the subset that is still fails
                 the test, maybe further reduced by applying ddmin2 on it.
        @rtype: list<some_type>
        """

        # printing some logging information:
        msg = "try_subsets(" + self._min_target.get_string_rep(elements)
        msg += ", %d);" % nr_of_subsets
        self._log(msg, spaces)

        step_size = int(math.floor(len(elements) / nr_of_subsets))
        reminder = len(elements) % nr_of_subsets
        first = 0
        last = -1
        # for all subsets:
        for i in range(0, nr_of_subsets):
            # calculate the elements of the subset. The first remainder
            # subsets have step_size+1 elements, all other subsets have
            # step_size elements:
            first = last + 1
            last = first + step_size - 1
            if reminder > 0:
                last += 1
                reminder -= 1
            
            subset = elements[first:last+1]

            # check if the subset still fails the test:
            if not self.test_function(subset, spaces + 2):
                # if it still fails the test we try to minimize the subset
                # further by again applying ddmin2:
                msg = " GREAT, but maybe we can reduce the set even further:"
                self._log(msg, spaces)
                return self._ddmin2(subset, 2, spaces + 2)
            
        # if we could not find any subset that still fails the test, we
        # return 'None' indicating that fact to the caller:
        return None



    def _try_complements(self, elements, nr_of_subsets, spaces):
        """
        Implements the 'reduce to complement' operation.

        This method implements the 'reduce to complement' operation as
        defined in the Delta Debugging algorithm in:
         - 'Finding Failure Causes through Automated Testing'
            by Holger Cleve and Andreas Zeller
        The set of elements passed is divided into nr_of_subsets equally
        sized complement-subsets. The subsets are the complements of the
        subsets calculated in try_subsets, so for i = 1..nr_of_subsets we ca
        say:
         - complement_subset_i = all_elements \ subset_i
        For each complement-subset, we check if it still fails the test.
        If it still fails the test, the complement-subset is our new
        starting point and we call ddmin2 with this complement-subset. ddmin2
        tries to reduce the complement-subset further. If all complement-
        subsets pass the test we return None, indicating this fact to the
        caller.

        @param elements: A list of elements that should be minimized.
        @type elements: list<some_type>
        @param nr_of_subsets: This method divides the passed set of elements
               into nr_of_subsets complement-subsets.
        @type nr_of_subsets: int
        @param spaces: The number of spaces to put in front of all logging
               entries, so this argument allows us to produce a nice-to-read
               logfile.
        @type spaces: int
        @return: 'None' if all of the complement-subsets passed the test, so
                 if trying all complement-subsets failed, otherwise the
                 complement-subset that is still fails the test, maybe further
                 reduced by applying ddmin2 on it.
        @rtype: list<some_type>
        """

        # printing some logging information:
        msg = "try_complements(" + self._min_target.get_string_rep(elements)
        msg += ", %d);" % nr_of_subsets
        self._log(msg, spaces)

        step_size = int(math.floor(len(elements) / nr_of_subsets))
        reminder = len(elements) % nr_of_subsets
        first = 0
        last = -1
        # for all parts:
        for i in range(0, nr_of_subsets):
            # calculate the index-range for the elements which are NOT in the
            # subset first: (This is done in exactly the same way as within
            # try_subsets.)
            first = last + 1
            last = first + step_size - 1
            if reminder > 0:
                last += 1
                reminder -= 1

            # The complement subset contains all elements except for the
            # elements[first:last+1]:
            complement_subset = elements[:first]
            complement_subset.extend(elements[last+1:])

            # check if the complement-subset still fails the test:
            if not self.test_function(complement_subset, spaces + 2):
                # if it still fails the test we try to minimize the subset
                # further by again applying ddmin2:
                msg = " GREAT, but maybe we can reduce the set even further:"
                gran = max(2, nr_of_subsets-1)
                return self._ddmin2(complement_subset, gran, spaces + 2)

        # if we could not find any complement-subset that still is not
        # realizable, we return 'undef' indicating that fact to the caller:
        return None

class SimpleMinimizer(Minimizer):
    """
    Implements a simple minimization algorithm.

    This class implements a simple minimization algorithm. It is used:
     - 'Diagnostic Information for Realizability' by
       A. Cimatti, M. Roveri, V. Schuppan, and A. Tchaltsev; VMCAI08
    This class can be used to find the minimal input to a function test()
    that still fails the test (i.e., test(input)=false). This class can be
    used with arbitrary inputs and arbitrary implementations of the function
    'test'. It works with some implementation of the L{MinTarget} interface
    which implements some concrete test() function.

    The simple minimization algorithm is just implemented to be able
    to compare the performance of the delta debugging algorithm.

    If a log_file_name is passed to the constructor, all steps performed by
    the delta debugging algorithm as well as performance measures are witten
    to this file.

    @see: L{DeltaDebugger}
    @see: L{MinTarget}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, min_target, log_file_name):
        """
        Constructor

        @param min_target: Some implementation of the interface L{MinTarget}.
               This implementation implements a concrete test() function.
        @type min_target: L{MinTarget}
        @param log_file_name: A file to write log entries to, or None if no
               log file whould be written.
        @type log_file_name: string
        """

        Minimizer.__init__(self, min_target, log_file_name)


    def minimize(self, all_elements):
        """
        Implements a simple minimization algorithm.

        This method implements a simple minimization algorihm. One element
        is removed after the other. If the test is passed with the reduced
        set of elements, removing the element is undone.
        Logging information that allows to trace what the algorithm actually
        did is written to the log file.

        @param all_elements: A list of elements that should be minimized.
        @type all_elements: list<some_type>
        @return: A list containing the minimal subset of all_elements which
                 makes the function test() fail.
        @rtype: list<some_type>
        """

        # copy the list
        result = all_elements[:]

        # try to remove one element after the other:
        for elem in all_elements:
            tmp = result[:]
            tmp.remove(elem)
            if not self.test_function(tmp, 2):
              result = tmp

        return result

class ApproxMinimizer(Minimizer):
    """
    Implements a minimization algorithm exploiting approximations.

    This class implements a minimization algorithm that uses an
    overapproximation of the test-function according to which the set should
    be minimized. It proceeds in two steps. In the first step it minimizes the
    set with the delta debugging algorithm with respect to the
    overapproximation of the test-function. This gives an overapproximation of
    the result. In the second step, the overapproximation is minimized with the
    exact test-function yielding the final result. Since the overapproximation
    of the test-function is faster than the original test function, this two
    step approach has a better performance.

    If a log_file_name is passed to the constructor, all steps performed by
    the delta debugging algorithm as well as performance measures are witten
    to this file.

    @see: L{DeltaDebugger}
    @see: L{MinTarget}
    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, min_target, log_file_name):
        """
        Constructor

        @param min_target: Some implementation of the interface L{MinTarget}.
               This implementation implements a concrete test() function.
        @type min_target: L{MinTarget}
        @param log_file_name: A file to write log entries to, or None if no
               log file whould be written.
        @type log_file_name: string
        """

        Minimizer.__init__(self, min_target, log_file_name)

        #: A delta debugger used for the first minimization step.
        #: @type: L{DeltaDebugger}
        self.__delta = DeltaDebugger(min_target, log_file_name)

        #: A simple minimizer used for the first minimization step.
        #: @type: L{SimpleMinimizer}
        self.__simple = SimpleMinimizer(min_target, log_file_name)

        #: Some statistics collected between the two steps.
        #: @type: string
        self.__first_step_stat = ""

    def minimize(self, all_elements):
        """
        Implements a minimization algorithm exploiting approximations.

        This method implements a minimization algorithm that uses an
        overapproximation of the test-function according to which the set should
        be minimized. It proceeds in two steps. In the first step it minimizes
        the set with the delta debugging algorithm with respect to the
        overapproximation of the test-function. This gives an overapproximation
        of the result. In the second step, the overapproximation is minimized
        with the exact test-function yielding the final result. Since the
        overapproximation of the test-function is faster than the original
        test function, this two step approach has a better performance.

        @param all_elements: A list of elements that should be minimized.
        @type all_elements: list<some_type>
        @return: A list containing the minimal subset of all_elements which
                 makes the function test() fail.
        @rtype: list<some_type>
        """

        starttime = time.clock()

        # checking if the approximation works at all
        approx_real = self._min_target.test_over_approx(all_elements, 0)
        if approx_real:
            # The approximation is to coarse for this specification, hence,
            # we apply the minimization without approximation
            self._remember_statistics(all_elements, time.clock() - starttime)
            self.__delta.test_function = self._min_target.test_approx_first_slim
            return self.__delta.minimize(all_elements)

        # Step 1: Minimization with the overapproximation of the test function:
        self.__delta.test_function = self._min_target.test_over_approx
        approx_result = self.__delta.minimize(all_elements)
        self._remember_statistics(approx_result, time.clock() - starttime)

        # Step 2: Minimization with the exact test function:
        final_result = self.__simple.minimize(approx_result)
        return final_result

    def _remember_statistics(self, approx_result, time_needed):
        """
        Stores statistic information in self.__first_step_stat.

        @param approx_result: The result of the first minimization step.
        @type approx_result: list<some_type>
        @param time_needed: The time needed for the first minimization step.
        @type time_needed: float
        """

        msg = self._min_target.get_reduction_statistics(approx_result)
        msg += "  time for approximation: %.2f seconds\n" % time_needed
        self.__first_step_stat = msg

    def _create_log_msg(self, result, time_needed):
        """
        Creates a log message containing performance measures.

        @param result: The minimization result.
        @type result: list<some_type>
        @param time_needed: The time needed for minimization.
        @type time_needed: float
        @return: A log message containing performance measures.
        @rtype: string
        """

        msg = " Some statistics:\n"
        msg += self._min_target.get_min_statistics(result)
        msg += "  time for minimization: %.2f seconds\n" % time_needed
        msg += "  Details to the first step:\n "
        # indenting self.__first_step_stat by one more space:
        msg += self.__first_step_stat.replace("\n", "\n ")[0:-1]
        return msg