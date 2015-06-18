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
Contains the entry point for all specification debugging features.
"""

from spec_debug_utils import SpecDebugUtils, PLog
from interactive_game import InteractiveGame
from counterstrategy_computer import CounterstrategyComputer
from path_finder import PathFinder
from countertrace_finder import CountertraceFinder
from sat_solver import SatSolver
from rat_min_target import RatMinTarget, RatMinTargetOverApprox
from rat_min_target import GR1Sect, RatMinTargetQuantifyProduct
from minimizer import DeltaDebugger, SimpleMinimizer, ApproxMinimizer
from diagnoses_finder import DiagnosesFinder
import time
import os
import re

class SpecDebugger(object):
    """
    The entry point for all specification debugging features.

    This class and its method 'debug' is the entry point for all
    specification debugging features provided by Marduk. Five main features
    are implemented so far in the following classes:

    L{SatSolver}:
    This class is able to check if a specification is satisfiable.

    L{DeltaDebugger}:
    This class implements the Delta Debugging algorithm for the
    specification of the system as introduced in
     - 'Finding Failure Causes through Automated Testing' by
       Holger Cleve and Andreas Zeller.
    Information can also be found at:
     - www.st.cs.uni-sb.de/dd/
    Delta Debugging answers the following question:
    'Which formulas of my specification can I leave out while still
    having the same problem (in our case unrealizability) in my
    specification?'. The idea is then to find the problem in the simpler
    specification much faster, because all formulas that are irrelevant
    for that problem have been removed.

    L{CounterstrategyComputer}:
    This class is able to compute a counterstrategy for an unrealizable
    specification. A counterstrategy is a strategy for the environment.
    If the environment adheres to it, no behaviour of the system can
    implement the specification.

    L{CountertraceFinder}:
    This class is able to heuristically search for a countertrace, i.e.,
    for a FIXED sequence of input values, so that the system is not able
    to fulfill the specification no matter how it behaves. Of course
    such a fixed sequence of inputs is a much simpler explanation for
    unrealizability than a sequence of inputs which is dependent on
    previous outputs.

    L{InteractiveGame}:
    This class implements an interactive game between the computer in
    the role of the environment and the user in the role of the system.
    In every time step, the environment first gives next inputs to the
    system. Then the user is asked to choose the next values of the
    output variables. The game is won for the user if she manages to
    fulfill all the fairness conditions of the system infinitely often
    or if the environment does not fulfill all its fairness constraints.

    L{PathFinder}:
    This module is able to calculate all states and all state transitions
    which are feasible in the interactive game implemented in
    L{InteractiveGame}. All states and state transitions are visualized as a
    graph. The L{PathFinder} is able to create a description of the
    graph in DOT format.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, marduk):
        """
        Constructor

        @param marduk: The main object of Marduk as it contains all command
               line options and data.
        @type marduk: L{Marduk}
        """

        #: The main object of Marduk
        #: @type: L{Marduk}
        self.__marduk = marduk

        #: Flag for enabling the computation of diagnoses.
        #:
        #: True if diagnoses should be computed, False otherwise.
        #: @type: bool
        self.__compute_diagnoses = True

        #: Flag for using one diagnoses-conflict computation for the game.
        #:
        #: True if a diagnoses-conflict should be used for the game, False
        #: otherwise.
        #: @type: bool
        self.__use_diagnoses_conflict = True

        #: The maximal number of diagnoses to compute.
        #:
        #: The maximal number of diagnoses to compute or None if all diagnoses
        #: should be computed.
        #: @type: int
        self.__max_diagnoses = None

        #: The maximal number of elements in any diagnosis.
        #:
        #: The maximal number of elements in any diagnosis or None if there is
        #: no upper bound for the number of elements in diagnoses.
        #: @type: int
        self.__max_diagnosis_elements = None

        #: Flag for enabling minimization.
        #:
        #: True if minimization should be performed, False otherwise.
        #: @type: bool
        self.__apply_minimization = True

        #: Flag for enabling variable minimization when minimizing.
        #:
        #: True if variables should be minimized, False otherwise.
        #: @type: bool
        self.__minimize_vars = True

        #: Flag for using the minimization result.
        #:
        #: True if the minimization result should be used, False otherwise.
        #: @type: bool
        self.__use_min_result = True

        #: Flag for performing trivial minimization.
        #:
        #: True if the trivial minimization should be performed, False
        #: otherwise.
        #: @type: bool
        self.__do_trivial_minimization = True

        #: Flag for performing trivial minimization.
        #:
        #: True if the delta debugging minimization should be performed, False
        #: otherwise.
        #: @type: bool
        self.__do_delta_debugging = True

        #: Flag for performing a satisfiability check.
        #:
        #: True if a satisfiability check should be performed, False otherwise.
        #: @type: bool
        self.__check_sat = True

        #: Flag for computing a countertrace.
        #:
        #: True if a countertrace should be computed, False otherwise.
        #: @type: bool
        self.__check_for_countertrace = True

        #: Flag for using the countertrace.
        #:
        #: True if the countertrace should be used, False otherwise.
        #: @type: bool
        self.__use_countertrace = True

        #: Flag for computing a summarizing graph.
        #:
        #: True if a summarizing graph should be computed, False otherwise.
        #: @type: bool
        self.__compute_graph = True

        #: Flag for playing an interactive debugging game.
        #:
        #: True if the interactive debugging game should be played, False
        #: otherwise.
        #: @type: bool
        self.__play_game = True

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = SpecDebugUtils(marduk)


    def debug(self, debug_mode):
        """
        Debugs an unrealizable specification.

        This method is the entry point for all specification debugging
        features Marduk provides. Dependent on the string passed as debug_mode,
        certain features are activated. debug_mode can contain certain
        substrings, each activating a certain feature. The substrings and
        their effects are:
         - D:    compute diagnoses (experimental)
         - Du:   compute diagnoses (experimental), use a conflict in the game
         - m<i>: compute at most <i> diagnoses (e.g. m42)
         - e<i>: compute only diagnoses with at most <i> elements (e.g. e42)
         - M:    minimize the specification, i.e, compute an unrealizable core
         - Mu:   minimize the specification, use result
         - v:    also minimize output variables when minimizing
         - t:    compare minimization to trivial minimization
         - d:    compare minimization to simple delta debugging
         - S:    check for satisfiability
         - T:    search for countertrace
         - Tu:   search for countertrace and use it
         - G:    compute graph that summarizes all plays
         - P:    play the interactive game
         - The default debug mode is 'MuvSTuGP'

        @param debug_mode: a string that says which debugging features should
               be used (as described above).
        @type debug_mode: string
        """

        self._parse_debug_mode(debug_mode)

        # make a directory to put all output files to, if it does not exist
        # already:
        if not os.path.isdir("./spec_debug_results/"):
            os.mkdir("./spec_debug_results/")

        # initialize the performance logger:
        PLog.set_log_file("./performance.log")


        # -------------------------- Satisfiability -------------------------
        # checking if specification is satisfiable:
        if self.__check_sat:
            self._check_sat()

        # ---------------------------- Diagnoses ----------------------------
        # computing diagnoses as suggested in
        # 'R. Reiter: A Theory of Diagnosis from First Principles'
        if self.__compute_diagnoses:
            self._compute_diagnoses()


        # --------------------------- Minimization --------------------------
        # we try to reduce the unrealizable specification by computing an
        # unrealizable core:
        if self.__apply_minimization and not self.__use_diagnoses_conflict:
            self._apply_min()
  
  
        # ------------------------ Counterstrategy --------------------------
        # computing a counterstrategy which is able to find inputs, so that 
        # the system is always forced to violate the  specification:
        (counterstrategy, z_array) = self._compute_counterstrategy()
  
        # Just a fix: The grammar allows things like:
        #  G((var=1) -> FALSE);
        # The bdd says nothing about the next values of var, it only says 
        # that the current value of var must not be 0. This might become a
        # problem in games and graph computation. We might have to choose
        # the next value of var. The bdd says: 'of course you can set the
        # next value of var to 1'. In the next step however it says that
        # this was not right. Therefore we add all restrictions on present
        # vars to next vars as well:
        # (When nusmv is used as parser, this method is not necessary.)
        self.__utils.secure_transition_relations();
  
        # ------------------------- Countertrace ---------------------------- 
        # searching for a countertrace, i.e., for a FIXED sequence of input 
        # values, so that the system is not able to fulfill the specification
        # no matter how it behaves:
        countertrace = None
        if self.__check_for_countertrace:
            countertrace = self._search_for_countertrace(counterstrategy)

        # ---------------------- Summarizing Graph --------------------------
        # computing a graph in DOT-format that summarizes all plays that are
        # possible if the environment adheres to the counterstrategy or the
        # countertrace calculate above:
        if self.__compute_graph:
            self._compute_graph(counterstrategy, z_array, countertrace)
  
        # ---------------------- Interactive Game ---------------------------
        # playing the interactive game between the user in the role of the 
        # system and the computer applying the counterstrategy (or the
        # countertrace):
        if self.__play_game:
            self._play_game(counterstrategy, z_array, countertrace)


        # closing the performance logger:
        PLog.close()


    def _parse_debug_mode(self, debug_mode):
        """
        Parses the debug mode string.

        This method parses the debug_mode string passed to the debug()-
        method. debug_mode can contain certain substrings, each activating a
        certain feature. The substrings and their effects are:
         - D:    compute diagnoses (experimental)
         - Du:   compute diagnoses (experimental), use a conflict in the game
         - m<i>: compute at most <i> diagnoses (e.g. m42)
         - e<i>: compute only diagnoses with at most <i> elements (e.g. e42)
         - M:    minimize the specification, i.e, compute an unrealizable core
         - Mu:   minimize the specification, use result
         - v:    also minimize output variables when minimizing
         - t:    compare minimization to trivial minimization
         - d:    compare minimization to simple delta debugging
         - S:    check for satisfiability
         - T:    search for countertrace
         - Tu:   search for countertrace and use it
         - G:    compute graph that summarizes all plays
         - P:    play the interactive game
         - The default debug mode is 'MuvSTuGP'

        @param debug_mode: a string that says which debugging features should
               be used (as described above).
        @type debug_mode: string
        """

        if debug_mode.find("S") < 0:
            self.__check_sat = False
        if debug_mode.find("Du") < 0:
            self.__use_diagnoses_conflict = False
        if debug_mode.find("D") < 0:
            self.__compute_diagnoses = False
        if debug_mode.find("m") >= 0:
            occ = re.compile('m[0-9]+').findall(debug_mode)
            if occ:
                self.__max_diagnoses = int(occ[0][1:])
        if debug_mode.find("e") >= 0:
            occ = re.compile('e[0-9]+').findall(debug_mode)
            if occ:
                self.__max_diagnosis_elements = int(occ[0][1:])
        if debug_mode.find("Mu") < 0:
            self.__use_min_result = False
        if debug_mode.find("M") < 0:
            self.__apply_minimization = False
        if debug_mode.find("v") < 0:
            self.__minimize_vars = False
        if debug_mode.find("t") < 0:
            self.__do_trivial_minimization = False
        if debug_mode.find("d") < 0:
            self.__do_delta_debugging = False
        if debug_mode.find("Tu") < 0:
            self.__use_countertrace = False
        if debug_mode.find("T") < 0:
            self.__check_for_countertrace = False
        if debug_mode.find("G") < 0:
            self.__compute_graph = False
        if debug_mode.find("P") < 0:
            self.__play_game = False
        print "debug mode is: %s" % debug_mode
        print "   computeDiagnoses = %d" % self.__compute_diagnoses
        print "   useDiagnosisConflict = %d" % self.__use_diagnoses_conflict
        print "   maxDiagnoses = " + str(self.__max_diagnoses)
        print "   maxDiagnosisElements = " + str(self.__max_diagnosis_elements)
        print "   applyMinimization = %d" % self.__apply_minimization
        print "   minimizeVars = %d" % self.__minimize_vars
        print "   useMinResult = %d" % self.__use_min_result
        print "   doTrivialMinimization = %d" % self.__do_trivial_minimization
        print "   doDeltaDebugging = %d" % self.__do_delta_debugging
        print "   checkSat = %d" % self.__check_sat
        print "   checkForCountertrace = %d" %self.__check_for_countertrace
        print "   useCountertrace = %d" % self.__use_countertrace
        print "   computeGraph = %d" % self.__compute_graph
        print "   playGame = %d" % self.__play_game


    def _compute_diagnoses(self):
        """
        Computes diagnoses for an unrealizable specification.

        This method uses the module L{DiagnosesFinder} to compute diagnoses for
        the unrealizable specification following the ideas in
        'R. Reiter: A Theory of Diagnosis from First Principles'
        """

        print "-------------------- Diagnoses ------------------"

        # We create a dictionary that tells the Minimizer which parts of the
        # specification it should minimize:
        minimize = {}
        minimize[GR1Sect.OUT_VARS] = self.__minimize_vars
        minimize[GR1Sect.SYS_TRANS] = True
        minimize[GR1Sect.SYS_FAIR] = True

        # Creating the components needed for diagnoses computation:
        min_target = RatMinTargetOverApprox(self.__utils, minimize, \
                     self.__use_diagnoses_conflict,
                     "./spec_debug_results/conflict.xml")
        minimizer = ApproxMinimizer(min_target, None)
        diagnoses_finder = DiagnosesFinder(self.__utils, minimizer, min_target,
                           self.__max_diagnosis_elements, self.__max_diagnoses)

        print "Computing diagnoses ..."
        diagnoses_finder.start()

        # Writing some result files:
        diagnoses_finder.write_diagnoses("./spec_debug_results/diagnoses.txt")
        print " Diagnoses were written to ./spec_debug_results/diagnoses.txt."
        diagnoses_finder.write_conflicts("./spec_debug_results/conflicts.txt")
        print " Conflicts were written to ./spec_debug_results/conflicts.txt."
        diagnoses_finder.write_hstree_dot("./spec_debug_results/hstree.dot")
        print " The HSTree was written to ./spec_debug_results/hstree.dot."
        print "   You can produce a picture of the HSTree by typing:"
        print "      'dot -Tpdf -o ./hstree.pdf ./hstree.dot'"
        print "   for example."

        if not self.__use_diagnoses_conflict:
            return

        diagnoses_finder.use_conflict(0)
        print " I will use the first conflict in",
        print "./spec_debug_results/conflicts.txt for all subsequent steps."
        print " That is, I will use a counterstrategy to illustrate this",
        print "conflict to you in an interactive game."
        print " The conflict has been written in form of a specification",
        print "to ./spec_debug_results/conflict.xml."        

    def _apply_min(self):
        """
        Computes an unrealizable core.

        This method uses the module L{DeltaDebugger} to minimize the
        unrealizable specification.
        """

        print "------------------ Minimization -----------------"

        # We create a dictionary that tells the Minimizer which parts of the
        # specification it should minimize:
        minimize = {}
        minimize[GR1Sect.OUT_VARS] = self.__minimize_vars
        minimize[GR1Sect.SYS_TRANS] = True
        minimize[GR1Sect.SYS_FAIR] = True

        if self.__do_trivial_minimization:
            print "Minimizing the spec with the trivial approach ..."
            print "  (this is just done for evaluating the performance",
            print    "of the fully optimized minimization)"
            target = RatMinTarget(self.__utils, minimize, False,
                                  "spec_debug_results/simple.xml")
            minimizer = SimpleMinimizer(target, "spec_debug_results/simple.log")
            minimizer.start()
            print " The minimal spec that is still unrealizable was written",
            print "to ./spec_debug_results/simple.xml."
            print " A log of what the simple minimizer did was written to",
            print "./spec_debug_results/simple.log.\n"

        if self.__do_delta_debugging:
            print "Minimizing the spec with the delta debugging algorithm ..."
            print "  (this is just done for evaluating the performance",
            print    "of the fully optimized minimization)"
            target = RatMinTarget(self.__utils, minimize, False,
                                  "spec_debug_results/delta.xml")
            minimizer = DeltaDebugger(target, "spec_debug_results/delta.log")
            minimizer.start()
            print " The minimal spec that is still unrealizable was written",
            print "to ./spec_debug_results/delta.xml."
            print " A log of what the simple minimizer did was written to",
            print "./spec_debug_results/delta.log.\n"

        print "Minimizing the unrealizable specification, i.e, computing an",
        print "unrealizable core ..."

        target = RatMinTargetOverApprox(self.__utils, minimize,
                 self.__use_min_result, "spec_debug_results/unreal_core.xml")
        mini = ApproxMinimizer(target, "spec_debug_results/unreal_core.log")

        #self.__utils.disable_dyn_reordering()
        mini.start()
        #self.__utils.enable_dyn_reordering()

        print " The minimal spec that is still unrealizable was written",
        print "to ./spec_debug_results/unreal_core.xml."
        print " A log of what the delta debugger did was written to",
        print "./spec_debug_results/unreal_core.log."
        if self.__use_min_result:
            print " FOR ALL FURTHER ANALYSIS, I WILL USE THE MINIMIZED",
            print "SPECIFICATION IN ./spec_debug_results/unreal_core.xml!!!"
            return
        print " FOR ALL FURTHER ANALYSIS, I WILL USE THE ORIGINAL",
        print "(not the minimized) SPECIFICATION!!!"
        

    def _check_sat(self):
        """
        Checks for satisfiability.

        This method checks with the help of the L{SatSolver} if the
        specification satisfiable or not.
        """
        print "----------------- Satisfiability ----------------"
        starttime = time.clock()
        sat_solver = SatSolver(self.__utils)
        sat = sat_solver.is_satisfiable()
        PLog.log(" checking satisfiability took ")
        PLog.log("%.2f seconds\n" % (time.clock() - starttime))
        if sat:
            PLog.log("The specification IS satisfiable\n")
        else:
            PLog.log("The specification is NOT satisfiable\n")

    def _compute_counterstrategy(self):
        """
        Computes a counterstrategy.

        This method computes a counterstrategy for an unrealizable
        specification.

        @return: A tuple (counterstrategy, z_array) where:
                  - counterstrategy is a strategy for the environment to find
                    inputs so that the system is forced to violate the
                    specification.
                  - z_array[a] are the intermediate results of the fixpoint
                    computation in the variable Z of the computation of the
                    winning region for the environment. 'a' counts the
                    iteration of the fixpoint computation in Z. It is used to
                    figure out how often the value of jx might still change in
                    the future. (If the play is in z_array[a], jx might change
                    at most a-1 times.)
        @rtype:(L{BDD}, list<L{BDD}>)
        """

        print "----------------- Counterstrategy ---------------"
        print "Calculating the winning region for the environment ..."
        counter = CounterstrategyComputer(self.__utils)
        starttime = time.clock()
        (Z, z_array, y_array, x_array) = counter.winm_env(True)

        PLog.log(" Computing the winning region for environment took ")
        PLog.log("%.2f seconds\n" % (time.clock() - starttime))

        print "Calculating the counterstrategy ..."
        starttime =  time.clock()
        counterstrategy = counter.strategy_env_fast(z_array, y_array, x_array)
        PLog.log(" Computing the counterstrategy took ")
        PLog.log("%.2f seconds\n" % (time.clock() - starttime))

        if not (self.__utils.init <= Z):
            self.__utils.env_init *= Z
            self.__utils.sys_init *= Z
            print "  The system is realizable from some of the initial states "
            print "   but not from all. I will start the countergame in one of "
            print "   the states from which the specification cannot be "
            print "   implemented."

        return (counterstrategy, z_array)


    def _search_for_countertrace(self, counterstrategy):
        """
        Heuristically searches for a countertrace.

        This method uses the module L{CountertraceFinder} to search for
        a countertrace. This is a FIXED sequence of input values, so that the
        system is not able to fulfill the specification no matter how it
        behaves.

        @param counterstrategy: A counterstrategy, i.e., a strategy for the
               environment to find inputs so that the system is forced to
               violate the specification.
        @type counterstrategy: L{BDD}
        @return: A sequence of inputs so that the system is forced to violate
                 its specification.
        @rtype: L{InfiniteTraceOfBdds}
        """

        print "------------------- Countertrace ----------------"
        print "Searching heuristically for a countertrace ..."
        tracer_finder = CountertraceFinder(self.__utils)
        starttime =  time.clock()
        countertrace = tracer_finder.compute_countertrace(counterstrategy)
        PLog.log(" compute_countertrace took ")
        PLog.log("%.2f seconds\n" % (time.clock() - starttime))

        if not countertrace:
            PLog.log(" Could NOT find a countertrace!\n")
            return None
        
        PLog.log(" Countertrace FOUND\n")
        PLog.log("Countertrace has:\n")
        PLog.log("    length loop: %d \n" % countertrace.loop_length)
        PLog.log("    length stem: %d \n" % countertrace.stem_length)

        print "Printing the trace to ./spec_debug_results/trace.txt ...";
        tracer_finder.print_trace(countertrace)
        if self.__use_countertrace:
            print " FOR ALL FURTHER ANALYSIS, I WILL USE THIS",
            print "COUNTERTRACE!!!"
            return countertrace
        else:
            print " I WILL NOT USE THIS COUNTERTRACE FOR ANY FURTHER",
            print "ANALYSIS!!!"
            return None

    def _compute_graph(self, counterstrategy, z_array, countertrace):
        """
        Computes a summarizing graph.

        This method is able to calculate all states and all state transitions
        which are feasible in the interactive game implemented in
        L{InteractiveGame}. All states and state transitions are visualized
        as a graph. The graph is created in DOT format. The DOT-program can
        then be used to generate pictures of the graph by typing:
         - dot -Tpdf filename.dot -o filename.pdf

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

        print "--------------- Summarizing Graph ---------------"
        print "Computing a graph that summarizes all possible plays ..."
        starttime =  time.clock()

        # 1000 means: abort if graph contains > 1000 states.
        path_finder = PathFinder(self.__utils, counterstrategy,  z_array, \
                                 countertrace, 1000)
        success = path_finder.write_graphs("./spec_debug_results/graph")

        # Printing some statistics:
        if not success:
            PLog.log("Graph contains more than 1000 states -> aborted\n")
            PLog.log(" Computing the graphs took ")
            PLog.log("%.2f seconds\n" % (time.clock() - starttime))
            return

        PLog.log("Nr of states in graph: %d\n" % len(path_finder.get_graph()))
        print "Graphs were written to 'spec_debug_results/graph.dot' and "
        print "  'spec_debug_results/graph_with_signals.dot'"
        print "   You can produce pictures of the graphs by typing:"
        print "      'dot -Tpdf -o ./graph.pdf ./graph.dot'"
        print "   for example."
        print "   Detailed information to the graphs was written to"
        print "   'spec_debug_results/graph.info."
        PLog.log(" Computing the graphs took ")
        PLog.log("%.2f seconds\n" % (time.clock() - starttime))


    def _play_game(self, counterstrategy, z_array, countertrace):
        """
        Performs the interactive debugging game.

        This method performs an interactive game between the computer in
        the role of the environment and the user in the role of the system.
        In every time step, the environment first gives next inputs to the
        system. Then the user is asked to choose the next values of the
        output variables. The game is won for the user if she manages to
        fulfill all the fairness conditions of the system infinitely often
        or if the environment does not fulfill all its fairness constraints.

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

        print "---------------- Interactive Game ---------------"
        print "Lets play a game. I am the environment and you are the"
        print "system. I will give you inputs, you have to choose"
        print "outputs. I will help you by writing possible output values"
        print "in brackets. A log of all variable values in all time "
        print "steps will be printed to 'spec_debug_results/log.txt' after you"
        print "quit with 'Q'. You will see that I will force you to"
        print "violate your specification!"
        game = InteractiveGame(self.__utils, counterstrategy, z_array, \
                               countertrace)
        game.interact()


