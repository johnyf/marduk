#!/usr/bin/env python

##  ===========================================================================
##  Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
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


from optparse import OptionParser
from sys import exit
import resource

from specification import Specification
from winning_region import WinningRegion
from strategy import Strategy
from output_functions import OutputFunctions
from code_generator import CodeGenerator
from code_generator import VerilogGenerator
from code_generator import BlifGenerator
from code_generator import HifGenerator
from code_generator import BlifFromGatesGenerator
from bddwrap import BDD
import marduk_utils
from marduk_utils import MardukException
from nusmv import dd
from spec_debug.spec_debugger import SpecDebugger


class MardukOptions(object):
    def __init__(self):
        self.input_file = "input.xml"
        self.output_file = "marduk_out"
        self.mode = None
        self.language = None
        self.partition = None
        self.dyn_reorder = False
        self.reorder1 = False
        self.reorder2 = False
        self.kill = False
        self.one_hot = False
        self.verbose = 0
        self.reorder_method = "SIFT_CONV"
        self.dyn_reorder_method = "SIFT"
        self.dac04 = False
        self.dac_search_mode = None
        self.dac_recur_limit = None
        self.dac_call_limit = None
        self.debug_mode = "DuvtSTuGP"
        self.num_class_vectors = 1024
        self.update_sigs_size = 32
        self.cache_size = None
        self.dont_care_upper_bound = False
        self.check_combinations = False
        self.transfer_functions = False

class Marduk(object):
    """
    This is the main class of the Marduk implementation. It is the main start of control flow.
    Furthermore it stores global options, parameters, and other objects and provides appropriate
    access methods.
    """    


    def __init__(self, options, args):
        """
        Marduk constructor. Analyzes and stores options.
        """

        self.__options = options
        self.__args = args

         # Initialize DD manager for synthesis.
        from nusmv import dd
        self.__dd_manager = dd.create_dd_manager(0,0,251,131071,0)  # Values from PerlDD


        self.__printed_lines = ["This file was automatically synthesized with Marduk.",
                                "Information on the synthesis process is displayed below.",
                                "---------------------------------------------------------------------------\n"]

        
        if options.input_file == None:
            self.println("WARNING: No input file specified! Using 'input.xml' as default input file!")
            self.__input_file = "input.xml"
        else:
            self.__input_file = options.input_file
                
        if options.output_file == None:
            self.println("WARNING: No output file specified! Using 'marduk_out' as default output file!")
            self.__output_file = "marduk_out"
        else:
            self.__output_file = options.output_file
        
        if options.mode == None:
            self.println("WARNING: No mode specified! Using 'cofactor' as default!")
            self.__mode = marduk_utils.Modes.COFACTOR
        elif options.mode.lower() == "cofactor":
            self.__mode = marduk_utils.Modes.COFACTOR
        elif options.mode.lower() == "irrsop":
            self.__mode = marduk_utils.Modes.IRRSOP
        elif options.mode.lower() == "factor":
            self.__mode = marduk_utils.Modes.FACTOR
        elif options.mode.lower() == "old":
            self.__mode = marduk_utils.Modes.OLD
            self.println("WARNING: In 'OLD' mode, the language setting will be ignored. Output will be in BLIF format.")
        else:
            self.println("WARNING: Unknown mode: '" + options.mode + \
                "'! Using 'cofactor' as default!")
            self.__mode = marduk_utils.Modes.COFACTOR
            options.mode = "COFACTOR"

        if options.language == None:
            self.println("WARNING: No language specified! Using 'blif' as default!")
            self.__language = marduk_utils.Languages.BLIF
        elif options.language.lower() == "blif":
            self.__language = marduk_utils.Languages.BLIF
        elif options.language.lower() == "verilog":
            self.__language = marduk_utils.Languages.VERILOG
        elif options.language.lower() == "hif":
            self.__language = marduk_utils.Languages.HIF
        else:
            self.println("WARNING: Unknown language: '" + options.language + \
                "'! Using 'blif' as default!")
            self.__language = marduk_utils.Languages.BLIF
            options.language = "BLIF"


        if options.transfer_functions and not self.__mode in (marduk_utils.Modes.COFACTOR, marduk_utils.Modes.OLD):
            self.println("WARNING: Cannot use 'transfer' option in '%s' mode. Will be ignored!" % options.mode)
            options.transfer_functions = False
            
        # Handle options concerning IrrSOP (cache)
        try:
            self.__num_class_vectors = int(options.num_class_vectors)
        except ValueError:
            self.println("WARNING: Given number of class-vectors '" + options.num_class_vectors + "' is not an integer.")
            self.println("         Using '1024' as default!")
            self.__num_class_vectors = 1024

        try:
            self.__update_sigs_size = int(options.update_sigs_size)
        except ValueError:
            self.println("WARNING: Given number for update signatures '" + options.update_sigs_size + "' is not an integer.")
            self.println("         Using '32' as default!")
            self.__update_sigs_size = 32
            
        try:
            self.__cache_size = int(options.cache_size)
        except TypeError:
            if not options.cache_size:
                self.__cache_size = None
            else:
                raise Exception("Unexpected TypeError for argument --cache-size='%s'." % options.cache_size)
        except ValueError:
            self.println("WARNING: Given cache size '" + options.cache_size + "' is not an integer.")
            self.println("         Using 'None' (=no limit) as default!")
            self.__cache_size = None

        self.__dont_care_upper_bound = options.dont_care_upper_bound
            
        # The following are not handled yet!    
        self.__check_combinations = options.check_combinations
        # Missing: option to set threshold for signature update

        
        
        if options.partition == None:
            self.__partition = None
        elif options.partition.lower() == "threshold":
            self.__partition = "Threshold"
        elif options.partition.lower() == "monolithic":
            self.__partition = "Monolithic"
        elif options.partition.lower() == "Iwls95CP".lower():
            self.__partition = "Iwls95CP"
        else:
            self.println("WARNING: Unknown partition method: '%s'! Using 'None' as default!" % options.partition)
            self.__partition = None

        try:
            self.__verbose = int(options.verbose)
        except ValueError:
            self.println("WARNING: Given verbose level '" + options.verbose + "' is not an integer.")
            self.println("         Using '0' as default!")
            self.__verbose = 0

        if options.dac_recur_limit and options.dac04:
            try:
                self.__dac_recur_limit = int(options.dac_recur_limit)
            except ValueError:
                self.println("WARNING: Given dac-recur-limit '" + options.verbose + "' is not an integer.")
                self.println("         Using '5' as default!")
                self.__dac_recur_limit = 5
        else:
            self.__dac_recur_limit = None

            
        if options.dac_call_limit and options.dac04:
            try:
                self.__dac_call_limit = int(options.dac_call_limit)
            except ValueError:
                self.println("WARNING: Given dac-call-limit '" + options.verbose + "' is not an integer.")
                self.println("         Using '10' as default!")
                self.__dac_call_limit = 10
        else:
            self.__dac_call_limit = None

        if options.dac_search_mode and options.dac04:
            if options.dac_search_mode.lower() in ['dfs', 'bfs']:
                self.__dac_search_mode = options.dac_search_mode
            else:
                self.println("WARNING: Given dac-search-mode '%s' is unknown." % options.dac_search_mode)
                self.println("         Using 'bfs' as default.")
        else:
            if options.dac04:
                self.println("WARNING: No dac-search-mode given. Using 'dfs' as default.")
                self.__dac_search_mode = 'dfs'
            else:
                self.__dac_search_mode = None

                
        if (not options.dac04) and options.dac_search_mode != None:
            self.println("WARNING: Specified a dac-search-mode, but '--dac04' was not given.")
            self.println("         The given mode will be ignored.")
                
        if (options.dac_recur_limit and (not options.dac04 or self.__dac_search_mode != 'dfs')):
            self.println("WARNING: A dac-recur-limit was given, but program is not in DAC04-DFS mode.")
            self.println("         The given limit will be ignored.")

        if (options.dac_call_limit and (not options.dac04 or self.__dac_search_mode != 'bfs')):
            self.println("WARNING: A dac-call-limit was given, but program is not in DAC04-BFS mode.")
            self.println("         The given limit will be ignored.")
            
        if options.dac04:
            if self.__dac_search_mode == 'dfs' and self.__dac_recur_limit == None:
                self.println("WARNING: Using DAC'04 in DFS mode without a recursion limit!")
                self.println("         Run time and memory consumption might become very high!")
            if self.__dac_search_mode == 'bfs' and self.__dac_call_limit == None:
                self.println("WARNING: Using DAC'04 in BFS mode without a call limit!")
                self.println("         Run time and memory consumption might become very high!")                
                
                         
            
        # Propagate necessary options to NuSMV
        from nusmv import opt
        from nusmv import dd
        from nusmv import game
        import re

        opt.set_batch(opt.OptsHandler_get_instance())
        opt.set_verbose_level(opt.OptsHandler_get_instance(), self.__verbose)
        print "marduk game mode: ", game.opt_game_game(opt.OptsHandler_get_instance())
        game.unset_game_game(opt.OptsHandler_get_instance())
        print "marduk game mode: ", game.opt_game_game(opt.OptsHandler_get_instance())

        # Dealing with reorder method for forced reorderings
        reorder_method = options.reorder_method.upper()
        reorder_method = re.sub('CUDD_','',reorder_method)
        reorder_method = re.sub('REORDER_','',reorder_method)
        reorder_method = re.sub('_CONVERGE','_CONV',reorder_method)

        self.__reorder_method = -1

        if reorder_method == "SAME":
            self.__reorder_method = dd.REORDER_SAME
        elif reorder_method == "NONE":
            self.__reorder_method = dd.REORDER_NONE
        elif reorder_method == "RANDOM":
            self.__reorder_method = dd.REORDER_RANDOM
        elif reorder_method == "RANDOM_PIVOT":
            self.__reorder_method = dd.REORDER_RANDOM_PIVOT
        elif reorder_method == "SIFT":
            self.__reorder_method = dd.REORDER_SIFT
        elif reorder_method == "SIFT_CONV":
            self.__reorder_method = dd.REORDER_SIFT_CONV
        elif reorder_method == "SYMM_SIFT":
            self.__reorder_method = dd.REORDER_SYMM_SIFT
        elif reorder_method == "SYMM_SIFT_CONV":
            self.__reorder_method = dd.REORDER_SYMM_SIFT_CONV
        elif reorder_method == "WINDOW2":
            self.__reorder_method = dd.REORDER_WINDOW2
        elif reorder_method == "WINDOW3":
            self.__reorder_method = dd.REORDER_WINDOW3
        elif reorder_method == "WINDOW4":
            self.__reorder_method = dd.REORDER_WINDOW4
        elif reorder_method == "WINDOW2_CONV":
            self.__reorder_method = dd.REORDER_WINDOW2_CONV
        elif reorder_method == "WINDOW3_CONV":
            self.__reorder_method = dd.REORDER_WINDOW3_CONV
        elif reorder_method == "WINDOW4_CONV":
            self.__reorder_method = dd.REORDER_WINDOW4_CONV
        elif reorder_method == "GROUP_SIFT":
            self.__reorder_method = dd.REORDER_GROUP_SIFT
        elif reorder_method == "GROUP_SIFT_CONV":
            self.__reorder_method = dd.REORDER_GROUP_SIFT_CONV
        elif reorder_method == "ANNEALING":
            self.__reorder_method = dd.REORDER_ANNEALING
        elif reorder_method == "GENETIC":
            self.__reorder_method = dd.REORDER_GENETIC
        elif reorder_method == "LINEAR":
            self.__reorder_method = dd.REORDER_LINEAR
        elif reorder_method == "LINEAR_CONV":
            self.__reorder_method = dd.REORDER_LINEAR_CONVERGE
        elif reorder_method == "EXACT":
            self.__reorder_method = dd.REORDER_EXACT
        else:
            self.println("WARNING: Specified unknown reordering method '%s'! Using NONE as default instead." % options.reorder_method)
            self.__reorder_method = dd.REORDER_NONE


        # Dealing with reorder method for dynamic reorderings
            
        dyn_reorder_method = options.dyn_reorder_method.upper()
        dyn_reorder_method = re.sub('CUDD_','',dyn_reorder_method)
        dyn_reorder_method = re.sub('REORDER_','',dyn_reorder_method)
        dyn_reorder_method = re.sub('_CONVERGE','_CONV',dyn_reorder_method)
        
        self.__dyn_reorder_method = -1

        if dyn_reorder_method == "SAME":
            self.__dyn_reorder_method = dd.REORDER_SAME
        elif dyn_reorder_method == "NONE":
            self.__dyn_reorder_method = dd.REORDER_NONE
        elif dyn_reorder_method == "RANDOM":
            self.__dyn_reorder_method = dd.REORDER_RANDOM
        elif dyn_reorder_method == "RANDOM_PIVOT":
            self.__dyn_reorder_method = dd.REORDER_RANDOM_PIVOT
        elif dyn_reorder_method == "SIFT":
            self.__dyn_reorder_method = dd.REORDER_SIFT
        elif dyn_reorder_method == "SIFT_CONV":
            self.__dyn_reorder_method = dd.REORDER_SIFT_CONV
        elif dyn_reorder_method == "SYMM_SIFT":
            self.__dyn_reorder_method = dd.REORDER_SYMM_SIFT
        elif dyn_reorder_method == "SYMM_SIFT_CONV":
            self.__dyn_reorder_method = dd.REORDER_SYMM_SIFT_CONV
        elif dyn_reorder_method == "WINDOW2":
            self.__dyn_reorder_method = dd.REORDER_WINDOW2
        elif dyn_reorder_method == "WINDOW3":
            self.__dyn_reorder_method = dd.REORDER_WINDOW3
        elif dyn_reorder_method == "WINDOW4":
            self.__dyn_reorder_method = dd.REORDER_WINDOW4
        elif dyn_reorder_method == "WINDOW2_CONV":
            self.__dyn_reorder_method = dd.REORDER_WINDOW2_CONV
        elif dyn_reorder_method == "WINDOW3_CONV":
            self.__dyn_reorder_method = dd.REORDER_WINDOW3_CONV
        elif dyn_reorder_method == "WINDOW4_CONV":
            self.__dyn_reorder_method = dd.REORDER_WINDOW4_CONV
        elif dyn_reorder_method == "GROUP_SIFT":
            self.__dyn_reorder_method = dd.REORDER_GROUP_SIFT
        elif dyn_reorder_method == "GROUP_SIFT_CONV":
            self.__dyn_reorder_method = dd.REORDER_GROUP_SIFT_CONV
        elif dyn_reorder_method == "ANNEALING":
            self.__dyn_reorder_method = dd.REORDER_ANNEALING
        elif dyn_reorder_method == "GENETIC":
            self.__dyn_reorder_method = dd.REORDER_GENETIC
        elif dyn_reorder_method == "LINEAR":
            self.__dyn_reorder_method = dd.REORDER_LINEAR
        elif dyn_reorder_method == "LINEAR_CONV":
            self.__dyn_reorder_method = dd.REORDER_LINEAR_CONVERGE
        elif dyn_reorder_method == "EXACT":
            self.__dyn_reorder_method = dd.REORDER_EXACT
        else:
            self.println("WARNING: Specified unknown dynamic reordering method '%s'! Using NONE as default instead." % options.dyn_reorder_method)
            self.__dyn_reorder_method = dd.REORDER_NONE

            
        if options.dyn_reorder:
            dd.dd_autodyn_enable(dd.cvar.dd_manager, self.__dyn_reorder_method)
            dd.dd_autodyn_enable(self.__dd_manager, self.__dyn_reorder_method)
        else:
            dd.dd_autodyn_disable(dd.cvar.dd_manager)
            dd.dd_autodyn_disable(self.__dd_manager)
        

        if self.__verbose > 0:
            # FIXXME: Format this output more nicely
            self.println("Used the following command line options/parameters:")
            self.println(str(options) + " " +  str(self.__args))
        
        # "Declare" attributes, initialize them to empty values.
        self.__specification = None
        self.__winning_region = None
        self.__strategy = None
        self.__output_functions = None
        self.__code_generator = None
        self.__variables = []

       
    ######################################################################################
    ######################################################################################
    #
    # Access functions to various members/properties

    def get_verbose(self):
        return self.__verbose
    verbose = property(get_verbose)

    def get_dyn_reorder(self):
        return self.__options.dyn_reorder
    dyn_reorder = property(get_dyn_reorder)

    def get_mode(self):
        return self.__mode
    mode = property(get_mode)

    def get_language(self):
        return self.__language
    language = property(get_language)
    
    def get_cache_size(self):
        return self.__cache_size
    cache_size = property(get_cache_size)

    def get_update_sigs_size(self):
        return self.__update_sigs_size
    update_sigs_size = property(get_update_sigs_size)

    def get_num_class_vectors(self):
        return self.__num_class_vectors
    num_class_vectors = property(get_num_class_vectors)

    def get_dont_care_upper_bound(self):
        return self.__dont_care_upper_bound
    dont_care_upper_bound = property(get_dont_care_upper_bound)
    
    def get_check_combinations(self):
        return self.__check_combinations
    check_combinations = property(get_check_combinations)

    def get_partition(self):
        return self.__partition
    partition = property(get_partition)

    def get_var_order(self):
        return self.__options.var_order
    var_order = property(get_var_order)
    
    def get_reorder1(self):
        return self.__options.reorder1
    reorder1 = property(get_reorder1)
    r1 = reorder1

    def get_reorder2(self):
        return self.__options.reorder2
    reorder2 = property(get_reorder2)
    r2 = reorder2

    def get_kill(self):
        return self.__options.kill
    kill = property(get_kill)

    def get_transfer_functions(self):
        return self.__options.transfer_functions
    transfer_functions = property(get_transfer_functions)
    
    def get_dac04(self):
        return self.__options.dac04
    dac04 = property(get_dac04)

    def get_dac_recur_limit(self):
        return self.__dac_recur_limit
    dac_recur_limit = property(get_dac_recur_limit)

    def get_dac_call_limit(self):
        return self.__dac_call_limit
    dac_call_limit = property(get_dac_call_limit)

    def get_dac_search_mode(self):
        return self.__dac_search_mode
    dac_search_mode = property(get_dac_search_mode)
    
    def get_reorder_method(self):
        return self.__reorder_method
    reorder_method = property(get_reorder_method)
    
    def get_dyn_reorder_method(self):
        return self.__dyn_reorder_method
    dyn_reorder_method = property(get_dyn_reorder_method)
    
    def get_one_hot(self):
        return self.__options.one_hot
    one_hot = property(get_one_hot)
            
    def get_variables(self):
        return self.__variables[:]
    def set_variables(self, variables):
        self.__variables = variables[:]
    vars = property(get_variables, set_variables)
    
    def get_input_variables(self):
        return [var for var in self.__variables if var.type == marduk_utils.VariableType.INPUT]
    input_vars = property(get_input_variables)

    def get_output_variables(self):
        return [var for var in self.__variables if var.type == marduk_utils.VariableType.OUTPUT]
    output_vars = property(get_output_variables)

    def get_state_variables(self):
        return [var for var in self.__variables if var.type == marduk_utils.VariableType.STATE]
    state_vars = property(get_state_variables)

    def get_input_file_name(self):
        return self.__input_file
    input_file = property(get_input_file_name)
    

    def get_output_file_name(self):
        return self.__output_file
    output_file = property(get_output_file_name)

    def get_debug_mode(self):
        return self.__options.debug_mode
    debug_mode = property(get_debug_mode)

    def get_winning_region(self):
        return self.__winning_region
    def set_winning_region(self, winning_region):
        self.__winning_region = winning_region
    winning_region = property(get_winning_region, set_winning_region)

    def get_specification(self):
        return self.__specification
    def set_specification(self, specification):
        self.__specification = specification
    specification = property(get_specification, set_specification)

    def get_dd_manager(self):
        return self.__dd_manager
    dd_mgr = property(get_dd_manager)


    def add_variable(self, var):
        """
        Adds the given variable to the internal list of variables.
        This function can be used to add variables, which are not part
        of the initial specification, e.g. the state (jx) variables.

        If a variable with the given name already exists, an exception
        is thrown.
        """
        if var.name in [variable.name for variable in self.__variables]:
            raise MardukException(("Error: A variable with name '%s' already exists!" % var.name)) 
        self.__variables.append(var)

    def print_welcome_message():
        print "------------------------------------------------------"
        print "  Welcome to Marduk - The God who slaughtered Anzu! "
        print "------------------------------------------------------\n"
    
    print_welcome_message = staticmethod(print_welcome_message)
    
    def run(self):
        from nusmv import dd
        import marduk_utils
        import time

        start_wall_clock = time.clock()
        
        self.println("------------------------------------------------------")
        self.println("Synthesize " + str(self.input_file) +  " to " + str(self.output_file))
        if self.__options.mode != None:
            self.println("Mode: " + self.__options.mode.upper())
        if self.__options.language != None:
            self.println("Output Language: " + self.__options.language.upper())

        from datetime import datetime
        self.println("Start time: %s" % datetime.now().ctime())
            
        #print "Reordering status:", dd.dd_reordering_status(dd.cvar.dd_manager)
        
        self.println("\n Dynamic reordering \t\t\t\t\t" + str(self.dyn_reorder))
        self.println(" Reordering method for dynamic reordering \t\t" + marduk_utils.reorder_method_to_string(self.dyn_reorder_method))
        self.println(" Reordering method for forced reordering \t\t" + marduk_utils.reorder_method_to_string(self.reorder_method))
        self.println(" Reorder BDD after reading configuration \t\t" + str(self.r1))
        self.println(" Reorder BDD after generating output functions  \t" + str(self.r2))
        self.println(" Kill strategy and reorder afterwards   \t\t" + str(self.kill))
        self.println(" One-hot encoding of jx vars\t\t\t\t" + str(self.one_hot))
        self.println(" Transfer functions to new DD manager and reorder \t" + str(self.transfer_functions))
        self.println(" Generate functions according to\n Baneres, Cortadella, Kishinevsky (DAC'04)\t\t" + str(self.dac04))
        if self.dac04:
            if self.dac_search_mode == 'dfs':
                self.println(" DAC'04 search mode \t\t\t\t\tDepth First")
                self.println(" DAC'04 recursion depth limit\t\t\t\t" + str(self.dac_recur_limit))
            elif self.dac_search_mode == 'bfs':
                self.println(" DAC'04 search mode \t\t\t\t\tBreadth First")
                self.println(" DAC'04 call limit\t\t\t\t\t" + str(self.dac_call_limit))

        if self.__mode in (marduk_utils.Modes.IRRSOP, marduk_utils.Modes.FACTOR):
            if self.cache_size != None:
                self.println(" Function cache size \t\t\t\t\t" + str(self.cache_size))
            else:
                self.println(" Function cache size \t\t\t\t\tunlimited")
            self.println(" Number of class vectors \t\t\t\t" + str(self.num_class_vectors))
            self.println(" Number of new vectors for cache reorganization \t" + str(self.update_sigs_size))
            self.println(" Use don't care upper bound for ISoP_d \t\t\t" + str(self.dont_care_upper_bound))
            self.println(" Check combinations of 2 functions \t\t\t" + str(self.check_combinations))

        self._starttime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        
        self.println("\n Timing Information:")
        
        # Load specification from input file
        self.__specification = Specification(self)
        self.__specification.readSpecification()
        self._specificationtime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
        self.println("   Specification read within\t\t\t %7.2f seconds" %(self._specificationtime-self._starttime))

        # Create list of variables and store it here in main class, for central access
        self.__variables = self.__specification.create_variable_list()

        if self.verbose > 1:
            print "Length of variables list: ", len(self.__variables)
            for var in self.__variables:
                print var

        if self.verbose > 1:        
            print "Current Ordering:"
            print marduk_utils.print_variable_ordering(self.vars)

        if self.var_order:
            self.println('    Forcing variable order: ' + self.var_order)
            marduk_utils.set_variable_ordering(self.var_order, self.vars, self.dd_mgr)
            
        if self.verbose > 1:
            print "Current Ordering:"
            print marduk_utils.print_variable_ordering(self.vars)
        
        # Compute winning region
        import sys    
        self.__winning_region = WinningRegion(self, self.__specification)
        self.__winning_region.calcWinningRegion()
        self._winningregiontime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime

        self.println("   Compute winning region within \t\t %7.2f seconds" %(self._winningregiontime - self._reorder1time))
        if(not(self.__winning_region.isRealizable())):
            self.println("The given specification is NOT REALIZABLE!\n")
            if not self.debug_mode:
                self.println("Use the argument --dm to debug unrealizability\n")
                return
            del self.__winning_region
            self.__spec_debugger = SpecDebugger(self)
            self.__spec_debugger.debug(self.debug_mode)
            return
        self.__winning_region_size = self.__winning_region.winRegion.size    

        
        # Compute strategy
        self.__strategy = Strategy(self)
        self.__strategy.calcStrategy()
        self._strategytime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
        self.println("   Compute strategy within \t\t\t %7.2f seconds" %(self._strategytime-self._winningregiontime))

        from marduk_utils import VariableType

        self.println("\nStrategy Characterization:")
        input_vars = [var.ns for var in self.input_vars] + [var.ps for var in self.vars]
        output_vars = [var.ns for var in self.vars if var.type != VariableType.INPUT]
        begin = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
        strat_char = marduk_utils.characterize_relation(self.__strategy.strategy_bdd, input_vars, output_vars, return_bdds=True)
        char_time = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime - begin
        self.println("(computed in %7.2f seconds)" % char_time)
        total = 2 ** strat_char['num_inputs']
        defined = (strat_char['num_defined'] / total) * 100
        fixed = (strat_char['num_fixed'] / total) * 100
        dc = (strat_char['num_dc'] / total) * 100
        non_dc = (strat_char['num_non_dc'] / total) * 100
        self.println("Defined:%7.2f%%" % defined)
        self.println("Fixed:\t %7.2f%%" % fixed)
        self.println("DC:\t %7.2f%%" % dc)
        self.println("Non-DC:\t %7.2f%%\n" % non_dc)

        strat_dc = strat_char['dc_bdd']
        del strat_char
        
        if self.__mode in (marduk_utils.Modes.COFACTOR, marduk_utils.Modes.OLD):
            self.do_cofactor_mode()
        else:
            self.do_function_generator_mode(strat_dc=strat_dc)


        if self.transfer_functions:
            self.println("   Transferred output functions within \t\t %7.2f seconds" % self.__code_generator._transfer_time)
            self.println("   Reordering transferred BDD took \t\t %7.2f seconds" % self.__code_generator._reorder_time)
        self.println("\n   Results in needed overall time of\t\t %7.2f seconds \n" %(self._codegentime - self._starttime))

        stop_wall_clock_time = time.clock()
        self.println("   Overall wall clock time\t\t\t %7.2f seconds" % (stop_wall_clock_time - start_wall_clock))

        self.println("\n BDD-Size Information:")
        self.println("   Size of Winning Region: \t\t %10d bdd-nodes" % self.__winning_region_size)
        self.println("   Size of rho1 is \t\t\t %10d bdd-nodes" %self.__strategy.rho1_size)
        self.println("   Size of rho2 is \t\t\t %10d bdd-nodes" %self.__strategy.rho2_size)
        self.println("   Size of rho3 is \t\t\t %10d bdd-nodes" %self.__strategy.rho3_size)

        self.println("------------------------------------------------------")
        self.println("                FINISHED synthesis!"            )
        self.println("------------------------------------------------------")

        if self.verbose > 1:
            print "Current Ordering:"
            print marduk_utils.print_variable_ordering(self.vars)
        
        
        # The following should be the last block in the run method:
        self.__code_generator.append_comment(self.__printed_lines)
        # Killing references to other objects, break up circular references
        self.__specification = None
        self.__winning_region = None
        self.__strategy = None
        self.__output_functions = None
        self.__code_generator = None
        

#-------------------------------------------------------------------------------------------------------------------
    def do_cofactor_mode(self):
        # Compute output functions
        self.__output_functions = OutputFunctions(self, self.__winning_region, self.__strategy)

        if not self.dac04:
            #new_rel =
            self.__output_functions.constructFunctions()
        else:
            new_rel = self.__output_functions.constructFunctionsDAC04(recur_limit=self.dac_recur_limit, call_limit=self.dac_call_limit,
                                                                      bfs=(self.dac_search_mode == 'bfs'))

        self._size_gen_strat = None # new_rel.size
        self._outputfcttime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        self._reorder2time = self._outputfcttime
        self._killingtime = self._outputfcttime
        self.println("   Compute output functions within \t\t %7.2f seconds" %(self._outputfcttime - self._strategytime))
        if self.reorder2:
            result = dd.dd_reorder(self.__dd_manager, self.reorder_method,0)
            self._reorder2time = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
            self.println("   Second reordering of bdd takes \t\t %7.2f seconds" %(self._reorder2time - self._outputfcttime))

        if self.kill:
            self.__strategy.killStrategy()
            dd.dd_reorder(self.__dd_manager, self.reorder_method,0)
            self._killingtime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
            self.println("   Killing strat and reordering takes\t\t %7.2f seconds" %(self._killingtime - self._reorder2time))

        before_code_gen = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
       
        if not self.mode == marduk_utils.Modes.OLD:    
            if self.language == marduk_utils.Languages.BLIF:
                self.__code_generator = BlifFromGatesGenerator(self.output_file)
            elif self.language == marduk_utils.Languages.HIF:
                self.__code_generator = HifGenerator(self.output_file)
            elif self.language == marduk_utils.Languages.VERILOG:
	        self.__code_generator = VerilogGenerator(self.output_file)
	
	
            dd.dd_autodyn_disable(dd.cvar.dd_manager)
            dd.dd_autodyn_disable(self.__dd_manager)
            self.__code_generator.convert_functions_to_gates(self, self.__output_functions, self.__dd_manager) 
        else:
            self.__code_generator = BlifGenerator(self, self.__output_functions)   
        
        self.__code_generator.write_code_to_file()
        self._codegentime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        self.println("   Code generation takes \t\t\t %7.2f seconds" %(self._codegentime - before_code_gen))
        return

#---------------------------------------------------------------------------------------------------------------------
    def do_function_generator_mode(self, strat_dc=None):

        if self.dac04:
            raise MardukException("ERROR! DAC'04 function generation is not implemented (yet) for function-generator mode!")
        
        # Compute output functions
        import sys
        self.__output_functions = OutputFunctions(self, self.__winning_region, self.__strategy)
        self.__code_generator = self.__output_functions.constructFunctionsUsingGenerator(strat_dc=strat_dc)
        
        self._outputfcttime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
        self.println("   Compute output functions within \t\t %7.2f seconds" %(self._outputfcttime - self._strategytime))
        if self.reorder2:
            self.println("WARNING: Using --reorder2 in IrrSOP mode just takes time and has no merit.")
            result = dd.dd_reorder(self.__dd_manager, self.reorder_method,0)
            self._reorder2time = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
            self.println("   Second reordering of bdd takes \t\t %7.2f seconds" %(self._reorder2time - self._outputfcttime))
        self._reorder2time = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
        if self.kill:
            self.println("WARNING: Using --kill in IrrSOP mode just takes time and has no merit."            )
            self.__strategy.killStrategy()
            dd.dd_reorder(self.__dd_manager, self.reorder_method,0)
            self._killingtime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
            self.println("   Killing strat and reordering takes\t\t %7.2f seconds" %(self._killingtime - self._reorder2time))
        
        self.__code_generator.write_code_to_file()
        self._codegentime = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime

        return

    def println(self, line):
        print line
        self.__printed_lines.append(line)
    
#----------------------------------------------------------

def parse_options():

    parser = OptionParser()

    parser.add_option("-i", "--in", dest="input_file",
                        help="Input File, Specification in GR(1) (XML format)")
    parser.add_option("-o", "--out", dest="output_file",
                        help="Output File for synthesized circuit")
    parser.add_option("-m", "--mode", dest="mode",
                        help="Program mode. Allowed values: cofactor (default), irrsop, factor, old")
    parser.add_option("-l", "--language", dest="language",
                        help="Language for output file. Allowed values: blif (default), verilog, hif")

    parser.add_option("-p", "--partition", dest="partition", #default="Threshold",
                        help="Specifies the partition method to use. Allowed values: Threshold, Monolithic, Iwls95CP")
    parser.add_option("-d", "--dyn", dest="dyn_reorder", action="store_true",
                        default=False, help="Enable dynamic reordering of DDs")
    parser.add_option("--r1", "--reorder1", dest="reorder1", action="store_true",
                        default=False, help="Reorder BDD after reading configuration")
    parser.add_option("--r2", "--reorder2", dest="reorder2", action="store_true",
                        default=False, help="Reorder BDD after synthesizing")
    parser.add_option("-k", "--kill", dest="kill", action="store_true",
                        default=False, help="Kill strategy when no longer needed and reorder BDD afterwards")
    parser.add_option("--oh", "--one_hot", dest="one_hot", action="store_true",
                        default=False, help="encodes the jx state variables in one-hot encoding instead of binary.")
    parser.add_option("-t", "--transfer-functions", dest="transfer_functions", action="store_true", default=False,
                        help="Transfer output functions to new DD manager and reorder before dumping.")
    parser.add_option("-v", "--verbose", dest="verbose", default="0",
                        help="Set verbose level")
    parser.add_option("--var-order", dest="var_order", default="",
                        help="Forces the given variable ordering after reading the spec. Format like this: 'var1_ns -> var2_ps -> ...'")
    parser.add_option("--reorder_method", dest="reorder_method", default="SIFT_CONV",
                        help="Specifies the reorder method to use for 'forced' reordering, i.e., the reorderings forced with options --r1, --r2, and --kill. See CUDD documentation for details. Specify name of method as STRING_IN_UPPER_CASE, e.g. SIFT_CONV (default).")
    parser.add_option("--dyn_reorder_method", dest="dyn_reorder_method", default="SIFT",
                        help="Specifies the reorder method to use for automatic (=dynamic) reordering, i.e., the reorderings that are triggered automatically by the CUDD package, based on memory usage. See CUDD documentation for details. Specify name of method as STRING_IN_UPPER_CASE, e.g. SIFT (default).")
    parser.add_option("--dm", "--debug-mode", dest="debug_mode",
                        help="The mode for debugging unrealizable specifications. " + \
                        "It is a string where each substring activates " + \
                        "a certain feature. Possible substrings are: " +\
                        "                       " + \
                        "S .... check for satisfiability                       " + \
                        "D .... compute diagnoses (experimental)               " + \
                        "Du ... compute diagnoses, use a conflict in the game  " + \
                        "m<i> . compute at most <i> diagnoses (e.g. m42)       " + \
                        "e<i> . compute diagnoses with at most <i> elements    " + \
                        "M .... minimize the spec, i.e, compute unreal. core   " + \
                        "Mu ... minimize the spec, use result                  " + \
                        "v .... also minimize output variables when minimizing " + \
                        "t .... compare minimization to trivial algorithm      " + \
                        "d .... compare minimization to delta debugging        " + \
                        "T .... search for countertrace                        " + \
                        "Tu ... search for countertrace and use it             " + \
                        "G .... compute graph that summarizes all plays        " + \
                        "P .... play the interactive game                      " + \
                        "If you don't know what to choose, choose 'MuvSTuGP'")

    # Options related to DAC'04 mode
    parser.add_option("--DAC04", "--dac04", dest="dac04", action="store_true", default=False,
                        help="Use the recursive method of Baneres, Cortadella, and Kishinevsky (DAC'04) to construct functions from the strategy")
    parser.add_option("--dsm", "--dac-search-mode", dest="dac_search_mode",
                        help="Set the search mode for the DAC'04 approach. Allowed values are 'dfs' (depth first) and 'bfs' (breadth first).")
    parser.add_option("--drl", "--dac-recur-limit", dest="dac_recur_limit",
                        help="Set a maximum recursion depth for the DAC'04 approach. This option can only be used together with --DAC04 in DFS mode.")
    parser.add_option("--dcl", "--dac-call-limit", dest="dac_call_limit",
                        help="Define how many calls to the relation solver are allowed. This option can only be used together with --DAC04 in BFS mode.")


    # Options related to IrrSOP (cache)
    parser.add_option("--cache-size", dest="cache_size",
                        help="Specify the maximum size of the function cache. 0 disables the cache. If this option is not used, the cache size is infinite. This option is only in effect in IrrSOP mode.")
    parser.add_option("--num-class-vectors", default=1024, dest="num_class_vectors",
                        help="Specify the number of class vectors used in the function cache. Default is 1024. This option is only in effect in IrrSOP mode.")
    parser.add_option("--update-sigs-size", dest="update_sigs_size", default=32,
                      help="Specifies the number of new discrimination vectors that triggers cache reorganization. 0 turns this feature off.")
    parser.add_option("--check-combinations", action="store_true", default=False, dest="check_combinations",
                        help="Check combinations of 2 chached functions. This option is only in effect in IrrSOP mode.")
    parser.add_option("--dcub", "--dont-care-upper-bound", action="store_true", default=False, dest="dont_care_upper_bound",
                        help="Use the upper bound of the interval for ISoP_d. This option is only in effect in IrrSOP mode.")


    (cmd_line_options, args) = parser.parse_args()
    return (cmd_line_options, args)


def main():
    Marduk.print_welcome_message()
    try:
        import random
        random.seed(1468192489) # Use "magic" number as seed for module random, to provide pseudorandomness and comparability across runs
        import sys
        sys.setrecursionlimit(10000)
        (cmd_line_options, args) = parse_options()
        marduk = Marduk(cmd_line_options, args)
        marduk.run()
        from nusmv import dd
        from bddwrap import BDD
        manager = marduk.dd_mgr
        marduk = None
        exit(0)
    except (MardukException), exc:
        print "ERROR! Encountered an exception!"
        import traceback
        traceback.print_exc()
        print exc.message
        exit(1)

if __name__ == "__main__":
    main()
