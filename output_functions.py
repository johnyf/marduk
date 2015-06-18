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

class OutputFunctions(object):
    """
    This class computes (combinational) functions for each (system) output.
    """

    from bddwrap import BDD
    from irrsop import IrrsopGenerator
    import marduk_utils
    from marduk_utils import MardukException
    
    def __init__(self, marduk, winning_region, strategy):
        self.__marduk = marduk
        self.__strategy = strategy
        self.__winning_region = winning_region

        self.__functions = {}

        self.__dac_recur_counter = 0  # Counts the recursion depth for DAC'04 function generation
        self.__dac_call_counter = 0   # Counts the number of calls to the recursive step of DAC'04. Used for limiting BFS
        self.__dac_recur_limit = None
        self.__dac_call_limit = None

    def get_size(self):
        size = 0
        for key in self.__functions.keys():
            size += self.__functions[key].size
        return size

    # The sum of the BDD sizes of all output functions
    size = property(get_size)
    
    
    def get_functions(self):
        return self.__functions

    # Dictionary from names (strings) of output and state vars to corresponding BDD object.
    functions = property(get_functions)


    def constructFunctions(self, simplify=True):
        """
        Construct functions
        
        Given a bdd rel in terms of invars and outvars computes a hashmap
        that maps each outvarname to a function f in terms of invars such
        that f(invars) = 1 (0) iff rel(invars,1)
        
        output_vars is a hashmap that maps outvarnames to bdds
        input_vars is just a ref to an array of bdds
        the results are optimized wrt the careset
        if simplify is 1, a simple optimization is used.
        
        returns the hasmap and a relational representation of the result.
        algorithm described in DATE & COCV papers

        [Copied (and modified) from Anzu.]
        """
        from bddwrap import BDD
        marduk_mgr = self.__marduk.dd_mgr
        
        strat = self.__strategy.strategy_bdd
        init = self.__winning_region.init12 * self.__winning_region.initjx

        # input_vars is a list of BDDs of all combinational inputs.
        # These are: x, x', y, jx
        # (present inputs, next inputs, prssent outputs, present jx state)
        input_vars = [var.ps for var in self.__marduk.vars]  # This includes all present-state vars, i.e. x, y, jx
        input_vars.extend([var.ns for var in self.__marduk.input_vars])

        # output_vars is a dictionary mapping from varnames to BDDs of combinational outputs.
        # These are: y', jx'
        # (next outputs, next jx state)
        output_vars = {}
        for var in self.__marduk.output_vars:
            output_vars[var.name] = var.ns
        for var in self.__marduk.state_vars:
            output_vars[var.name] = var.ns
        
        careset = self.__winning_region.reachableStates(init, strat, self.__winning_region.winRegion)
        del init
        
        outputvarnames = output_vars.keys()

        import random
        random.seed(1468192489) # Seed is just some magic number (for reproducability)
#         outputvarnames.reverse()
#         random.shuffle(outputvarnames)
#         random.shuffle(outputvarnames)
#         random.shuffle(outputvarnames)
        
        for output in outputvarnames:
            rel_prime = strat

            # quantify out all other output variables
            for other_output in outputvarnames:
                if output != other_output:
                    var = output_vars[other_output]
                    rel_prime = rel_prime.exists(var)
                
            
            var = output_vars[output]
            positive_cofactor = rel_prime / var
            negative_cofactor = rel_prime / ~var
            p = positive_cofactor * ~negative_cofactor
            n = negative_cofactor * ~positive_cofactor
            
            if simplify :
                for input in input_vars:
                    p_prime = p.exists(input)
                    n_prime = n.exists(input)
                    if (p_prime * n_prime) == BDD.ZERO(marduk_mgr):
                        p = p_prime 
                        n = n_prime

            xor = p + n 
            del n
            func = p // (xor * careset) 
            func.name = "func_" + output
            del p, xor

            if self.__marduk.verbose > 1:
                print "-----------------------"
                print "Output: ", output
                func.print_minterm()
            
            self.__functions[output] = func
            strat = strat.compose(var, func)
            
        # end for each output
        
        return 


    def constructFunctionsUsingGenerator(self, strat_dc=None):
        """
        Computes output functions by using the IrrSOP Generator
        """
        from nusmv import dd
        import marduk_utils
        from irrsop import IrrsopGenerator
        from factorization import FactorizationGenerator
        from code_generator import VerilogGenerator
        from code_generator import HifGenerator
        from code_generator import BlifFromGatesGenerator
        from bddwrap import BDD
        marduk_mgr = self.__marduk.dd_mgr
        if self.__marduk.language == marduk_utils.Languages.BLIF:
            code_generator = BlifFromGatesGenerator(self.__marduk.output_file)
        elif self.__marduk.language == marduk_utils.Languages.VERILOG:
            code_generator = VerilogGenerator(self.__marduk.output_file)
        elif self.__marduk.language == marduk_utils.Languages.HIF:
            code_generator = HifGenerator(self.__marduk.output_file)
        else:
            from marduk_utils import MardukException
            raise MardukException("Unknown language %s" % self.__marduk.language)

        strat = self.__strategy.strategy_bdd

        # input_vars is a list of BDDs of all combinational inputs.
        # These are: x, x', y, jx
        # (present inputs, next inputs, prssent outputs, present jx state)
        input_vars = [var.ps for var in self.__marduk.vars]  # This includes all present-state vars, i.e. x, y, jx
        input_vars.extend([var.ns for var in self.__marduk.input_vars])

        # output_vars is a dictionary mapping from varnames to BDDs of combinational outputs.
        # These are: y', jx'
        # (next outputs, next jx state)
        output_vars = {}
        for var in self.__marduk.output_vars:
            output_vars[var.name] = var.ns
        for var in self.__marduk.state_vars:
            output_vars[var.name] = var.ns
        
        careset = self.__winning_region.reachableStates(self.__winning_region.init12 * self.__winning_region.initjx, strat, self.__winning_region.winRegion)
    
        wires = self.__createSignalsForFunctionGenerator(code_generator)

        function_gen = None
        
        if self.__marduk.mode == marduk_utils.Modes.IRRSOP:
            function_gen = IrrsopGenerator(wires, marduk_mgr, code_generator, self.__marduk.vars, num_class_vectors=self.__marduk.num_class_vectors, strat_dc=strat_dc)
            function_gen.useDontCareUpperBound = self.__marduk.dont_care_upper_bound
        elif self.__marduk.mode == marduk_utils.Modes.FACTOR:
            function_gen = FactorizationGenerator(wires, marduk_mgr, code_generator, self.__marduk.vars, num_class_vectors=self.__marduk.num_class_vectors, strat_dc=strat_dc)

        function_gen.functionCache.cacheSize = self.__marduk.cache_size
        function_gen.functionCache.updateSignatures = self.__marduk.update_sigs_size

        import random
        random.seed(1468192489) # Seed is just some magic number (for reproducability)
        literal_list = None
#         literal_list = [var for var in input_vars]
#         literal_list.sort(cmp = marduk_utils.comp_bdd_objs)
#         literal_list.reverse()
#         random.shuffle(literal_list)
#         random.shuffle(literal_list)
#         random.shuffle(literal_list)

        
        outputvarnames = output_vars.keys()
        num = 0
        for output in outputvarnames:
            num += 1
            rel_prime = strat

            # quantify out all other output variables
            for other_output in outputvarnames:
                if output != other_output:
                    var = output_vars[other_output]
                    rel_prime = rel_prime.exists(var)
                
            var = output_vars[output]
            positive_cofactor = rel_prime / var
            negative_cofactor = rel_prime / ~var
            del rel_prime
            
            lower = positive_cofactor * ~negative_cofactor
            upper = ~negative_cofactor + positive_cofactor
            del positive_cofactor, negative_cofactor

            if self.__marduk.mode == marduk_utils.Modes.IRRSOP:
                (function, signal) = function_gen.irrsop(lower, upper, literal_list=literal_list)
            elif self.__marduk.mode == marduk_utils.Modes.FACTOR:
                (function, signal) = function_gen.factor_interval(lower, upper)
            del lower, upper
            
            # DEBUG: Sanity Check: Is the computed function ok?
#             if function >= lower and function <= upper:
#                 print "Function for %s is ok (%d of %d)." % (output, num, len(outputvarnames))
#             else:
#                 print "Function for %s is NOT ok." % output
#                 raise Exception
#             del lower, upper

            
            # DEBUG Sanity Check:
#             reproduction = code_generator.wire2BDD(signal, self.__marduk.vars)
#             if function == reproduction:
#                 print "Function %s matched." % output
#             else:
#                 print "MISMATCH for function %s" % output
#                 raise Exception

            strat = strat.compose(var, function)
            del function
            #new_rel *= ((~var + function) * (var + ~function)) #=($var <-> $function)

            code_generator.add_output(output, signal)
            #print "Size of circuit for %s:%d" %(output,code_generator.circuit_size(signal))
            code_generator.change_flipflop_input(output + "_ps", signal)
            #self.__functions[output] = function
            if self.__marduk.verbose > 0:
                print "Done with output '%s'." % output        
        function_gen.functionCache.print_stats()

        if self.__marduk.mode == marduk_utils.Modes.FACTOR:
            print "Factor Steps:", function_gen._num_factor_steps
            print "Fallback Steps:", function_gen._num_fallback_steps
        
        return code_generator
    # end of constructFunctionsUsingGenerator
    
    def __createSignalsForFunctionGenerator(self, code_generator):
        import marduk_utils
        wires = {}
        for var in self.__marduk.input_vars:
            code_generator.add_input(var.name)
            negation = code_generator.add_not(var.name)
            wires[str(var.ns)] = var.name
            wires[str(~var.ns)] = negation
            

            initial = marduk_utils.get_init_value_from_bdd(var, self.__marduk.winning_region.init12 * self.__marduk.winning_region.initjx)
            code_generator.add_flipflop(var.name + "_ps", var.name, initial)
            negation = code_generator.add_not(var.name + "_ps")
            wires[str(var.ps)] = var.name + "_ps"
            wires[str(~var.ps)] = negation

        for var in self.__marduk.vars:
            if var.type == marduk_utils.VariableType.INPUT:
                continue
            initial = marduk_utils.get_init_value_from_bdd(var, self.__marduk.winning_region.init12 * self.__marduk.winning_region.initjx)
            code_generator.add_flipflop(var.name + "_ps", None, initial)
            negation = code_generator.add_not(var.name + "_ps")
            wires[str(var.ps)] = var.name + "_ps"
            wires[str(~var.ps)] = negation
            
        return wires


###############################################################################################
###############################################################################################
#                                                                                             #
# Function Generation according to DAC'04 (Baneres, Cortadella, Kishinevsky)                  #
#                                                                                             #
# Main functions, and necessary internal functions follow below.                              #
#                                                                                             #
###############################################################################################

    def constructFunctionsDAC04(self, recur_limit=None, call_limit=None, bfs=False):
        
        if recur_limit:
            self.__dac_recur_limit = recur_limit

        if call_limit:
            self.__dac_call_limit = call_limit
        
        # First make lists of inputs and outputs, get the strategy,
        # then start the recursive algorithm.
        from bddwrap import BDD
        strat = self.__strategy.strategy_bdd
        reachable_states =  self.__winning_region.reachableStates(self.__winning_region.init, self.__winning_region.trans12, BDD.ONE(self.__marduk.dd_mgr))
        strat //= reachable_states

        #print "Constructing functions according to DAC'04.\nStrategy is:"
        #strat.print_minterm()
       
        # input_vars is a list of BDDs of all combinational inputs.
        # These are: x, x', y, jx
        # (present inputs, next inputs, prssent outputs, present jx state)
        input_vars = [var.ps for var in self.__marduk.vars]  # This includes all present-state vars, i.e. x, y, jx
        input_vars.extend([var.ns for var in self.__marduk.input_vars])

        # output_vars is a dictionary mapping from varnames to BDDs of combinational outputs.
        # These are: y', jx'
        # (next outputs, next jx state)
        output_vars = {}
        for var in self.__marduk.output_vars:
            output_vars[var.name] = var.ns
        for var in self.__marduk.state_vars:
            output_vars[var.name] = var.ns
        

        strat = self._make_well_defined(strat, output_vars)

        import marduk_utils

        # Obtain a quick solution, which is used as a reference for branch&bound
        quick_solution = self._quick_solver(strat, input_vars, output_vars)
        initial_solution = quick_solution
        print "Cost of initial solution: %d" % self._costs(initial_solution)
        print "Overspecification ratio of relation: %d" % marduk_utils.relation_freedom_ratio(strat, input_vars, output_vars)
        
        # Now start the recursion

        if bfs:
            # This is BFS mode
            if bfs:
                bfs_queue = []
            self.__dac_call_counter = 0
            self.__functions = self._solve_relation_recur(strat, quick_solution, input_vars, output_vars, queue=bfs_queue)
            while len(bfs_queue) > 0:
                print self.__dac_call_counter
                #print "Cost of best functions: ", self._costs(self.__functions)
                print "Queue length:", len(bfs_queue)
                current = bfs_queue.pop(0)
                self.__functions = self._solve_relation_recur(current[0], self.__functions, current[2], current[3], queue=bfs_queue)
        else:
            # This is DFS mode
            self.__dac_recur_counter = 0
            self.__functions = self._solve_relation_recur(strat, quick_solution, input_vars, output_vars)

        print "Made %d calls to recursive step" % self.__dac_call_counter
        print "Solution is equal to initial solution:", (self.__functions == initial_solution)
        new_rel = self._to_relation(self.__functions, output_vars)
        print "Overspecification ratio of solution: %d" % marduk_utils.relation_freedom_ratio(new_rel, input_vars, output_vars)
        return new_rel


    ########################################################################################################
    # Main recursive step                                                                                  #
    ########################################################################################################
    def _solve_relation_recur(self, relation, best_functions, input_vars, output_vars, code_generator=None, queue=None):
        """
        Recursive step of relation solving.
        Based on Baneres, Cortadella, Kishinevsky, 'A Recursive Paradigm To Solve Boolean Relations', DAC'04
        Slightly adapted to fit into Marduk.
        """
        from bddwrap import BDD
        from marduk_utils import MardukException

        self.__dac_recur_counter += 1
        self.__dac_call_counter += 1
        print "Recur counter: %d" % self.__dac_recur_counter
        print "Call counter : %d" % self.__dac_call_counter
     
        # Stop recursion, if there is an existing limit and it is reached.
        if queue == None:
            # This is DFS mode
            if self.__dac_recur_limit:
                if self.__dac_recur_counter > self.__dac_recur_limit:
                    quick_solution = self._quick_solver(relation, input_vars, output_vars)
                    print "Quick Solution: ", self._costs(quick_solution)
                    if self._compare_costs(quick_solution, best_functions) < 0:
                        result = quick_solution
                    else:
                        result = best_functions
                    self.__dac_recur_counter -= 1
                    return result
        else:
            # This is BFS mode
            if self.__dac_call_limit:
                if (self.__dac_call_counter + len(queue)) >= self.__dac_call_limit:
                    quick_solution = self._quick_solver(relation, input_vars, output_vars)
                    print "Quick Solution: ", self._costs(quick_solution)
                    if self._compare_costs(quick_solution, best_functions) < 0:
                        result = quick_solution
                    else:
                        result = best_functions
                    self.__dac_recur_counter -= 1
                    return result
                        

        tmp_rel = relation.copy()
        for var in output_vars.values():
            tmp_rel = tmp_rel.exists(var)

        if not tmp_rel.isOne():
            raise MardukException("Error! Relation not well-defined!")

        functions = self._to_functions(relation, input_vars, output_vars)

        if functions:
            print "Relation represents a function"
            if best_functions:
                if self._compare_costs(functions, best_functions) < 0:
                    self.__dac_recur_counter -= 1
                    return functions
                else:
                    self.__dac_recur_counter -= 1
                    return best_functions
            else:
                self.__dac_recur_counter -= 1
                return functions
        else:
            print "Not a function yet"

            
        # From here, 'relation' is not a function
        # Minimize each output independently
            
        functions = {}
        outputvarnames = output_vars.keys()
        for output_name in outputvarnames:
            output = output_vars[output_name]

            rel_prime = relation.copy()
            
            # quantify out all other output variables
            for other_output in outputvarnames:
                if output_name != other_output:
                    var = output_vars[other_output]
                    rel_prime = rel_prime.exists(var)
        
            functions[output_name] = self._minimize(rel_prime, output, input_vars)
            
        # End loop over all outputs
        print "Cost of solution attempt is: ", self._costs(functions)
        print "Cost of best functions is: ", self._costs(best_functions)
        if best_functions: 
            if self._compare_costs(functions, best_functions) >= 0:
                self.__dac_recur_counter -= 1
                return best_functions
        
        
        # New solution is better, but it may not be compatible
        incompatibilities = self._find_incompatibilities(relation, self._to_relation(functions, output_vars))
        if incompatibilities.isZero():
            self.__dac_recur_counter -= 1
            print "No incompatibilities. Found new solution of cost %d" % self._costs(functions)
            return functions

        # There are incompatibilities. --> Split and call recursively
        (vertex, output) = self._pick_vertex(relation, incompatibilities, input_vars, output_vars)

        tmp_rel = relation.copy()
        for other_output in output_vars.values():
            if other_output != output:
                tmp_rel = tmp_rel.exists(other_output)
        test = tmp_rel / vertex
        if test.isNotOne():
            raise MardukException("Error: test value is not BDD.ONE() as expected!")
        
        (relation_0, relation_1) = self._split(relation, vertex, output)
        if relation == relation_0:
            raise MardukException("ERROR! relation == relation_0 after split!!!")
        if relation == relation_1:
            raise MardukException("ERROR! relation == relation_1 after split!!!")
        if relation_0 == relation_1:
            raise MardukException("ERROR! relation_0 == relation_1 after split!!!")

        if queue == None:
            # This is DFS mode
            best_functions = self._solve_relation_recur(relation_0, best_functions, input_vars, output_vars)
            best_functions = self._solve_relation_recur(relation_1, best_functions, input_vars, output_vars)
        else:
            # This is BFS mode
            queue.append((relation_0, best_functions, input_vars, output_vars))
            queue.append((relation_1, best_functions, input_vars, output_vars))

        self.__dac_recur_counter -= 1
        return best_functions
    #####################################################################################################
    # End main recursive step                                                                           #
    #####################################################################################################

    def _to_relation(self, functions, output_vars):
        from bddwrap import BDD
        relation = BDD.ONE(self.__marduk.dd_mgr)
        for outputname in output_vars.keys():
            output = output_vars[outputname]
            relation *= ((output * functions[outputname]) + ((~output)*(~functions[outputname])))
        return relation


    def _to_functions(self, relation, input_vars, output_vars):
        """
        Returns the functions represented by 'relation'. If 'relation' does not
        represent completely specified functions, then 'None' is returned.
        """
        from bddwrap import BDD
        functions = {}
        for outputname in output_vars.keys():
            output = output_vars[outputname]
            tmp_rel = relation.copy()

            # Quantify out all other outputs
            for other_outputname in output_vars.keys():
                if outputname != other_outputname:
                    var = output_vars[other_outputname]
                    tmp_rel = tmp_rel.exists(var)

            pos = tmp_rel / output
            neg = tmp_rel / ~output

            if ((pos + neg).isNotOne()):
                # Not well-defined. Some x-vertices have no output.
                raise MardukException("Encountered a relation which is not well-defined in DAC'04-mode.")
            
            if ((pos * neg).isNotZero()):
                # Not completely specified. Don't cares still exist.
                return None

            functions[outputname] = pos

        return functions


    def _make_well_defined(self, relation, output_vars):
        """
        Makes the given relation well-defined. For all vertices x, for which the relation
        is currently not defined, (x, -) will be added (for all outputs).
        """
        from bddwrap import BDD
        # First find out for which inputs the relation is undefined.
        # --> Quantify out all outputs.

        defined = relation.copy()
        for outputname in output_vars.keys():
            output = output_vars[outputname]
            defined = defined.exists(output)

        undefined = BDD.ONE(self.__marduk.dd_mgr) * ~defined

        # Extend relation with currently undefined vertices.
        # Do not restrict outputs, i.e. set them DC.
        return relation + undefined


    def _compare_costs(self, functions_1, functions_2):
        costs_1 = self._costs(functions_1)
        costs_2 = self._costs(functions_2)
        if costs_1 == costs_2:
            return 0
        elif costs_1 < costs_2:
            return -1
        else:
            return 1

    def _costs(self, functions):
        if functions == None:
            return None
        costs = 0
        for function in functions.values():
            costs += function.size
        return costs
    

    def _minimize(self, relation, output, input_vars, simplify=True):
        from bddwrap import BDD

        # positive_cofactor = relation / output
#         negative_cofactor = relation / ~output
#         lower = positive_cofactor * ~negative_cofactor
#         upper = ~negative_cofactor + positive_cofactor
        
#         func = BDD.between(lower, upper)
#         return func

        # Trying "Anzu"-Approach instead:
        # seems to be more efficient. (Not sure why)

        positive_cofactor = relation / output
        negative_cofactor = relation / ~output
        p = positive_cofactor * ~negative_cofactor
        n = negative_cofactor * ~positive_cofactor
            
        if simplify :
            for input in input_vars:
                p_prime = p.exists(input)
                n_prime = n.exists(input)
                if (p_prime * n_prime).isZero():
                    p = p_prime.copy() 
                    n = n_prime.copy()

        xor = p + n #$p*!$n + !$p*$n; #$positive_cofactor ^ $negative_cofactor;
        func = p // xor #(xor * careset) #$positive_cofactor->Restrict($xor * $careset);
        return func



    def _quick_solver(self, relation, input_vars, output_vars):
        tmp_rel = relation.copy()
        outputvarnames = output_vars.keys()
        functions = {}
        for output_name in outputvarnames:
            output = output_vars[output_name]

            rel_prime = tmp_rel.copy()
            
            # quantify out all other output variables
            for other_output in outputvarnames:
                if output_name != other_output:
                    var = output_vars[other_output]
                    rel_prime = rel_prime.exists(var)
            functions[output_name] = self._minimize(rel_prime, output, input_vars)
            tmp_rel *= ((output * functions[output_name]) + ((~output)*(~functions[output_name])))
        return functions
        

    def _find_incompatibilities(self, relation, new_relation):
        #print "New relation:"
        #new_relation.print_minterm()
        return ~relation * new_relation


    def _split(self, relation, vertex, output):
        #print "Split vertex:"
        #vertex.print_minterm()
        #print "output:"
        #output.print_minterm()
        #print "(~vertex + ~output)"
        #(~vertex + ~output).print_minterm()
        relation_1 = relation * (~vertex + ~output)
        relation_2 = relation * (~vertex + output)
        return (relation_1, relation_2)


    def _pick_vertex(self,relation, incompatibilities, input_vars, output_vars):
        """
        Picks a vertex for conflict resolution.
        Heuristic approach from Baneres, Cortadella, Kishinevsky (DAC'04), Section 4.4 is followed.
        """
        from nusmv import dd
        from bddwrap import BDD
        from marduk_utils import MardukException
        conflicts = incompatibilities.copy()

        # Abstract outputs
        tmp_conflicts = incompatibilities.copy()

        for output in output_vars.values():
            tmp_conflicts = tmp_conflicts.exists(output)

        # Find largest cube
        ptr = tmp_conflicts.ptr
        (largest_cube_ptr, length) = dd.bdd_largest_cube(self.__marduk.dd_mgr, ptr)
        largest_cube = BDD(largest_cube_ptr, self.__marduk.dd_mgr, "largest_cube")
        dd.bdd_free(self.__marduk.dd_mgr, largest_cube_ptr)
        dd.bdd_free(self.__marduk.dd_mgr, ptr)

        # Select on specific vertex, covered by the largest cube
        # For the moment: set all variables which are dc to 1.
        # Maybe something more intelligent can be done instead.
        vertex = largest_cube.copy()
        for input in input_vars:
            pos = largest_cube / input
            neg = largest_cube / ~input
            if pos == neg:
                vertex *= input
                
        # Find some output, for which the selected vertex has a conflict.
        # Use the first output that has such a conflict.
        # Maybe use better heuristics here at a later time.

        tmp_rel = relation.copy()
        tmp_rel /= vertex

        for output in output_vars.values():

            pos = tmp_rel / output
            neg = tmp_rel / ~output
            if pos.isNotZero() and neg.isNotZero():
                return (vertex, output)
                           
            
        raise MardukException("No output had a conflict with the selected cube. This should not happen. There must be some serious error!")
