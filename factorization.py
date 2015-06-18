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

from bddwrap import BDD
from function_cache import FunctionCache
from function_generator import FunctionGenerator

import marduk_utils


class FactorizationGenerator(FunctionGenerator):

    def __init__(self, var_wires, dd_mgr, code_generator=None, marduk_vars=None, num_class_vectors=1024, strat_dc=None ):
        """
        'var_wires' is supposed to be a dictionary which maps the string representation of a BDD object
        to the corresponding signal in the code generator, for all inputs (and their negations) on which the function(s) to be
        handled by this Generator depend.
        """
        FunctionGenerator.__init__(self, var_wires, dd_mgr, code_generator, marduk_vars, num_class_vectors, strat_dc)        
        
        self._factor_recursion_depth = 0
        self._num_fallback_steps = 0
        self._num_factor_steps = 0
        

#####################
        
    def factor_interval(self, f, fd, cube=None):
        """
        Recursively factors the given intervall.
        """
        
        self._factor_recursion_depth += 1

        print "f", str(f)
        print "fd", str(fd)
        if cube:
            print "cube"
            cube.print_minterm()
        else:
            print "No cube"

        

        if cube:
            f /= cube
            fd /= cube

        print "after cube cofactor"
        print "f", str(f)
        print "fd", str(fd)

        # assert(self._factor_recursion_depth < 100)  # DEBUG


        if f.isZero():
            self._factor_recursion_depth -= 1
            return (BDD.ZERO(self._dd_mgr), "zero")

        if fd.isOne():
            self._factor_recursion_depth -= 1
            return (BDD.ONE(self._dd_mgr), "one")

        (function, signal, close_functions) = self._function_cache.find_suitable_function(f, fd, find_closest=True)

        if(function != None):
            print "[DBG]: Using cached function!"
            # DEBUG
            # if not (f <= function and function <= fd):
#                 raise Exception
#             else:
#                 print "Cached Function OK."
            # END DEBUG
            self._factor_recursion_depth -= 1
            return (function, signal)


        # No suitable function found in cache. Now determining a divisor, using close matches, if possible
        
        if (not close_functions):
            assert(self._function_cache.cacheSize == 0)  # If the cache is non-empty, there should be close functions
            print "[DBG]: No close_functions found. Using top literal of (f, fd) as fallback."
            literal = marduk_utils.top_variable(f, fd)
            self._function_cache.update(literal, self._wires[str(literal)])
            divisors = [self._wires[str(literal)]]
        else:
            print "[DBG]: Close functions:", close_functions
            divisors = close_functions
            
        del close_functions

        # Check that the chosen divisor will lead to bigger intervalls (--> termination)
        # Otherwise choose different divisor

        while len(divisors):
            divisor_signal = self.choose_divisor(f, fd, divisors)
            print "[DBG]: Trying divisor:", divisor_signal
            divisor_bdd = self._code_generator.wire2BDD(divisor_signal, self._marduk_vars)

            if cube:
                if cube <= divisor_bdd:
                    print "[DBG]: Divisor is implied by cube. Try next one."
                    divisor_bdd = None
                    continue
                elif cube.invert_cube_polarity() <= divisor_bdd:
                    print "[DBG]: Divisor is implied by polarity-inverted cube. Try next one."
                    divisor_bdd = None
                    continue
                else:
                    print "[DBG]: Divisor is not implied by cube or polarity-inverted cube."

            low_q = f * divisor_bdd
            up_q = (fd + ~(~fd * divisor_bdd))
            low_r = f * ~divisor_bdd

            if cube:
                low_q = low_q / cube
                up_q = up_q / cube
                low_r = low_r / cube
            
            if (low_q < f or up_q > fd) and low_r < f:
                # Divisor fulfills properties for termination --> choose it
                print "f:", str(f)
                print "fd", str(fd)
                print "low_q", str(low_q)
                print "up_q", str(up_q)
                print "[DBG]: Divisor fulfills properties for termination. --> Choose it"
                break
            else:
                print "[DBG]: Divisor does not fulfill properties for termination. --> Try next one. (%d left)" % len(divisors)
                divisor_bdd = None

        if not divisor_bdd:
            print "[DBG]: No divisor found."
            print "[DBG]: ==> Fallback in this step."
            self._num_fallback_steps += 1
            return self.one_step_cofactor(f, fd, cube)

        self._num_factor_steps += 1
                
        
        # Compute interval for quotient and recur
        
        (quotient_bdd, quotient_signal) = self.factor_interval(low_q, up_q, cube)
        del low_q, up_q

        # Compute interval for remainder and recur
        
        (remainder_bdd, remainder_signal) = self.factor_interval(low_r, fd, cube)
        del low_r


        # Compose results

        and_bdd = quotient_bdd * divisor_bdd
        del quotient_bdd, divisor_bdd
        and_signal = self._code_generator.add_and((quotient_signal, divisor_signal))
        self._function_cache.update(and_bdd, and_signal)

        
        result_bdd = and_bdd + remainder_bdd
        del and_bdd, remainder_bdd
        result_signal = self._code_generator.add_or((and_signal, remainder_signal))
        self._function_cache.update(result_bdd, result_signal)

        self._factor_recursion_depth -= 1
        return (result_bdd, result_signal)
        
        
####################

    def one_step_cofactor(self, f, fd, cube=None):

        if cube:
            f = f/ cube
            fd = fd / cube
        else:
            cube = BDD.ONE(f.mgr)

        x = marduk_utils.top_variable(f, fd)

        print "[DBG]: Chose literal", self._wires[str(x)]

        (f0, f1) = self.decompose_bdd(f, x)
        (fd0, fd1) = self.decompose_bdd(fd, x)

        r0 = self.factor_interval(f0, fd0, cube*(~x))
        del f0, fd0

        neg_wire = self._code_generator.add_and((r0[1], self._wires[str(~x)]))
        neg_bdd = r0[0] * ~x
        del r0
        self._function_cache.update(neg_bdd, neg_wire)

        r1 = self.factor_interval(f1, fd1, cube*x)
        del f1, fd1

        pos_wire = self._code_generator.add_and((r1[1], self._wires[str(x)]))
        pos_bdd = r1[0] * x
        del r1
        self._function_cache.update(pos_bdd, pos_wire)

        result_bdd = pos_bdd + neg_bdd
        del pos_bdd, neg_bdd

        result_wire = self._code_generator.add_or((pos_wire, neg_wire))
        self._function_cache.update(result_bdd, result_wire)

        return (result_bdd, result_wire)



####################

    def choose_divisor(self, f, fd, close_functions):
        """
        Heuristic to choose a divisor from a list of possible ones.
        The chosen divisor is removed from the list.

        For now, just take the first one. Try better heuristics later.
        """

        return close_functions.pop()  # FIXXME: Use better heuristic
            
            

        
    
