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

from nusmv import dd
from bddwrap import BDD
import marduk_utils
from function_cache import FunctionCache
from function_generator import FunctionGenerator


class IrrsopGenerator(FunctionGenerator):
    """
    Implements generation of IrrSOPs (cf. Mishchenko 2001, An introduction to ZDDs)

    Assumptions:
    The ZDD variable ordering is 'linked' to the BDD variable ordering, where (in the ZDD)
    the indices of the positive literals are 2*i and the indices of the negative literals
    are 2*i+1 (where i is the BDD index).
    """
    from nusmv import dd
    from bddwrap import BDD
    #from zddwrap import ZDD
    import code_generator



    #======================================================================
    #  METHODS
    #======================================================================

    #----------------------------------------------------------------------
    def __init__(self, var_wires, dd_mgr, code_generator=None, marduk_vars=None, num_class_vectors=1024, strat_dc=None):
        """
        'var_wires' is supposed to be a dictionary which maps the string representation of a BDD object
        to the corresponding signal in the code generator, for all inputs (and their negations) on which the function(s) to be
        handled by this IrrsopGenerator depend.
        """
        FunctionGenerator.__init__(self, var_wires, dd_mgr, code_generator, marduk_vars, num_class_vectors, strat_dc)
        self._irrsop_recur = 0
        


    #----------------------------------------------------------------------
    def irrsop(self, f, fd, upper_bound_for_lookup=None, literal_list=None):
        """
        Computes an IrrSOP.

        Comments, variable names, etc. are inspired by Mishchenko 2001 (An Introduction to ZDDs)

        Parameters:
        'f' is the onset 'fd' is the sum of the onset and the dont-care-set.
        (both as BDD objects)

        Returns:
        A BDD object representing the function implementend by the cover, and a reference to the corresponding signal in the
        output-code generator.
        """
        self._irrsop_recur += 1
        print "Recursion depth:", self._irrsop_recur
        
        if f.isZero():
            self._irrsop_recur -= 1
            return (BDD.ZERO(self._dd_mgr), "zero")

        if fd.isOne():
            self._irrsop_recur -= 1
            return (BDD.ONE(self._dd_mgr), "one")

        if upper_bound_for_lookup:
            if upper_bound_for_lookup.isOne():
                self._irrsop_recur -= 1
                return (BDD.ONE(self._dd_mgr), "one")

        if self._use_fd_upper_bound and upper_bound_for_lookup != None:
            (function, signal) = self._function_cache.find_suitable_function(f,upper_bound_for_lookup)
        else:
            (function, signal) = self._function_cache.find_suitable_function(f,fd)

        if(function != None):
            print "[DBG]: Using cached function!"
            # DEBUG
            # if not (f <= function and function <= fd):
#                 raise Exception
#             else:
#                 print "Cached Function OK."
            # END DEBUG
            self._irrsop_recur -= 1
            return (function, signal)

        if literal_list:
            if len(literal_list) > 0:
                x = literal_list.pop(0)
            else:
                x = marduk_utils.top_variable(f, fd)  # x is the BDD of the corresponding projection function
        else:
            x = marduk_utils.top_variable(f, fd)  # x is the BDD of the corresponding projection function
        
        (f0, f1) = self.decompose_bdd(f, x)
        (fd0, fd1) = self.decompose_bdd(fd, x)
        
        g0 = f0 * ~fd1
        r0 = self.irrsop(g0, fd0)
        del g0
        
        g1 = f1 * ~fd0
        r1 = self.irrsop(g1, fd1)
        del g1
    
        h = (f0 * ~(r0[0])) + (f1 * ~(r1[0]))
        del f0, f1
        hd = fd0 * fd1
        del fd0, fd1
        
        if self._use_fd_upper_bound:
            r2 = self.irrsop(h, hd, upper_bound_for_lookup=fd)
        else:  
            r2 = self.irrsop(h, hd)

        del h, hd, fd
            
        (r, signal) = self.compose_cover(x, r0, r1, r2)
        self._function_cache.update(r, signal)
        #self._function_cache.print_stats()

        # DEBUG
#         if not (f <= r and r <= fd):
#             raise Exception
#         else:
#             print "Function OK."
        # END DEBUG
        self._irrsop_recur -= 1
        return (r, signal)

