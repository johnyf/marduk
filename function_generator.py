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


class FunctionGenerator(object):

    #======================================================================
    #  PROPERTIES
    #======================================================================

    #----------------------------------------------------------------------
    def __get_cache(self):
        return self._function_cache

    #----------------------------------------------------------------------
    def __get_use_fd_upper_bound(self):
        return self._use_fd_upper_bound

    #----------------------------------------------------------------------
    def __set_use_fd_upper_bound(self, value):
        self._use_fd_upper_bound = value


    #----------------------------------------------------------------------
    functionCache = property(__get_cache)
    """
    Access the function cache for setting properties of the cache.
    """

    #----------------------------------------------------------------------
    useDontCareUpperBound = property(__get_use_fd_upper_bound, __set_use_fd_upper_bound)
    """
    Use the whole dont-care set as upper bound when calculating irrsop.
    """


    def __init__(self, var_wires, dd_mgr, code_generator=None, marduk_vars=None, num_class_vectors=1024, strat_dc=None):
        """
        'var_wires' is supposed to be a dictionary which maps the string representation of a BDD object
        to the corresponding signal in the code generator, for all inputs (and their negations) on which the function(s) to be
        handled by this IrrsopGenerator depend.
        """

        self._dd_mgr = dd_mgr
        self._use_fd_upper_bound = False
        self._code_generator = code_generator
        self._marduk_vars = marduk_vars
        self._function_cache = FunctionCache(marduk_vars, dd_mgr, code_generator, num_class_vectors, strat_dc=strat_dc)

        if var_wires != None:
            self._wires = var_wires
        else:
            self._wires = {}

        self._factor_recursion_depth = 0
        self._num_irrsop_steps = 0
        self._num_factor_steps = 0


    #----------------------------------------------------------------------
    def decompose_bdd(self, f, x):
        """
        Returns the negative and positive cofacter of f w.r.t. x.
        f and x are both given as BDD objects, the cofactors are
        also returned as BDD objects.
        """

        f0 = f / ~x
        f1 = f /  x
        return(f0, f1)


    #----------------------------------------------------------------------
    def compose_cover(self, x, r0, r1, r2):
        """
        Composes the three covers r0, r1, r2 (given as tuples consisting of the BDD objects
        and the corresponding signal of the code generator) in the following way:
        ~x * r0 + x * r1 + r2

        x is given as a BDD object representing a BDD projection function.

        Returns the cover in ZDD (object) representation, and the corresponding signal in the code generator.
        """
        
        result = ~x * r0[0] + x * r1[0] + r2[0]
        
        if len(self._wires) > 0 or self._code_generator != None:
            gen = self._code_generator
            pos_x_wire = self._wires[str(x)]
            neg_x_wire = self._wires[str(~x)]
            pos = gen.add_and((pos_x_wire, r1[1]))
            self._function_cache.update(x * r1[0], pos)
            neg = gen.add_and((neg_x_wire, r0[1]))
            self._function_cache.update(~x * r0[0], neg)
            signal = gen.add_or((pos, neg, r2[1]))            
        else:
            signal = None
        
        return (result, signal)


        
    
