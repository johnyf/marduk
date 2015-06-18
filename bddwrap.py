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
from marduk_utils import MardukException

class BDD(object):
    """
    This class wraps bdd_ptr objects returned from the NuSMV wrapper.
    Thus it is possible to use operator overloading and some sort of
    auto-referencing/dereferencing.

    Create new objects of this class by passing them a bdd_ptr.
    Example:
    my_object = BDD(my_bdd_ptr)

    Notice that the original pointer (my_bdd_ptr) still needs to be
    freed. The BDD class keeps only a duplicate.

    The pointer can later be accessed by using the ptr property.
    Example:
    my_bdd_ptr = my_object.ptr

    Notice that only a duplicate of the internal pointer is returned,
    which must be freed by the caller!    
    """
    

    # Static reference to the "premium" DD Manager, i.e., the one
    # that is first created in and used internally by NuSMV
    # Other managers can be created manually later
    dd_mgr = dd.cvar.dd_manager

    # Static instance counter (for statistical/debugging reasons)
    num_instances = 0

    # List of names of living instances
    living_names_list = []

    def get_one(manager):
        tmp = dd.bdd_one(manager)
        result = BDD(tmp, manager, "one*")
        dd.bdd_free(manager, tmp)
        return result

    def get_zero(manager):
        tmp = dd.bdd_zero(manager)
        result = BDD(tmp, manager, "zero*")
        dd.bdd_free(manager, tmp)
        return result
        
    ONE = staticmethod(get_one)
    ZERO = staticmethod(get_zero)

    def get_manager(self):
        return self.__manager
    mgr = property(get_manager)
    
    def _between(min, max):
        if min.__manager != max.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_between(min.mgr, min.__ptr, max.__ptr)
        result = BDD(tmp, min.mgr)
        dd.bdd_free(result.mgr, tmp)
        return result

    between = staticmethod(_between)

    def get_ith_var(mgr, i):
        ptr = dd.bdd_new_var_with_index(mgr, i)
        result = BDD(ptr, mgr, name="%d-th var" % i)
        dd.bdd_free(mgr, ptr)
        return result
    ith_var = staticmethod(get_ith_var)

    def get_new_var(mgr):
        ptr = dd.bdd_new_var(mgr)
        result = BDD(ptr, mgr, name="new var")
        dd.bdd_free(mgr, ptr)
        return result
    new_var = staticmethod(get_new_var)

    def _living_names(delimiter="\n"):
        result = ""
        for name in BDD.living_names_list:
            result += name + delimiter
        return result
    living_names = staticmethod(_living_names)

    def __init__(self, ptr, manager, name="NO NAME!!", dest_mgr=None):
        """
        Creates a new instance, which wraps the given bdd_ptr.
        A duplicate of the given pointer is created and stored
        internally. Thus the "original" pointer still has to be
        freed by the caller.
        
        If dest_mgr is given, the BDD is transfered to this manager.
        """

        if len(name) > 100:
            name = "long name"
        
        BDD.num_instances += 1
        BDD.living_names_list.append(name)

        if dest_mgr:
            self.__manager = dest_mgr
            self.__ptr = dd.bdd_transfer(manager, dest_mgr, ptr)
        else:
            self.__ptr = dd.bdd_dup(ptr)
            self.__manager = manager

        self.__name = name


    def __del__(self):
        """
        When this (Python) object is garbage collected, the underlying
        C pointer is "freed". (To be more precise: The BDD node is
        dereferenced in CUDD.)
        """
        BDD.num_instances -= 1
        BDD.living_names_list.remove(self.__name)
        dd.bdd_free(self.__manager, self.__ptr)


    def __str__(self):
        return(str(self.__ptr))
        
    def get_ptr(self):
        """
        Returns a duplicate of the bdd_ptr wrapped by this class.
        It is the caller's responsibility to call bdd_free for the
        returned bdd_ptr.
        Returning a duplicate is necessary to protect the internal
        pointer against (accidental) external freeing.
        """
        return dd.bdd_dup(self.__ptr)

    ptr = property(get_ptr)

    
    def get_name(self):
        return self.__name
    def set_name(self, new_name):
        if len(new_name) > 100:
            new_name = "long name"
        if new_name != "":
            BDD.living_names_list[BDD.living_names_list.index(self.__name)] = new_name
            self.__name = new_name
        else:
            raise MardukException("Empty new name not allowed!")
            
    name = property(get_name, set_name)


    def count_minterm(self, num_vars):
        return dd.bdd_count_minterm(self.__manager, self.__ptr, num_vars)
    
    def print_minterm(self):
        dd.bdd_printminterm(self.__manager, self.__ptr)

    def get_minterm_string(self):
        return dd.bdd_printminterm_string(self.__manager, self.__ptr)
    minterm_string = property(get_minterm_string)

    def get_size(self):     
        return dd.bdd_size(self.__manager, self.__ptr)
    size = property(get_size)

    def get_index(self):
        return dd.bdd_index(self.__manager, self.__ptr)
    index = property(get_index)

    def get_level(self):
        return dd.bdd_readperm(self.__manager, self.__ptr)
    level = property(get_level)


    def get_then(self):
        """
        Return a new object representing the "then"-child of this one.
        """
        from marduk_utils import MardukException
        if self.isZero() or self.isOne():
            raise MardukException("Constant node has no THEN-child!")
        return BDD(dd.bdd_then(self.__manager, self.__ptr), self.__manager, "then of " + self.__name)
    THEN = property(get_then)
        
    def get_else(self):
        """
        Return a new object representing the "else"-child of this one.
        """
        from marduk_utils import MardukException
        if self.isZero() or self.isOne():
            raise MardukException("Constant node has no ELSE-child!")
        return BDD(dd.bdd_else(self.__manager, self.__ptr), self.__manager, "else of " + self.__name)
    ELSE = property(get_else)        

    def transfer(self, dest_mgr):
        """
        Transfers the BDD represented by self to the given dest_mgr.
        The resulting BDD object is returned.
        """
        result_ptr = dd.bdd_transfer(self.__manager, dest_mgr, self.__ptr)
        result = BDD(result_ptr, dest_mgr, name='transfer of %s' % self.name)
        dd.bdd_free(dest_mgr, result_ptr)
        return result
    
    def support(self):
        """
        Return a bdd which is build by the product of the variables of the support.
        """
        support_ptr = dd.bdd_support(self.__manager, self.__ptr)
        support =  BDD(support_ptr, self.__manager, name="support of %s" % self.name)
        dd.bdd_free(self.__manager, support_ptr)
        return support
    
    def copy(self):
        """
        Creates and returns a copy of self.
        """
        result = BDD(self.__ptr, self.__manager, "copy of " + self.name)
        return result


    def invert_cube_polarity(self):
        """
        Creates and returns a cube which has all literals in opposite polarity as this one.
        This method might behave unexpectedly when called on a non-cube BDD.
        """
        result = BDD.ONE(self.mgr)

        tmp_cube = self.copy()

        while tmp_cube.isNotOne():
            lit = BDD.ith_var(self.mgr, tmp_cube.index)

            if tmp_cube <= lit:
                result *= ~lit
                tmp_cube /= lit
                continue

            if tmp_cube <= ~lit:
                result *= lit
                tmp_cube /= ~lit
                continue

            # Never reached!
            assert(False)  # If we reach here, we got a non-cube BDD.

        return result

    def swapVariables(self, x, y):
        """
        Swaps two sets of variables of the same size (x and y)
        in the BDD f. The size is given by n. The two sets of variables are
        assumed to be disjoint. The resulting BDD is returned, if successful,
        None otherwise.

        The variable lists x and y are assumed to contain BDD objects, not
        bdd_ptr.
        """
        for var in x + y:
            if self.__manager != var.__manager:
                raise MardukException("Operation on BDDs from different managers not possible!")
        x_list = [var.ptr for var in x]
        y_list = [var.ptr for var in y]
        tuple = (x_list, y_list)
        result_ptr = dd.bdd_swap_variables(self.__manager, self.__ptr, tuple)
        for ptr in x_list:
            dd.bdd_free(self.__manager, ptr)
        for ptr in y_list:
            dd.bdd_free(self.__manager, ptr)
        result = BDD(result_ptr, self.__manager, "swap_vars*")
        dd.bdd_free(self.__manager, result_ptr)
        return result

    def compose(self, var, func):
        """
        Substitutes func for var in the BDD for self and returns the result.
        """
        if var.__manager != self.__manager or func.__manager != self.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        index = dd.bdd_index(self.__manager, var.__ptr)        
        result_ptr = dd.bdd_compose(self.__manager, self.__ptr, func.__ptr, index)
        result = BDD(result_ptr, self.__manager, "compose*")
        dd.bdd_free(self.__manager, result_ptr)
        return result
    
    def exists(self, vars_cube):
        """
        Existentially abstracts all variables in vars_cube from the bdd. 
        Returns the abstracted BDD if successful; a failure is generated
        otherwise.

        The variables vars_cube is assumed to contain a BDD object, not 
        bdd_ptr.
        """
        if self.__manager != vars_cube.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        result_ptr = dd.bdd_forsome(self.__manager, self.__ptr, vars_cube.__ptr)
        result = BDD(result_ptr, self.__manager, "exists*")
        dd.bdd_free(self.__manager, result_ptr)
        return result

    def forall(self, vars_cube):
        """
        Universally abstracts all vars in vars_cube from the bdd. 
        Returns the abstracted BDD if successful; a failure is generated
        otherwise.

        The variables vars_cube is assumed to contain a BDD object, not 
        bdd_ptr.
        """
        if self.__manager != vars_cube.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")        
        result_ptr = dd.bdd_forall(self.__manager,self.__ptr,vars_cube.__ptr)
        result = BDD(result_ptr, self.__manager, "forall*")
        dd.bdd_free(self.__manager, result_ptr)
        return result

    def andExists(self, bdd2, vars_cube):
        """
        Takes the AND of two BDDs and simultaneously abstracts
        the variables in vars_cube. The variables are existentially abstracted.
        Returns a pointer to the result if successful; a failure is
        generated otherwise.

        The variables vars_cube and the bdd2 are assumed to contain 
        BDD objects, not bdd_ptr.
        """
        if self.__manager != bdd2.__manager or self.__manager != vars_cube.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        result_ptr = dd.bdd_and_abstract(self.__manager,self.__ptr,bdd2.__ptr,vars_cube.__ptr)
        result = BDD(result_ptr, self.__manager,"andExists*")
        dd.bdd_free(self.__manager, result_ptr)
        return result


    def calculate_value(self, values):
        """
        Computes the value of the BDD for the given variable assignment.
        If the length of the given list is one less than the number of
        indices, a 0 will be prepended to work around the mysterious
        NuSMV variable with index 0.

        If the length of the list is not equal to the number of indices
        or the number of indices minus 1, an exception is raised.
        """

        num_indices = dd.dd_get_size(self.__manager)
        
        if len(values) == num_indices:
            return dd.calculate_bdd_value(self.__manager, self.__ptr, values)
        elif len(values) + 1 == num_indices:
            return dd.calculate_bdd_value(self.__manager, self.__ptr, [0] + values)
        else:
            raise MardukException("Cannot compute BDD value with %d variables, when there are %d indices." % (len(values), num_indices))

        
    def implies(self, right_side):
        """
        Returns a BDD for 'self -> right_side' (read: "self implies right_side").
        """

        return ~self + right_side

    ###############################################################

    def isOne(self):
        result = dd.bdd_is_one(self.__manager, self.__ptr)
        return result != 0

    def isNotOne(self):
        result = dd.bdd_isnot_one(self.__manager, self.__ptr)
        return result != 0

    def isZero(self):
        result = dd.bdd_is_zero(self.__manager, self.__ptr)
        return result != 0

    def isNotZero(self):
        result = dd.bdd_isnot_zero(self.__manager, self.__ptr)
        return result != 0


    
    ###############################################################
    # OPERATOR OVERLOADING
    # This section defines functions for operator overloading.
    ###############################################################
    
    def __eq__(self, other):
        """
        Overloads: ==
        Returns true iff the other BDD equals this one, i.e. if
        the have the same internal pointer.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        return self.__ptr == other.__ptr

    
    def __ne__(self, other):
        """
        Overloads: !=
        Returns true iff the other BDD is different to this one,
        i.e. does not have the same internal pointer.
        """
        result = self.__eq__(other)
        if result is NotImplemented:
            return result
        return not result
    
    #------------------------------------------------------------

    def __le__(self, other):
        """
        Overloads: <=
        Returns True if self is less than or equal to other; False otherwise.
        """
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")        
        result = dd.bdd_leq(self.__manager, self.__ptr, other.__ptr)
        return result != 0

    def __ge__(self, other):
        """
        Overloads: >=
        Returns True if self is greater than or equal to other; False otherwise.
        Remark: Uses method bdd_leq, but with parameters in reverse order.
        """
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        result = dd.bdd_leq(self.__manager, other.__ptr, self.__ptr)
        return result != 0    


    #------------------------------------------------------------

    def __lt__(self, other):
        """
        Overloads: <
        Returns True if self is less than (and NOT equal) to other; False otherwise.
        """
        return self <= other and not self == other


    def __gt__(self, other):
        """
        Overloads: >
        Returns True if self is greater than (and NOT equal) to other; False otherwise.
        """
        return self >= other and not self == other
    
    #------------------------------------------------------------
    def __or__(self, other):
        """
        Overloads: |
        Returns the result of the OR operation of self and other.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_or(self.__manager, self.__ptr, other.__ptr)
        result = BDD(tmp, self.__manager, "(" + self.name + " + " + other.name + ")")
        dd.bdd_free(self.__manager, tmp)
        return result

    def __ior__(self, other):
        """
        Overloads: |=
        Stores the result of the OR operation of self and other
        in this object.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_or(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager, self.__ptr)
        self.__ptr = tmp

        
    def __add__(self, other):
        """
        Overloads: +
        Returns the same as __or__
        """
        if not isinstance(other, BDD):
            return NotImplemented
        return self | other

    def __iadd__(self, other):
        """
        Overloads: +=
        Stores the result of the OR operation of self and other
        in this object.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_or(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager, self.__ptr)
        self.__ptr = tmp
        return self

    #-------------------------------------------------------------
    
    def __and__(self, other):
        """
        Overloads: &
        Returns the result of the AND operation of self and other.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_and(self.__manager, self.__ptr, other.__ptr)
        result = BDD(tmp, self.__manager, "(" + self.name + " * " + other.name + ")")
        dd.bdd_free(self.__manager, tmp)
        return result

    def __iand__(self, other):
        """
        Overloads: &=
        Stores the result of the AND operation of self and other
        in this object.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_and(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager, self.__ptr)
        self.__ptr = tmp
        return self

    def __mul__(self, other):
        """
        Overloads: *
        Returns the same as __and__
        """
        if not isinstance(other, BDD):
            return NotImplemented
        return self & other

    def __imul__(self, other):
        """
        Overloads: *=
        Stores the result of the AND operation of self and other
        in this object.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_and(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager,self.__ptr)
        self.__ptr = tmp
        return self

    
    #-------------------------------------------------------------

    def __xor__(self, other):
        """
        Overloads: ^
        Returns the result of the XOR operation of self and other.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_xor(self.__manager, self.__ptr, other.__ptr)
        result = BDD(tmp, self.__manager, "xor*")
        dd.bdd_free(self.__manager, tmp)
        return result

    def __ixor__(self, other):
        """
        Overloads: ^=
        Stores the result of the XOR operation of self and other
        in this object.
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_xor(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager, self.__ptr)
        self.__ptr = tmp
        return self
    

    #-------------------------------------------------------------

    def  __invert__(self):
        """
        Overloads: ~
        Returns the result of the NOT operation of self.
        """
        tmp = dd.bdd_not(self.__manager, self.__ptr)
        result = BDD(tmp, self.__manager, "!" + self.name)
        dd.bdd_free(self.__manager, tmp)
        return result

    #-------------------------------------------------------------
    
    def __div__(self, other):
        """
        Overloads: /
        Returns the result of the COFACTOR operation of self and other.
        (For generality NuSMV uses CONSTRAIN internally)
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_cofactor(self.__manager, self.__ptr, other.__ptr)
        result = BDD(tmp, self.__manager, "cof*")
        dd.bdd_free(self.__manager, tmp)
        return result

    def __idiv__(self, other):
        """
        Overloads: /=
        Stores the result of the COFACTOR operation of self and other
        in this object. (For generality NuSMV uses CONSTRAIN internally)
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_cofactor(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager, self.__ptr)
        self.__ptr = tmp
        return self
    

    
    def __floordiv__(self, other):
        """
        Overloads: //
        Returns the result of the RESTRICT operation (cf. Coudert et al., ICCAD90)
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_minimize(self.__manager, self.__ptr, other.__ptr)
        result = BDD(tmp, self.__manager, "restrict*")
        dd.bdd_free(self.__manager, tmp)
        return result

    def __ifloordiv__(self, other):
        """
        Overloads: //=
        Stores the result of the RESTRICT operation of self and other
        in this object. (cf. Coudert et al., ICCAD90)
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")
        tmp = dd.bdd_minimize(self.__manager, self.__ptr, other.__ptr)
        dd.bdd_free(self.__manager, self.__ptr)
        self.__ptr = tmp
        return self


    #--------------------------------------------------------------

    
    def iff(self, other):
        """
        Computes the BDD for (self <-> other).
        """
        if not isinstance(other, BDD):
            return NotImplemented
        if self.__manager != other.__manager:
            raise MardukException("Operation on BDDs from different managers not possible!")

        return ((self * other) + ((~self) * (~other)))
