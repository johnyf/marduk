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


## ATTENTION: This class has not yet been ported to the new way of handling multiple DD managers.
##            Consequently it is currently not used anywhere, and should not be used until it is ported.

from nusmv import dd

class ZDD(object):
    """
    This class wraps zdd_ptr objects returned from the NuSMV wrapper.
    Thus it is possible to use operator overloading and some sort of
    auto-referencing/dereferencing.

    Create new objects of this class by passing them a zdd_ptr.
    Example:
    my_object = ZDD(my_zdd_ptr)

    Notice that the original pointer (my_zdd_ptr) still needs to be
    freed. The ZDD class keeps only a duplicate.

    The pointer can later be accessed by using the ptr property.
    Example:
    my_zdd_ptr = my_object.ptr

    Notice that only a duplicate of the internal pointer is returned,
    which must be freed by the caller!    
    """
    

    # Static reference to the DD Manager and the basic constants
    mgr = dd.cvar.dd_manager

    def get_one():
        tmp = dd.zdd_one(ZDD.mgr)
        result = ZDD(tmp)
        dd.zdd_free(ZDD.mgr, tmp)
        return result

    def get_zero():
        tmp = dd.zdd_zero(ZDD.mgr)
        result = ZDD(tmp)
        dd.zdd_free(ZDD.mgr, tmp)
        return result
        
    ONE = staticmethod(get_one)
    ZERO = staticmethod(get_zero)


    def __init__(self, ptr):
        """
        Creates a new instance, which wraps the given zdd_ptr.
        A duplicate of the given pointer is created and stored
        internally. Thus the "original" pointer still has to be
        freed by the caller.
        
        """
        self.__ptr = dd.zdd_dup(ptr)


    def __del__(self):
        """
        When this (Python) object is garbage collected, the underlying
        C pointer is "freed". (To be more precise: The ZDD node is
        dereferenced in CUDD.)
        """
        #print "Attempting to free pointer", self.__ptr
        #self.print_minterm()
        dd.zdd_free(ZDD.mgr, self.__ptr)
        #print "DEBUG: Freeing pointer", self.__ptr



    def get_ptr(self):
        """
        Returns a duplicate of the zdd_ptr wrapped by this class.
        It is the caller's responsibility to call zdd_free for the
        returned zdd_ptr.
        Returning a duplicate is necessary to protect the internal
        pointer against (accidental) external freeing.
        """
        return dd.zdd_dup(self.__ptr)

    ptr = property(get_ptr)


    def get_size(self):     
        return dd.zdd_size(self.__ptr)

    size = property(get_size)

    def print_minterm(self):
        dd.zdd_printminterm(ZDD.mgr, self.__ptr)
    
    def copy(self):
        """
        Creates and returns a copy of self.
        """
        result = ZDD(self.__ptr)
        return result


    def __str__(self):
        return(str(self.__ptr))
    



    ###############################################################

    def isOne(self):
        result = dd.zdd_is_one(ZDD.mgr, self.__ptr)
        return result != 0

    def isNotOne(self):
        result = dd.zdd_isnot_one(ZDD.mgr, self.__ptr)
        return result != 0

    def isZero(self):
        result = dd.zdd_is_zero(ZDD.mgr, self.__ptr)
        return result != 0

    def isNotZero(self):
        result = dd.zdd_isnot_zero(ZDD.mgr, self.__ptr)
        return result != 0



    def to_bdd(self):
        """
        Returns a BDD object for the function represented by
        this (=self) ZDD cover.
        """
        from bddwrap import BDD
        tmp = dd.zdd_cover_to_bdd(ZDD.mgr, self.__ptr)
        result = BDD(tmp)
        dd.bdd_free(BDD.mgr, tmp)
        return result

    
    ###############################################################
    # OPERATOR OVERLOADING
    # This section defines functions for operator overloading.
    ###############################################################
    
    def __eq__(self, other):
        """
        Overloads: ==
        Returns true iff the other ZDD equals this one, i.e. if
        the have the same internal pointer.
        """
        if not isinstance(other, ZDD):
            return NotImplemented

        return self.__ptr == other.__ptr

    
    def __ne__(self, other):
        """
        Overloads: !=
        Returns true iff the other ZDD is different to this one,
        i.e. does not have the same internal pointer.
        """
        result = self.__eq__(other)
        if result is NotImplemented:
            return result
        return not result
    
    #------------------------------------------------------------

    def __or__(self, other):
        """
        Overloads: |
        Returns the result of the OR operation of self and other.
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        tmp = dd.zdd_or(ZDD.mgr, self.__ptr, other.__ptr)
        result = ZDD(tmp)
        dd.zdd_free(ZDD.mgr, tmp)
        return result

    def __ior__(self, other):
        """
        Overloads: |=
        Stores the result of the OR operation of self and other
        in this object.
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        tmp = dd.zdd_or(ZDD.mgr, self.__ptr, other.__ptr)
        dd.zdd_free(ZDD.mgr, self.__ptr)
        self.__ptr = tmp

        
    def __add__(self, other):
        """
        Overloads: +
        Returns the same as __or__
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        return self | other

    def __iadd__(self, other):
        """
        Overloads: +=
        Stores the result of the OR operation of self and other
        in this object.
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        tmp = dd.zdd_or(ZDD.mgr, self.__ptr, other.__ptr)
        dd.zdd_free(ZDD.mgr, self.__ptr)
        self.__ptr = tmp
        return self

    #-------------------------------------------------------------
    
    def __and__(self, other):
        """
        Overloads: &
        Returns the result of the AND operation of self and other.
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        tmp = dd.zdd_and(ZDD.mgr, self.__ptr, other.__ptr)
        result = ZDD(tmp)
        dd.zdd_free(ZDD.mgr, tmp)
        return result

    def __iand__(self, other):
        """
        Overloads: &=
        Stores the result of the AND operation of self and other
        in this object.
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        tmp = dd.zdd_and(ZDD.mgr, self.__ptr, other.__ptr)
        dd.zdd_free(ZDD.mgr, self.__ptr)
        self.__ptr = tmp
        return self

    def __mul__(self, other):
        """
        Overloads: *
        Returns the same as __and__
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        return self & other

    def __imul__(self, other):
        """
        Overloads: *=
        Stores the result of the AND operation of self and other
        in this object.
        """
        if not isinstance(other, ZDD):
            return NotImplemented
        tmp = dd.zdd_and(ZDD.mgr, self.__ptr, other.__ptr)
        dd.zdd_free(ZDD.mgr,self.__ptr)
        self.__ptr = tmp
        return self

    
    #-------------------------------------------------------------

    def  __invert__(self):
        """
        Overloads: ~
        Returns the result of the NOT operation of self.
        """
        tmp = dd.zdd_not(ZDD.mgr, self.__ptr)
        result = ZDD(tmp)
        dd.zdd_free(ZDD.mgr, tmp)
        return result

    #-------------------------------------------------------------

    def cofactor(self, var, pol):
        """
        Returns the positive (pol=1) or the negative (pol=0)
        cofactor of self with var. Var must be given as an integer
        (index of the respective var).
        """
        tmp = dd.zdd_cofactor(ZDD.mgr, self.__ptr, var, pol)
        result = ZDD(tmp)
        dd.zdd_free(ZDd.mgr, tmp)
        return result
    
    
