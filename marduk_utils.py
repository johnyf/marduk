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


"""
This module contains utility classes and functions used by Marduk.
"""

class Variable(object):
    """
    This class stores all information connected to a variable in Marduk's synthesis process,
    including variable name, type (input, output, state [used to be 'jx' in Anzu]), BDD pointers
    to present and next state instances.
    """

    def __init__(self, name, type, ps_bdd_ptr, ns_bdd_ptr):
        self.__name = name
        if  type in [VariableType.INPUT, VariableType.OUTPUT, VariableType.STATE]:
            self.__type = type
        else:
            self.__type = VariableType.UNKNOWN
        self.__ps_bdd_ptr = ps_bdd_ptr
        self.__ns_bdd_ptr = ns_bdd_ptr

    def __str__(self):
        type = "UNKNOWN"
        if self.__type == VariableType.INPUT:
            type = "INPUT"
        elif self.__type == VariableType.OUTPUT:
            type = "OUTPUT"
        elif self.__type == VariableType.STATE:
            type = "STATE"
            
        string = "Name: %s\nType: %s\nps: %s\nns: %s" % (self.__name, type, self.__ps_bdd_ptr, self.__ns_bdd_ptr)
        return string
        
        
    def get_name(self):
        return self.__name
    name = property(get_name)
        
    def get_type(self):
        return self.__type
    type = property(get_type)
    
    def get_ps_bdd_ptr(self):
        return self.__ps_bdd_ptr
    ps = property(get_ps_bdd_ptr)
    
    def get_ns_bdd_ptr(self):
        return self.__ns_bdd_ptr
    ns = property(get_ns_bdd_ptr)


class VariableType(object):
    """Enum for variable types"""
    UNKNOWN = 0
    INPUT = 1
    OUTPUT = 2
    STATE = 3
    
class Modes(object):
    """Enum for modes"""
    UNKNOWN         = 0
    COFACTOR        = 1
    IRRSOP          = 2
    FACTOR          = 3
    OLD             = 4

class Languages(object):
    """Enum for modes"""
    UNKNOWN         = 0
    BLIF            = 1
    VERILOG         = 2
    HIF             = 3

class MardukException(Exception):
    """
    Base class for all Marduk exceptions
    """
    def __init__(self, string):
        self.message = string
        Exception(self, string)


def comp_name_bdd_tuples(t1, t2):
    """
    This function expects two tuples of a name (string) and a bdd_ptr, and
    compares the indices of the bdd_ptr.
    It is to be used to sort lists of variables according to the bdd ordering.
    The given tuples must contain a third object: The corresponding DD Manager.
    """
    from nusmv import dd
    from bddwrap import BDD
    i1 = dd.bdd_index(t1[2], t1[1])
    i2 = dd.bdd_index(t2[2], t2[1])

    if i1 < i2:
        return -1
    elif i1 == i2:
        return 0
    else:
        return 1

def comp_string_int_tuples(t1, t2):
    """
    This functions compares a tuple consisting of a string and an integer according to the integer.
    """
    return comp_tuples_according_to_second_element(t1, t2)

def comp_tuples_according_to_second_element(t1,t2):
    """
    Compares tuples according to their second element. (The one with index 1.)
    """
    if t1[1] < t2[1]:
        return -1
    elif t1 == t2:
        return 0
    else:
        return 1

def comp_bdd_objs(o1, o2):
    """
    Compares two bdd objects according to their indices
    """
    from bddwrap import BDD
    i1 = o1.index
    i2 = o2.index

    if i1 < i2:
        return -1
    elif i1 == i2:
        return 0
    else:
        return 1

def get_init_value_from_bdd(var, init):
    """
    This function takes a variable and a BDD representing an initial state
    and extracts the initial value of the variable in the BDD.
    The value is returned as integer.
    """
    from bddwrap import BDD

    var_zero = init * ~(var.ps)
    var_one = init * var.ps

    if var_one.isZero():
        if var_zero.isNotZero():
            return 0
        else:
            raise MardukException("Encountered illegal initial value for variable '%s' in BDD!" % var.name)
    else:
        if var_zero.isZero():
            return 1
        else:
            print("Initial value of variable '%s' is free. Assuming it to be '0'."  % var.name)
            return 0


def dump_brel(relation, input_vars, output_vars, filename):
    """
    Dumps the given relation into the given file, using the
    format used by the BREL relation solver.
    """

    file = open(filename, 'w')

    file.write(".i %d\n" % len(input_vars))
    file.write(".o %d\n" % len(output_vars))
    
    _dump_brel_input_recur(relation, input_vars, output_vars, '', file)

    file.write(".e\n")
    file.close()

    
def _dump_brel_input_recur(relation, input_vars, output_vars, term, file):
    """
    Performs the recursive step of dump_brel over inputs
    """

    if input_vars == []:
        file.write(term + " ")
        _dump_brel_output_recur(relation, output_vars, '', file)
        file.write("\n")
        return
    
    var = input_vars[0]

    pos = relation / var
    neg = relation / ~var
    
    rel = pos * neg
    if rel.isNotZero():
        _dump_brel_input_recur(rel, input_vars[1:], output_vars, term + "-", file)   # -

    rel = ~pos * neg
    if rel.isNotZero():
        _dump_brel_input_recur(rel, input_vars[1:], output_vars, term + "0", file)  # 0

    rel = pos * ~neg
    if rel.isNotZero():
        _dump_brel_input_recur(rel, input_vars[1:], output_vars, term + "1", file)  # 1


    
def _dump_brel_output_recur(relation, output_vars, term, file):
    """
    Performs the recursive stop of dump_brel over outputs.
    """

    if output_vars == []:
        file.write(term + " ")
        return

    var = output_vars[0]

    pos = relation / var
    neg = relation / ~var

    rel = pos * neg
    if rel.isNotZero():
        _dump_brel_output_recur(rel, output_vars[1:], term + "-", file)   # -

    rel = ~pos * neg
    if rel.isNotZero():        
        _dump_brel_output_recur(rel, output_vars[1:], term + "0", file)  # 0

    rel = pos * ~neg
    if rel.isNotZero():        
        _dump_brel_output_recur(rel, output_vars[1:], term + "1", file)  # 1
    

        
def relation_freedom_ratio(relation, input_vars, output_vars):
    """
    Returns the ratio, how much the given relation is "over-defined", i.e.
    the number of vertexes in it, versus the number of vertexes a function with
    the given number of inputs would have.
    Assumes that the given relation is well-defined.
    """
    from nusmv import dd
    from bddwrap import BDD

    num_in = len(input_vars)
    num_out = len(output_vars)

    ptr = relation.ptr
    num_rel_minterms = dd.bdd_count_minterm(relation.mgr, ptr, num_in + num_out)
    dd.bdd_free(relation.mgr, ptr)

    num_func_minterms = 2 ** num_in

    return num_rel_minterms / num_func_minterms


def characterize_relation(relation, input_vars, output_vars, return_bdds=False):
    """
    Returns a dictionary containing the following data about the given relation:
    num_inputs, num_outputs, num_defined (the number of input vertices
    for which the relation is defined), num_fixed (number of input vertices for which
    the output is fixed), num_dc (number of input_vertices for which the output can be
    written as a DC term), num_non_dc (number of input vertices for which the output is
    not fixed and cannot be written as a DC term).

    REMARK: The loops for computing the constant vertices and the DC vertices can possibly
            be merged.

    If return_bdds is True, also BDDs representing the set of fixed/dc/non-dc vertices will
    be returned.
    """
    from bddwrap import BDD
    result = {}
    
    num_inputs = len(input_vars)
    result['num_inputs'] = num_inputs
    result['num_outputs'] = len(output_vars)

    output_product = BDD.ONE(relation.mgr)
    for output in output_vars:
        output_product *= output

    # Compute number of defined vertices
    
    defined = relation
    for output in output_vars:
        defined = defined.exists(output)
        
    result['num_defined'] = defined.count_minterm(num_inputs)


    # compute constants vertices

    fixed_vertices = BDD.ONE(relation.mgr)
    
    for output in output_vars:
        (lower, upper) = get_lower_upper(output, relation, input_vars, output_vars)
        
        fixed_vertices *= ~(lower ^ upper)
        del lower, upper

    result['num_fixed'] = fixed_vertices.count_minterm(num_inputs)
    if not return_bdds:
        del fixed_vertices
    
    # compute non DC vertices

    non_dc_vertices = BDD.ZERO(relation.mgr)

    for output in output_vars:
        (lower, upper) = get_lower_upper(output, relation, input_vars, output_vars)
        tmp_rel = relation * (lower ^ upper)   # Cut off constant vertices
        
        rel_lower = tmp_rel.compose(output, lower)
        rel_upper = tmp_rel.compose(output, upper)


        tmp_non_dc = ((~rel_lower)*tmp_rel).exists(output_product)

        tmp_non_dc += ((~rel_upper)*tmp_rel).exists(output_product)

        
        
        non_dc_vertices += tmp_non_dc
        del tmp_non_dc, tmp_rel, rel_lower, rel_upper, lower, upper

    result['num_non_dc'] = non_dc_vertices.count_minterm(num_inputs)


    if not return_bdds:
        del non_dc_vertices
    else:
        dc_vertices = relation
        for output in output_vars:
            dc_vertices = dc_vertices.exists(output)
        dc_vertices *= ~(fixed_vertices + non_dc_vertices)
        result['fixed_bdd'] = fixed_vertices
        result['non_dc_bdd'] = non_dc_vertices
        result['dc_bdd'] = dc_vertices

    result['num_dc'] = (2 ** num_inputs) - (result['num_fixed'] + result['num_non_dc'])
    return result


def get_lower_upper(output, relation, input_vars, output_vars):
    """
    Computes the lower and the upper bound for output in relation.
    """
    rel_prime = relation
    for other in output_vars:
        if other != output:
            rel_prime = rel_prime.exists(other)

    pos = rel_prime / output
    neg = rel_prime / ~output

    lower = pos * ~neg
    upper = ~neg + pos
    
    return (lower, upper)
    


def reorder_method_to_string(method):
    """
    Takes a reorder method (integer) and returns the corresponding string.
    """

    from nusmv import dd
    
    if method == dd.REORDER_SAME:
        return "SAME"
    elif method == dd.REORDER_NONE:
        return "NONE"
    elif method == dd.REORDER_RANDOM:
        return "RANDOM"
    elif method == dd.REORDER_RANDOM_PIVOT:
        return "RANDOM_PIVAT"
    elif method == dd.REORDER_SIFT:
        return "SIFT"
    elif method == dd.REORDER_SIFT_CONV:
        return "SIFT_CONV"
    elif method == dd.REORDER_SYMM_SIFT:
        return "SYMM_SIFT"
    elif method == dd.REORDER_SYMM_SIFT_CONV:
        return "SYMM_SIFT_CONV"
    elif method == dd.REORDER_WINDOW2:
        return "WINDOW2"
    elif method == dd.REORDER_WINDOW3:
        return "WINDOW3"
    elif method == dd.REORDER_WINDOW4:
        return "WINDOW4"
    elif method == dd.REORDER_WINDOW2_CONV:
        return "WINDOW2_CONV"
    elif method == dd.REORDER_WINDOW3_CONV:
        return "WINDOW3_CONV"
    elif method == dd.REORDER_WINDOW4_CONV:
        return "WINDOW4_CONV"
    elif method == dd.REORDER_GROUP_SIFT:
        return "GROUP_SIFT"
    elif method == dd.REORDER_GROUP_SIFT_CONV:
        return "GROUP_SIFT_CONV"
    elif method == dd.REORDER_ANNEALING:
        return "ANNEALING"
    elif method == dd.REORDER_GENETIC:
        return "GENETIC"
    elif method == dd.REORDER_LINEAR:
        return "LINEAR"
    elif method == dd.REORDER_LINEAR_CONV:
        return "LINEAR_CONVERGE"
    elif method == dd.REORDER_EXACT:
        return "EXACT"
    else:
        raise MardukException("Unknown reordering method '%d'!" % method)

        
def print_variable_ordering(var_list):
    """
    Creates a string representing the current variable ordering in the CUDD package.
    The string will look like "var1_ps -> var3_ns -> ... "
    Expects a Marduk-style variable list as argument.
    """

    from nusmv import dd
    from bddwrap import BDD
    
    
    order_list = []
    
    for var in var_list:
        ps_ptr = var.ps.ptr
        ns_ptr = var.ns.ptr
        ps_tuple = (var.name + "_ps", dd.bdd_readperm(var.ps.mgr, ps_ptr))
        ns_tuple = (var.name + "_ns", dd.bdd_readperm(var.ns.mgr, ns_ptr))
        dd.bdd_free(var.ps.mgr, ps_ptr)
        dd.bdd_free(var.ns.mgr, ns_ptr)
        order_list.append(ps_tuple)
        order_list.append(ns_tuple)

    order_list.sort(cmp=comp_string_int_tuples)

    result = ""
    for tuple in order_list:
        result = result + tuple[0] + " -> "

    result = result[0:-4]
    return result
        
def set_variable_ordering(order_string, marduk_vars, dd_mgr):
    """
    Forces the variable ordering in the given DD manager to the order
    given via 'order_string'. This string should be formatted as the one
    which is returned by utils.print_variable_ordering.
    The given list of marduk_vars is used to find the BDD indices corresponding
    to the strings.
    """
    import re
    from nusmv import dd
    order_string = re.sub(r'\s','',order_string)
    string_list = order_string.split('->')

    int_list = [0]

    #print string_list
    for string in string_list:
        for var in marduk_vars:
            stripped = re.sub('_[pn]s$','',string)
            if re.search('_ps', string):
                if stripped == var.name:
                    int_list.append(var.ps.index)
                    break
            elif re.search('_ns', string):
                if stripped == var.name:
                    int_list.append(var.ns.index)
                    break
    if len(int_list) != 2*len(marduk_vars) + 1:
        raise Exception('set_variable_order:\n Num vars: %d\n Level list length: %d' % (len(marduk_vars), len(int_list)))
    dd.dd_set_order(dd_mgr, int_list)
    


def top_variable(f, fd):
    """
    Takes two BDD objects and returns the projection function (as BDD object) of the
    variable with the highest level in the union of the supports of f and fd.
        """
    from nusmv import dd
    from bddwrap import BDD
    if f.mgr != fd.mgr:
        raise MardukException("Cannot find top variable of 2 BDDs from different managers!")
    
    if f.level < fd.level:
        tmp = dd.bdd_new_var_with_index(f.mgr, f.index)
    else:
        tmp = dd.bdd_new_var_with_index(f.mgr, fd.index) 
            
    result = BDD(tmp, f.mgr)
    dd.bdd_free(f.mgr, tmp)

    return result
    
