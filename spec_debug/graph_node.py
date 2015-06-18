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
Contains a class that represents a node in the summarizing graph.
"""

from bddwrap import BDD

class GraphNode(object):
    """
    Represents a node in the summarizing graph.

    This class represents a node in the graph which summarizes all
    sequences of inputs and outputs that are possible when the
    environment adheres to the counterstrategy (or the countertrace).
    Such a node contains references to its successors and predecessors.
    It is also able to print itself in DOT-format. The DOT-program can
    then be used to create nice pictures of the graph.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """

    def __init__(self, utils):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: A bdd that represents the state of this node.
        #:
        #: A bdd which represents the setting of the input- and output
        #: variables corresponding to this node
        #: @type: L{BDD}
        self.__bdd = None

        #: A bdd that represents the next input from this state.
        #: 
        #: A bdd which represents the setting of the next input variables
        #: in the state corresponding to this node.
        #: @type: L{BDD}
        self.__next_input = None

        #: The decimal value of ix.
        #: @type: int
        self.__ix_val = None

        #: The decimal value of jx.
        #: @type: int
        self.__jx_val = None

        #: All environment fairness constraints which are fulfilled in this
        #: node.
        #:
        #: A comma separated string that contains the indices of all
        #: fairness constraints of the environment which are fulfilled in
        #: this state.
        #: @type: string
        self.__env_fulfilled = None

        #: All system fairness constraints which are fulfilled in this node.
        #:
        #: A comma separated string that contains the indices of all
        #: fairness constraints of the system which are fulfilled in
        #: this state.
        #: @type: string
        self.__sys_fulfilled = None

        #: A unique name of the node.
        #: @type: string
        self.__name = None

        #: A list of successor nodes.
        #: @type: list<GraphNode> 
        self.__successors = []

        #: A list of predecessor nodes.
        #: @type: list<GraphNode> 
        self.__predecessors = []

        #: The maximal number of changes of jx in the sequel of the play.
        #: @type: int 
        self.__jx_changes = None

        #: All next inputs that should be printed in the node.
        #: 
        #: A dictionary mapping from variable names to their values. It
        #: contains next input variables which should be printed.
        self.__next_inputs_to_print = {}

 
    def set_bdd(self, bdd):
        """
        Sets the bdd that represents the state of this node.

        This method sets the bdd which represents the setting of the
        input- and output variables corresponding to this node.

        @param bdd: The bdd which represents the setting of the input- and
               output variables corresponding to this node.
        @type bdd: L{BDD}
        """
        self.__bdd = bdd

    def get_bdd(self):
        """
        Returns the bdd that represents the state of this node.

        This method returns the bdd which represents the setting of the
        input- and output variables corresponding to this node.

        @return: The bdd which represents the setting of the input- and
                 output variables corresponding to this node.
        @rtype: L{BDD}
        """
        return self.__bdd

    #: The bdd that represents the state of this node.
    #: @type: L{BDD}
    bdd = property(get_bdd, set_bdd)

    def set_next_input(self, next_input):
        """
        Sets the next input from this state.

        This method sets the bdd which represents the next input from the
        state represented by this node.

        @param next_input: The bdd which represents the next input from the
               state represented by this node.
        @type next_input: L{BDD}
        """
        self.__next_input = next_input

    def get_next_input(self):
        """
        Returns the next input from this state.

        This method sets the bdd which represents the next input from the
        state represented by this node.

        @return: The bdd which represents the next input from the state
                 represented by this node.
        @rtype: L{BDD}
        """
        return self.__next_input

    #: The next input from this state.
    #: @type: L{BDD}
    next_input = property(get_next_input, set_next_input)

    def set_ix_val(self, ix):
        """
        Sets the decimal value of ix for this node.

        @param ix: The decimal value of ix for this node.
        @type ix: int
        """
        self.__ix_val = ix

    def get_ix_val(self):
        """
        Returns the decimal value of ix for this node.

        @return: The decimal value of ix for this node.
        @rtype: int
        """
        return self.__ix_val

    #: The decimal value of ix for this node.
    #: @type: int
    ix_val = property(get_ix_val, set_ix_val)

    def set_jx_val(self, jx):
        """
        Sets the decimal value of jx for this node.

        @param jx: The decimal value of jx for this node.
        @type jx: int
        """
        self.__jx_val = jx

    def get_jx_val(self):
        """
        Returns the decimal value of jx for this node.

        @return: The decimal value of jx for this node.
        @rtype: int
        """
        return self.__jx_val

    #: The decimal value of jx for this node.
    #: @type: int
    jx_val = property(get_jx_val, set_jx_val)


    def set_fulfilled_env(self, env_fulfilled):
        """
        Sets the environment fairness constraints which are fulfilled in this
        state.

        This method sets a comma separated string that contains the indices
        of all fairness constraints of the environment which are fulfilled
        in this state.

        @param env_fulfilled: A comma separated string that contains the
               indices of all fairness constraints of the environment
               which are fulfilled in this state.
        @type env_fulfilled: string
        """
        self.__env_fulfilled = env_fulfilled

    def get_fulfilled_env(self):
        """
        Returns the environment fairness constraints which are fulfilled in
        this state.

        This method sets a comma separated string that contains the indices
        of all fairness constraints of the environment which are fulfilled
        in this state.

        @return: A comma separated string that contains the
                 indices of all fairness constraints of the environment
                 which are fulfilled in this state.
        @rtype: string
        """
        return self.__env_fulfilled

    #: The environment fairness constraints which are fulfilled in this state.
    #: @type: string
    fulfilled_env = property(get_fulfilled_env, set_fulfilled_env)

    def set_fulfilled_sys(self, sys_fulfilled):
        """
        Sets the system fairness constraints which are fulfilled in this state.

        This method sets a comma separated string that contains the indices
        of all fairness constraints of the system which are fulfilled
        in this state.

        @param sys_fulfilled: A comma separated string that contains the
               indices of all fairness constraints of the system
               which are fulfilled in this state.
        @type sys_fulfilled: string
        """
        self.__sys_fulfilled = sys_fulfilled

    def get_fulfilled_sys(self):
        """
        Returns the system fairness constraints which are fulfilled in this
        state.

        This method sets a comma separated string that contains the indices
        of all fairness constraints of the system which are fulfilled
        in this state.

        @return: A comma separated string that contains the
                 indices of all fairness constraints of the system
                 which are fulfilled in this state.
        @rtype: string
        """
        return self.__sys_fulfilled

    #: The system fairness constraints which are fulfilled in this state.
    #: @type: string
    fulfilled_sys = property(get_fulfilled_sys, set_fulfilled_sys)

    def set_name(self, name):
        """
        Sets the name of the node.

        @param name: The name of the node.
        @type name: string
        """
        self.__name = name

    def get_name(self):
        """
        Returns the name of the node.

        @return: The name of the node.
        @rtype: string
        """
        return self.__name

    #: The name of the node.
    #: @type: string
    name = property(get_name, set_name)

    def add_successor(self, succ):
        """
        Adds a reference to a successor node.
        
        @param succ: A reference to a successor node.
        @type succ: L{GraphNode}
        """
        self.__successors.append(succ)

    def get_successors(self):
        """
        Returns all successor nodes.

        @return: All successor nodes.
        @rtype: list<L{GraphNode}>
        """
        return self.__successors

    #: All successor nodes.
    #: @type: list<L{GraphNode}>
    successors = property(get_successors)

    def add_predecessor(self, pre):
        """
        Adds a reference to a predecessor node.

        @param pre: A reference to a predecessor node.
        @type pre: L{GraphNode}
        """
        self.__predecessors.append(pre)

    def get_predecessors(self):
        """
        Returns all predecessor nodes.

        @return: All predecessor nodes.
        @rtype: list<L{GraphNode}>
        """
        return self.__predecessors

    #: All predecessor nodes.
    #: @type: list<L{GraphNode}>
    redecessors = property(get_predecessors)

    def set_changes_of_jx(self, changes):
        """
        Set the maximal number of changes of jx in the sequel of the play.

        @param changes: The maximal number of changes of jx in the sequel of
               the play.
        @type changes: int
        """
        self.__jx_changes = changes

    def get_changes_of_jx(self):
        """
        Returns the maximal number of changes of jx in the sequel of the play.

        @return: The maximal number of changes of jx in the sequel of the play.
        @rtype: int
        """
        return self.__jx_changes

    #: The maximal number of changes of jx in the sequel of the play.
    #: @type: int
    changes_of_jx = property(get_changes_of_jx, set_changes_of_jx)

    def add_next_input_to_print(self, var_name, var_val):
        """
        Adds a next inputs that should be printed in the node.

        This method adds the name and the next value of an input variable
        which should be printed in the node.

        @param var_name: The name of the input variable.
        @type var_name: string
        @param var_val: The value of the input variable.
        @type var_val: int
        """
        self.__next_inputs_to_print[var_name] = var_val
        

    def print_node_dot(self, include_inputs):
        """
        Returns the DOT-representation of the node.

        The string looks like:

        S0[label = "S0 | {2,3,4 | 2} | {1,4,6 | 4} | 2 |sig0=1\\n sig1=0\\n "];

        where: 
         - S0 = name of the state
         - 2,3,4 = indices of environment fairness conditions fulfilled in
           this state
         - 2 = the index ix of the fairness condition of the environment we
           want to reach next
         - 1,4,6 = indices of system fairness conditions fulfilled in this
           state
         - 4 = the index jx of the fairness condition of the system we want to
           evade
         - 2 = jx might change 2 times from now
         - sig0=1... = changing next inputs and their values

        @param include_inputs: True if inputs should be included and False
               otherwise.
        @type include_inputs: bool
        @return: A string representing the node in DOT-format.
        @rtype: string
        """
        ix = "?"
        if self.__ix_val != None:
            ix = str(self.__ix_val)
        jx = "?"
        if self.__jx_val != None:
            jx = str(self.__jx_val)

        res = "  " + self.__name
        res += "[label = \"" + self.__name + " | "
        res += "{" + self.__env_fulfilled + " | "
        res += ix
        res += "} | {" + self.__sys_fulfilled + " | "
        res += jx
        res += "}"
        res += " | " + str(self.__jx_changes)

        if include_inputs:
            res += " | "
            for var_name in self.__next_inputs_to_print.keys():
                res += var_name + "="
                res += str(self.__next_inputs_to_print[var_name]) + "\\n "
            
        
        res += "\"];\n"
        return res
        


    def print_node_info(self):
        """
        Returns an entry for the .info file.

        This method returns a string that contains an entry for the node in
        the .info file. The entry contains all values of all input and output
        variables as well as the indices of the environment and system
        fairness conditions fulfilled in this state. It further contains
        information about which fairness condition the environment wants to
        reach next (ix value) and which fairness condition of the system it
        wants to evade (jx value).

        @return: A string that contains an entry for the node in the .info
                 file.
        @rtype: string
        """

        res = "--------  " + self.__name + ":  ----------\n"

        all_vars = []
        all_vars.extend(self.__utils.input_vars)
        all_vars.extend(self.__utils.relevant_out_vars)

        # printing all values of all variables in this state:
        for var in all_vars:
            symb = self.__utils.get_val_as_string(self.__bdd, var, False)
            res += "current " + var.name + " is: " + symb + "\n"

        # printing the indices of the fairness conditions fulfilled in this
        # state:
        res += "indices of environment fairness conditions fulfilled: "
        res += self.__env_fulfilled + "\n"
        res += "indices of system fairness conditions fulfilled: "
        res += self.__sys_fulfilled + "\n"

        # printing the index of the fairness condition of the environment
        # which we try to fulfill next (ix value) as well as the index of the
        # fairness condition of the system we try to evade (jx value):
        if self.__ix_val != None:
            res += "The environment tries to fulfill fairness condition nr "
            res += str(self.__ix_val) + " next\n"
        else:
            res += "The environment has not decided yet which fairness "
            res += "condition it will try to reach next\n"
        
        if self.__jx_val != None:
            res += "I try to keep the system from fulfilling fairness "
            res += "condition nr: " + str(self.__jx_val) +"\n"
        else:
            res += "I have not decided yet which fairness condition of the "
            res += "system I will try to evade\n"
        
        return res
        

    def print_edges_to_succ_dot(self, include_outputs):
        """
        Returns DOT-edges to all successor nodes.
        
        This method prints an edge to each successor of the node into a
        string in DOT-format and returns this string.

         - For include_outputs=0, the string looks like:\n
           'S0 -> S1;'

         - For include_outputs=1, the string looks like:\n
           'S0 -> S1[label="sig1=0\\n sig2=1\\n];'

        @param include_outputs: True if relevant outputs should be included and
               False otherwise.
        @type include_outputs: bool
        @return: A string representing all edges to successors in DOT-format.
        @rtype: string
        """
        if include_outputs:
            return self._print_labeled_edges_to_succ_dot()
        
        return self._print_unlabeled_edges_to_succ_dot()
        

    def _print_unlabeled_edges_to_succ_dot(self):
        """
        Returns unlabeled DOT-edges to all successor nodes.

        This method prints an edge to each successor of the node into a
        string in DOT-format and returns this string. Relevant next output
        values are not included.

         - The string looks like:\n
           'S0 -> S1;'

        @return: A string representing all edges to successors
                 in DOT-format.
        @rtype: string
        """
        res = ""
        for succ in self.__successors:
            res += "  " + self.__name + " -> " + succ.name + ";\n"
        
        return res

    def _print_labeled_edges_to_succ_dot(self):
        """
        Returns labeled DOT-edges to all successor nodes.

        This method prints an edge to each successor of the node into a
        string in DOT-format and returns this string. Relevant next output
        values are included. An output is relevant (and thus printed) if
        it is different for the different successors.

         - The string looks like:\n
           'S0 -> S1[label="sig1=0\\n sig2=1\\n];'

        @return: A string representing all edges to successors in DOT-format.
                 Relevant outputs are included.
        @rtype: string
        """

        res = ""

        # First, we compute a bdd which is the union of all successor bdds:
        all_successors_bdd = BDD.ZERO(self.__utils.dd_mgr)
        for succ in self.__successors:
            all_successors_bdd += succ.bdd
        

        # Second, we figure out which output variables are different for the
        # different successors:
        different_out_vars = []
        for out_var in self.__utils.relevant_out_vars:
            (can_be_1, can_be_0) =  \
                      self.__utils.get_val(all_successors_bdd, out_var, False)
            # If the value of the output is equal for all successors,
            # only one concrete value for the output is allowed. If both
            # values are allowed, the values must have been different in
            # some successors:
            if can_be_1 and can_be_0:
                different_out_vars.append(out_var)
            
        

        # Finally we print the edges to all successors, where we also print
        # the values of all variables which are different for some
        # successors:
        for succ in self.__successors:
            res += "  " + self.__name + " -> " + succ.name
            res += "[label=\""
            for out_var in different_out_vars:
                symb = self.__utils.get_val_as_string(succ.bdd, out_var, False)
                res += out_var.name + "=" + symb + "\\n"
            res += "\"];\n"
        
        return res
        
        

    def unlink(self):
        """
        Removes all circular references.

        This method should be called on every graph node if the graph is not
        needed any more. This is necessary as the garbage collector of Python
        cannot destroy nodes when they have circular references.
        """

        self.__successors = []
        self.__predecessors = []
        
