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


class Specification(object):
    """
    This class is responsible for parsing the input and turning it into usable formats (among others: BDDs).
    """
    
    def __init__(self, marduk):
        self.__marduk = marduk
        self.__init1 = None
        self.__init2 = None
        self.__init12 = None
        self.__trans1 = None
        self.__trans2 = None
        self.__trans12 = None
        self.__assumptions = []
        self.__guarantees = []

    def clear(self):
        self.__init1 = None
        self.__init2 = None
        self.__init12 = None
        self.__trans1 = None
        self.__trans2 = None
        self.__trans12 = None
        self.__assumptions = []
        self.__guarantees = []

    def create_variable_list(self):
        """
        Creates the list of variables (containing variable names, pointer to present state BDD, and next state BDD.
        This list contains only input and output variabels, no state variables (jx).
        Thus this function should only be called ONCE by the Marduk main class. From that point on, the main class
        stores the list internally, including any state variables which might have been added later on.

        ATTENTION: This function may only be called AFTER the specification has been read and compiled via
        readSpecification!!
        """
        from nusmv import utils as nusmv_utils
        from nusmv import compile
        from nusmv.compile import symb_table
        from nusmv import enc
        from nusmv.enc import bdd
        from nusmv.enc import bbool
        from nusmv import node
        from nusmv import dd
        import marduk_utils
        from bddwrap import BDD

        list = []

        nusmv_mgr = BDD.dd_mgr
        marduk_mgr = self.__marduk.dd_mgr
        
        st = compile.get_global_symb_table()
        bdd_enc = enc.Enc_get_bdd_encoding()
        bool_enc = enc.Enc_get_bool_encoding()
        vars_node_list_ptr = symb_table.SymbTable_get_vars(st)

        iter = nusmv_utils.NodeList_get_first_iter(vars_node_list_ptr)
        
        while not nusmv_utils.ListIter_is_end(iter):
            var_node = nusmv_utils.NodeList_get_elem_at(vars_node_list_ptr, iter)
            iter = nusmv_utils.ListIter_get_next(iter)

            var_name = node.sprint_node(var_node)
            
            layer = symb_table.SymbTable_variable_get_layer(st, var_node)
            layer_name = symb_table.SymbLayer_get_name(layer)

            if layer_name == "layer_of_PLAYER_1":
                var_type = marduk_utils.VariableType.INPUT
                if self.__marduk.verbose > 0:
                    print "Detected input variable:", var_name
            elif layer_name == "layer_of_PLAYER_2":
                var_type = marduk_utils.VariableType.OUTPUT
                if self.__marduk.verbose > 0:
                    print "Detected output variable:", var_name
            else:
                var_type = marduk_utils.VariableType.UNKNOWN
                print "WARNING! Detected unknown variable type of variable:", var_name

            symbol_type = symb_table.SymbTable_get_var_type(st, var_node)

            if not symb_table.SymbType_is_boolean_enum(symbol_type):

                encoding = bbool.BoolEnc_get_var_encoding(bool_enc, var_node)
                encoding_add = bdd.expr_to_add(bdd_enc, encoding, node.Nil)

                import sys
                import os

                # Redirecting stdout to tmpfile.
                stdout = sys.stdout
                tmpfile = os.tmpfile() 
                sys.stdout = tmpfile
                dd.dd_setStdout(nusmv_mgr, tmpfile)

                print "\n=================================================="
                print "Encountered non-Boolean variable '%s'." % var_name
                print "Encoding it with the following Boolean variables:"
                print "(BDD minterms correspond to present state part of variable)\n"
                
                bits_node_list_ptr = bbool.BoolEnc_get_var_bits(bool_enc, var_node)
                bit_iter = nusmv_utils.NodeList_get_first_iter(bits_node_list_ptr)
                count = 0
                while not nusmv_utils.ListIter_is_end(iter):
                    bit_node = nusmv_utils.NodeList_get_elem_at(bits_node_list_ptr, iter)

                    bit_name = node.sprint_node(bit_node)
                    import re
                    bit_name = re.sub(r'\.','_', bit_name)
                    ps_bdd_ptr = bdd.expr_to_bdd(bdd_enc, bit_node, node.Nil)
                    ns_bdd_ptr = bdd.state_var_to_next_state_var(bdd_enc, ps_bdd_ptr)
                    ps_bdd = BDD(ps_bdd_ptr, nusmv_mgr, bit_name + "_ps", dest_mgr=marduk_mgr)
                    ns_bdd = BDD(ns_bdd_ptr, nusmv_mgr, bit_name + "_ns", dest_mgr=marduk_mgr)
                    var = marduk_utils.Variable(bit_name, var_type, ps_bdd, ns_bdd)
                    list.append(var)
                    dd.bdd_free(BDD.dd_mgr, ps_bdd_ptr)
                    dd.bdd_free(BDD.dd_mgr, ns_bdd_ptr)                
                    
                    
                    iter = nusmv_utils.ListIter_get_next(iter)
                    count += 1
                    
                    print "Bit %s: '%s'" %(str(count), var.name)
                    var.ps.print_minterm()
                    print ""

                print "ADD corresponding to the encoding:"
                dd.add_printminterm(nusmv_mgr, encoding_add)
                dd.add_free(nusmv_mgr, encoding_add)
                print "\n+++  +++   End of encoding information for variable '%s'   +++ +++\n" % var_name
                
                # Resetting stdout
                sys.stdout = stdout
                dd.dd_setStdout(nusmv_mgr, stdout)

                # Adding information about encoding to output
                tmpfile.seek(0)
                lines = tmpfile.readlines()
                tmpfile.close()
                for line in lines:
                    line = re.sub(r'\n', '', line)
                    self.__marduk.println(line)
                    
            else:
                ps_bdd_ptr = bdd.expr_to_bdd(bdd_enc, var_node, node.Nil)
                ns_bdd_ptr = bdd.state_var_to_next_state_var(bdd_enc, ps_bdd_ptr)
                ps_bdd = BDD(ps_bdd_ptr, nusmv_mgr, var_name + "_ps", dest_mgr=marduk_mgr)
                ns_bdd = BDD(ns_bdd_ptr, nusmv_mgr, var_name + "_ns", dest_mgr=marduk_mgr)
                var = marduk_utils.Variable(var_name, var_type, ps_bdd, ns_bdd)

                dd.bdd_free(nusmv_mgr, ps_bdd_ptr)
                dd.bdd_free(nusmv_mgr, ns_bdd_ptr)                
                
                list.append(var)
                if self.__marduk.verbose > 1:
                    print var.name
                    var.ps.print_minterm()
                    var.ns.print_minterm()
                    print "#####################"
        return list
                

    def readSpecification(self, filename = None):
        from nusmv import utils
        from nusmv import game
        from nusmv import compile
        from nusmv import cmd
        from nusmv.compile import symb_table
        from nusmv import prop
        from nusmv import opt
        import sys
        from marduk_utils import MardukException


        if not filename:
            filename = self.__marduk.input_file

        #cmd.Cmd_CommandExecute("read_model -i %s" %filename)
        #game_ok = 0
        game_ok = game.RatFileToGameWrap(filename)

        #print "hallo"
        #cmd.Cmd_CommandExecute("read_rat_file %s" % filename)
        if self.__marduk.verbose > 1: 
            print "\nGame OK?", game_ok
            
        if game_ok != 0:
            raise MardukException(("Error: could not parse the input file '%s'." % filename))

        if self.__marduk.partition == "Threshold":
            opt.set_conj_partitioning(opt.OptsHandler_get_instance())
        elif self.__marduk.partition == "Monolithic":
            opt.set_monolithic(opt.OptsHandler_get_instance())
        elif self.__marduk.partition == "Iwls95CP":
            opt.set_iwls95cp_partitioning(opt.OptsHandler_get_instance())

        # Command 'go' comprises the following commands :
        # 1) read_model
        # 2) flatten_hierarchy
        # 3) encode_variables
        # 4) build_flat_model
        # 5) build_model
        #print "before go"
        cmd.Cmd_CommandExecute("go")

        if self.__marduk.verbose > 1:
            print "Flattening OK? ", compile.check_if_flattening_was_built(sys.stdout)
            print "Encoding OK?", compile.check_if_encoding_was_built(sys.stdout)

            st = compile.get_global_symb_table()
            vars_num = symb_table.SymbTable_get_vars_num(st)

            vars_node_list_ptr = symb_table.SymbTable_get_vars(st)
            print "variables in symbol table: ", utils.NodeList_print_nodes(vars_node_list_ptr, sys.stdout)
            print "\n"

            print "Property: ", prop.PropDb_print_all(prop.PropPkg_get_prop_database(), sys.stdout)
        self._set_up_bdds()
        


    def _set_up_bdds(self):

        from nusmv import game
        from nusmv import prop
        from nusmv import node
        from nusmv import dd
        from marduk_utils import MardukException
        from bddwrap import BDD
        from nusmv.game import bddfsm
        from nusmv import enc
        from nusmv.enc import bdd

        prop_database = prop.PropPkg_get_prop_database()

        num_of_prop =  prop.PropDb_get_size(prop_database)

        #What do we do if there are more properties?
        if num_of_prop != 1:
             raise MardukException(("Error: the number of properties is '%s'. Expected exactly one property!\nProbably the specification is not in GR(1) format!" % num_of_prop))

        property = prop.PropDb_get_prop_at_index(prop_database, num_of_prop - 1);
        prop_type_str = prop.Prop_get_type_as_string(property)

        if prop_type_str != "GenReactivity":
            raise MardukException("""Error: The given specification is not a 'GenReactivity' specification.
        The game type is '%s'.""" % prop_type_str)

        spec_exp = prop.Prop_get_expr_core(property)

        game_property = game.castPropToGameProp(property)
        fsm = game.PropGame_get_game_bdd_fsm(game_property);
        if fsm == None:
            prop.PropDb_set_fsm_to_master(prop_database, property);
            game_property = game.castPropToGameProp(property)
            fsm = game.PropGame_get_game_bdd_fsm(game_property);

        nusmv_mgr = BDD.dd_mgr

        invars_1_ptr = bddfsm.get_invars_1(fsm)
        invars_2_ptr = bddfsm.get_invars_2(fsm)
        init_1_ptr = bddfsm.get_init_1(fsm)
        init_2_ptr =  bddfsm.get_init_2(fsm)
        trans_1_ptr = bddfsm.get_monolitic_trans_1(fsm)
        trans_2_ptr = bddfsm.get_monolitic_trans_2(fsm)

        invars_1 = BDD(invars_1_ptr, nusmv_mgr, "invars_1")
        invars_2 = BDD(invars_2_ptr, nusmv_mgr, "invars_2")
        init_1 = BDD(init_1_ptr, nusmv_mgr, "init_1")
        init_2 = BDD(init_2_ptr, nusmv_mgr, "init_2")
        trans_1 = BDD(trans_1_ptr, nusmv_mgr, "trans_1")
        trans_2 = BDD(trans_2_ptr, nusmv_mgr, "trans_2")

        dd.bdd_free(nusmv_mgr, invars_1_ptr)
        dd.bdd_free(nusmv_mgr, invars_2_ptr)
        dd.bdd_free(nusmv_mgr, init_1_ptr)
        dd.bdd_free(nusmv_mgr, init_2_ptr)
        dd.bdd_free(nusmv_mgr, trans_1_ptr)
        dd.bdd_free(nusmv_mgr, trans_2_ptr)

        self.__init1 = (init_1 * invars_1)
        self.__init1.name = "init1"
        self.__init2 = (init_2 * invars_2)
        self.__init2.name = "init2"
        self.__init12 = self.__init1 * self.__init2
        self.__init12.name = "init12"

        self.__trans1 = (trans_1 * invars_1)
        self.__trans1.name = "trans1"
        self.__trans2 = (trans_2 * invars_2)
        self.__trans2.name = "trans2"
        self.__trans12 = self.__trans1 * self.__trans2
        self.__trans12.name = "trans12"

        invars = (invars_1 * invars_2)
        invars_1 = None
        invars_2 = None
        init_1 = None
        init_2 = None
        trans_1 = None
        trans_2 = None

        assume_exp = node.car(spec_exp)
        guaran_exp = node.cdr(spec_exp)
        bdd_enc = enc.Enc_get_bdd_encoding()

        while assume_exp:
            assume_ptr = bdd.expr_to_bdd(bdd_enc, node.car(assume_exp), node.Nil)
            self.__assumptions.append(BDD(assume_ptr, nusmv_mgr, "assumption"))
            dd.bdd_free(nusmv_mgr, assume_ptr)
            self.__assumptions[-1] *= invars
            assume_exp = node.cdr(assume_exp)

        while guaran_exp:
            guaran_ptr = bdd.expr_to_bdd(bdd_enc, node.car(guaran_exp), node.Nil)
            self.__guarantees.append(BDD(guaran_ptr, nusmv_mgr, "guarantee"))
            dd.bdd_free(nusmv_mgr, guaran_ptr)
            self.__guarantees[-1] *= invars
            guaran_exp = node.cdr(guaran_exp)


    def get_init1(self, dest_mgr = None):
        if dest_mgr:
            return self.__init1.transfer(dest_mgr)
        return self.__init1.copy()

    def get_init2(self, dest_mgr = None):
        if dest_mgr:
            return self.__init2.transfer(dest_mgr)
        return self.__init2.copy()

    def get_init12(self, dest_mgr = None):
        if dest_mgr:
            return self.__init12.transfer(dest_mgr)
        return self.__init12.copy()

    def get_trans1(self, dest_mgr = None):
        if dest_mgr:
            return self.__trans1.transfer(dest_mgr)
        return self.__trans1.copy()

    def get_trans2(self, dest_mgr = None):
        if dest_mgr:
            return self.__trans2.transfer(dest_mgr)
        return self.__trans2.copy()

    def get_trans12(self, dest_mgr = None):
        if dest_mgr:
            return self.__trans12.transfer(dest_mgr)
        return self.__trans12.copy()

    def get_assumptions(self, dest_mgr = None):
        if dest_mgr:
            return [assumption.transfer(dest_mgr) for assumption in self.__assumptions]
        else:
            return [assumption.copy() for assumption in self.__assumptions]
      
    def get_guarantees(self, dest_mgr = None):
        if dest_mgr:
            return [guarantee.transfer(dest_mgr) for guarantee in self.__guarantees]
        else:
            return [guarantee.copy() for guarantee in self.__guarantees]
