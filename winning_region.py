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

from marduk_utils import MardukException

class WinningRegion(object):
    """
    This class computes (and stores) the winning region.
    """
    
    def __init__(self, marduk, specification):
        self.__marduk = marduk
        self.__specification = specification
        self.__winningRegion = None
        self.__xArray = {} 
        self.__yArray = {}
        self.__numOfGuarantees = 0
        self.__numOfAssumptions = 0
        self.__guarantees = []
        self.__assumptions = []
        self.__transition1 = None
        self.__transition2 = None
        self.__transition12 = None
        self.__transitionjx = None
        self.__init1 = None
        self.__init2 = None
        self.__init12 = None
        self.__init = None
        self.__initjx = None
        self.__jx_ps_vars = None
        self.__jx_ns_vars = None

    def __del__(self):
        self.killArrays()
        self.killWinReg()
        
    def calcWinningRegion(self):
        """
        calls the ComputeGenReactivityWrap function from NuSMV to calculate
        the winning region. Also the xArray and yArray are calculated and
        converted to python arrays. The numOfAssumptions and numOfGuarantees
        are already integer (here the conversion happens in the wrapper, 
        by the typemap). All the properties of the WinningRegion class
        (guarantees, assumptions, transition1 ...) are set to the right 
        values by this function
        """
        
        from marduk_utils import MardukException
        from bddwrap import BDD
        from nusmv import dd

        marduk_mgr = self.__marduk.dd_mgr
        nusmv_mgr = BDD.dd_mgr
        spec = self.__marduk.specification
        

        self.__init1 = spec.get_init1(marduk_mgr)
        self.__init2 = spec.get_init2(marduk_mgr)
        self.__init12 = spec.get_init12(marduk_mgr)
        
        self.__transition1 = spec.get_trans1(marduk_mgr)
        self.__transition2 = spec.get_trans2(marduk_mgr)
        self.__transition12 = spec.get_trans12(marduk_mgr)
                
        self.__assumptions = spec.get_assumptions(marduk_mgr)
        self.__guarantees = spec.get_guarantees(marduk_mgr)
        
        self._moduloInc(len(self.__guarantees))

        # Built all BDDs from specification. Now perform first reordering, if requested.
        import resource
        before_reorder1_time = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        if self.__marduk.reorder1:
            result = dd.dd_reorder(marduk_mgr, self.__marduk.dyn_reorder_method,0)
        self.__marduk._reorder1time = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime 
        self.__marduk.println("   First reordering of bdd takes \t\t %7.2f seconds" %(self.__marduk._reorder1time - before_reorder1_time))
        
        
        n = len(self.__guarantees)
        m = len(self.__assumptions)
        old_z = BDD.ZERO(marduk_mgr)
        z = BDD.ONE(marduk_mgr)
        while(z != old_z): # GreatestFixpoint(z)
            old_z = z
    
            for j in range(0,n):            
                r = 0
                old_y = BDD.ONE(marduk_mgr)
                y = BDD.ZERO(marduk_mgr)

                # Free previously remembered results:
                self.__yArray[j] = {}
                self.__xArray[j] = {}
                
                while(y != old_y): # LeastFixpoint(y)
                    self.__xArray[j][r] = {}                   
                    old_y = y
                    start = (self.__guarantees[j] * self.coax(z)) + self.coax(y)
                    y = BDD.ZERO(marduk_mgr)
                    for i in range(0,m):
                        # RB: it would seem to me that we can add x[j][r][i-1] to start here,
                        # which would make the fixpoint larger.
                        old_x = BDD.ZERO(marduk_mgr)
                        x = z
                        while (x != old_x): # GreatestFixpoint(x)
                            old_x = x
                            x = start + ((~(self.__assumptions[i])) * self.coax(x))
                            x.name = "x_elem"
                        # End -- GreatestFixpoint(x)
                        self.__xArray[j][r][i] = x
                        y = y + x
                        y.name = "y_elem"
                    # End - For (i in 1...m)
                    self.__yArray[j][r] = y
                    r += 1
                # End -- LeastFixpoint(y)
                self.__yArray[j].pop(r-1)
                self.__xArray[j].pop(r-1)
                z = y
            # End -- For (j in 1...n)
        # End -- GreatestFixpoint(z)

        z.name = "WinReg"
        self.__winningRegion = z
        return
       

        
    def coax(self, states):
        from bddwrap import BDD
        import marduk_utils
        marduk_mgr = self.__marduk.dd_mgr
        input_product = BDD.ONE(marduk_mgr)
        output_product = BDD.ONE(marduk_mgr)
        present = []
        next = []
        for var in self.__marduk.vars:
            if var.type == marduk_utils.VariableType.INPUT:
                input_product *=  var.ns
            elif var.type == marduk_utils.VariableType.OUTPUT:
                output_product *= var.ns
            present.append(var.ps)
            next.append(var.ns)
        
        swapped_states = states.swapVariables(present, next)

        result = self.__transition2.andExists(swapped_states, output_product)
        result += (~ self.__transition1)
 
        result = result.forall(input_product)
 
#        result = Forall $input_product ((!@$env_transitions[0]) + 
#                                      Cudd::BDD::AndExists($output_product, @$sys_transitions[0], $swapped_states));     
        return result


        

    def _convert_y_array(self,CyArray):
        """
        converts the yArray from NuSMV into a python array and writes it to
        self.__yArray. Also duplicates the bdds in the array, so they do
        not get lost when the NuSMV array is freed
    
        CyArray is an array of lists of BDDs of Y
        """

        from nusmv import game
        from nusmv import utils
        from bddwrap import BDD

        for j in range(0,self.__numOfGuarantees):
            tmp_node = game.ReactivityArrayGet(CyArray,j)        
            tmp_list = utils.NodeList_create_from_list(tmp_node)
            iter = utils.NodeList_get_first_iter(tmp_list)

            bdd_list = []
            while not utils.ListIter_is_end(iter):
                tmp_bdd_node = utils.NodeList_get_elem_at(tmp_list, iter)
                bdd_node = game.CastNodePtrToBddPtr(tmp_bdd_node)
                bdd_list.append(BDD(bdd_node, BDD.dd_mgr, "yArrayElem", dest_mgr=self.__marduk.dd_mgr))                
                iter = utils.ListIter_get_next(iter)

            self.__yArray.append(bdd_list)


    def _convert_x_array(self,CxArray):
        """
        converts the xArray from NuSMV into a python array and writes it to
        self.__xArray. Also duplicates the bdds in the array, so they do
        not get lost when the NuSMV array is freed
    
        CxArray is an array of lists of arrays of BDDs of X
        """
        from nusmv import game
        from nusmv import utils
        from bddwrap import BDD

        for j in range(0,self.__numOfGuarantees):
            tmp_node = game.ReactivityArrayGet(CxArray,j)        
            tmp_list = utils.NodeList_create_from_list(tmp_node)
            iter = utils.NodeList_get_first_iter(tmp_list)

            bdd_list_list = []
            while not utils.ListIter_is_end(iter):
                tmp_node_list = utils.NodeList_get_elem_at(tmp_list, iter)
                tmp = game.CastNodePtrToNodePtrPtr(tmp_node_list)

                tmp_bdd_list = []

                for i in range(0,self.__numOfAssumptions):             
                    tmp_bdd = game.CastNodePtrToBddPtr(game.ReactivityArrayGet(tmp,i))
                    tmp_bdd_list.append(BDD(tmp_bdd, BDD.dd_mgr, "xArrayElem", dest_mgr=self.__marduk.dd_mgr))
                bdd_list_list.append(tmp_bdd_list)                
                iter = utils.ListIter_get_next(iter)
            self.__xArray.append(bdd_list_list)


    def _convert_guarantee_bdds(self,Cguarantee_bdds):
        """
        Converts the guarantee_bdds from NuSMV into a python array and writes it to
        self.__guarantees. Also duplicates the bdds in the array, so they do
        not get lost when the NuSMV array is freed
    
        Cguarantee_bdds is an array of bdd_ptr representing the guarantees
        """
        from nusmv import game
        from bddwrap import BDD

        for i in range(0,self.__numOfGuarantees):
            bdd = game.BddArrayGet(Cguarantee_bdds,i)        
            #self.__guarantees.append(BDD(bdd, BDD.dd_mgr, "guarantee_" + str(i), dest_mgr=self.__marduk.dd_mgr))
            print "guarantee[%d]:" % i, self.__guarantees[i] == (BDD(bdd, BDD.dd_mgr, "guarantee_" + str(i), dest_mgr=self.__marduk.dd_mgr))
#             print "Guarantee %d" % i
#             self.__guarantees[i].print_minterm()
#             print "###############################################"
 

    def _convert_assumption_bdds(self,Cassumption_bdds):
        """
        Converts the assumption_bdds from NuSMV into a python array and writes it to
        self.__assumptions. Also duplicates the bdds in the array, so they do
        not get lost when the NuSMV array is freed
        
        Cassumption_bdds is an array of bdd_ptr representing the assumptions
        """
        from nusmv import game
        from bddwrap import BDD

        for i in range(0,self.__numOfAssumptions):
            bdd = game.BddArrayGet(Cassumption_bdds,i)        
            print "assumption[%d]" %i, self.__assumptions[i] == (BDD(bdd, BDD.dd_mgr, "assumption_" + str(i), dest_mgr=self.__marduk.dd_mgr))


    def _calc_trans_and_initial_bdds(self):
        """
        Gets the transitions and initial states from NuSMV and writes it into
        the corresponding winning_region properties
        """
        from nusmv import prop
        from nusmv.game import bddfsm
        from nusmv import dd
        from bddwrap import BDD

        dd_manager = dd.cvar.dd_manager
        prop_master = prop.Prop_master_get_game_bdd_fsm()

        trans = bddfsm.get_monolitic_trans_1(prop_master)
        init = bddfsm.get_init_1(prop_master)
        invar = bddfsm.get_invars_1(prop_master)
        tmp = dd.bdd_and(dd_manager,trans,invar)
        self.__transition1 = BDD(tmp, dd_manager, "trans_1")
        dd.bdd_free(dd_manager, tmp)
        tmp = dd.bdd_and(dd_manager,init,invar)
        self.__init1 = BDD(tmp, dd_manager, "init_1")
        dd.bdd_free(dd_manager, tmp)
        dd.bdd_free(dd_manager,trans)
        dd.bdd_free(dd_manager,init)
        dd.bdd_free(dd_manager,invar)
        trans = bddfsm.get_monolitic_trans_2(prop_master)
        init = bddfsm.get_init_2(prop_master)
        invar = bddfsm.get_invars_2(prop_master)
        tmp = dd.bdd_and(dd_manager,trans,invar) 
        self.__transition2 = BDD(tmp, dd_manager, "trans_2")
        dd.bdd_free(dd_manager, tmp)
        tmp = dd.bdd_and(dd_manager,init,invar)
        self.__init2 == BDD(tmp, dd_manager, "init_2")
        dd.bdd_free(dd_manager, tmp)
        dd.bdd_free(dd_manager,trans)
        dd.bdd_free(dd_manager,init)
        dd.bdd_free(dd_manager,invar)
        self.__transition12 = self.__transition1 * self.__transition2
        self.__transition12.name = "trans_12"
        self.__init12 = self.__init1 * self.__init2
        self.__init12.name = "init_12"

        self._moduloInc(self.__numOfGuarantees)
        self.__init = self.__init12 * self.__initjx
        self.__init.name = "init"
        # KG: I think we do not want to change jx every time we take a transition, consequently we do not want to have trans12 and transjx at the same time
        #self.__transition = self.__transition12 * self.__transitionjx
        
  
    def isRealizable(self):
        """
        returns True if for all initial configurations or the inputs there
        exists an initial configuration of the outputs such that the
        thereby formed initial state is contained in the winning region.
        """

        from bddwrap import BDD
        import marduk_utils
        in_product = BDD.ONE(self.__marduk.dd_mgr)
        out_product = BDD.ONE(self.__marduk.dd_mgr)
        for var in self.__marduk.vars:
            if var.type == marduk_utils.VariableType.INPUT:
                in_product *=  var.ps
            elif var.type == marduk_utils.VariableType.OUTPUT:
                out_product *= var.ps

        win_and_sys_initial = self.__winningRegion * self.__init2
        can_find_initial_output = win_and_sys_initial.exists(out_product)
        realizable = ((~self.__init1) + can_find_initial_output).isOne()

        if realizable and not self.__init12 <= self.__winningRegion:
        # if some but not all initial states are contained in the winning 
        # region, we have to make sure that we start from a winning state
        # when synthesizing a circuit:
            print "Warning: Not all initial states are winning."
            self.__init1 *= self.__winningRegion
            self.__init2 *= self.__winningRegion
            self.__init12 *= self.__winningRegion
            self.__init = self.__init12 * self.__initjx

        return realizable

    def reachableStates(self,init,trans,invar):
        """
        returns the set of states which are reachable from init via trans
        never leaving invar

        Notice that NuSMV sets the next states for system transitions 
        of the form G(pure_propositional) whereas Anzu sets the present 
        states. This leads to different sets of reachable states 
        Consider the following example:
        (xyy')*x=xyy'
        (xyy')*x'=xyx'y'
        """

        from bddwrap import BDD

        present_vars = [var.ps for var in self.__marduk.vars]
        
        present_vars_cube  = BDD.ONE(self.__marduk.dd_mgr)
        for var in present_vars:
            present_vars_cube *= var

        next_vars = [var.ns for var in self.__marduk.vars]
        reach = init * invar
        old_reach = BDD.ZERO(self.__marduk.dd_mgr)
        while not(old_reach == reach):
            old_reach = reach.copy()
            reach *= invar
            tmp = reach.andExists(trans, present_vars_cube)
            reach += tmp.swapVariables(present_vars,next_vars)

        return reach


    def _moduloInc(self,n):
        """
        Creates a bdd which does 'j = (j+1) mod n': 0,1,2,...n-1,0,1,.
        """
        
        import math
        from bddwrap import BDD

        marduk_mgr = self.__marduk.dd_mgr
        
        if n == 0 :
            print "modulo_inc for 0 does not make sense!"
            return (BDD.ZERO(marduk_mgr), BDD.ZERO(marduk_mgr), BDD.ZERO(marduk_mgr), BDD.ZERO(marduk_mgr))
        
        
        ########################################################
        # one hot encoding
        ########################################################             
        if self.__marduk.one_hot:
            (present_vars, next_vars) = self.generate_JX_vars(n)
            trans_relation = BDD.ZERO(marduk_mgr)
            present_states = []
            next_states = []
            
            for i in range(0,n):
                present_state = BDD.ONE(marduk_mgr)
                next_state = BDD.ONE(marduk_mgr)
                for j in range(0,n):
                    if (i == j):
                        present_state *= present_vars[j]
                        next_state *= next_vars[j]
                    else:
                        present_state *= ~present_vars[j]
                        next_state *= ~next_vars[j]
                present_states.append(present_state)
                next_states.append(next_state)

            for i in range(0,n-1):
                trans_relation += present_states[i] * next_states[i+1]
                
            trans_relation += present_states[n-1] * next_states[0]
            trans_relation.name = "trans_jx"
            start_state = present_states[0]
            start_state.name = "init_jx"

            
            
            self.__transitionjx = trans_relation
            self.__initjx = start_state
            self.__jx_ps_vars = present_vars
            self.__jx_ns_vars = next_vars
            return


        ########################################################
        # binary encoding
        ########################################################            
        else:
            num_of_bits = int(math.ceil(math.log(n,2)))
            if num_of_bits == 0: #n = 1
                num_of_bits = 1

            (present_vars, next_vars) = self.generate_JX_vars(num_of_bits)
            trans_relation = BDD.ONE(marduk_mgr)
            carry = BDD.ONE(marduk_mgr)

            for i in range(0,num_of_bits):
                trans_relation *= (~next_vars[i] + (carry ^ present_vars[i])) * (~(carry ^ present_vars[i]) + next_vars[i]);
                
                carry *= present_vars[i]
            
            reset_condition = BDD.ONE(marduk_mgr)
            reset_state = BDD.ONE(marduk_mgr)
            start_state = BDD.ONE(marduk_mgr)
            bit_selector = n-1
            for i in range(0,num_of_bits):
                if ((bit_selector & 0x1) == 1):
                    reset_condition *= present_vars[i]
                else:
                    reset_condition *= ~present_vars[i]

                bit_selector = bit_selector >> 1
                reset_state *= ~next_vars[i]
                start_state *= ~present_vars[i]

            case_increase = reset_condition + trans_relation
            case_reset = ~reset_condition + reset_state

            trans_relation = case_increase * case_reset
                        
            self.__transitionjx = trans_relation
            self.__transitionjx.name = "trans_jx"
            self.__initjx = start_state
            self.__initjx.name = "init_jx"
            self.__jx_ps_vars = present_vars
            self.__jx_ns_vars = next_vars
            return
     
    
    def generate_JX_vars(self,n):
        """
        gernerates n jx vars
        returns a list of present states and a list of next states
        """

        from nusmv import dd
        import marduk_utils
        from bddwrap import BDD

        present_vars = []
        next_vars = []
        dd_manager = self.__marduk.dd_mgr
        
        for i in range(0,n):
            tmp = dd.bdd_new_var(dd_manager)
            present = BDD(tmp, dd_manager, "jx_" + str(i) + "_ps")
            dd.bdd_free(dd_manager, tmp)
            present_vars.append(present)
            tmp = dd.bdd_new_var(dd_manager)
            next = BDD(tmp, dd_manager, "jx_" + str(i) + "_ns")
            dd.bdd_free(dd_manager, tmp)
            next_vars.append(next)
            
            # write to Variables list in marduk
            var = marduk_utils.Variable('jx_%s' % i, marduk_utils.VariableType.STATE, present, next)
            self.__marduk.add_variable(var)

        return(present_vars,next_vars)


    def killArrays(self):
        """
        Kills the x and y arrays which store the intermediate results of the fixpoints
        from the computation of the winning region.
        """
        self.__xArray = None
        self.__yArray = None

    def killXArrays(self):
        """
        Kills the x array which store the intermediate results of the fixpoints
        from the computation of the winning region.
        """
        self.__xArray = None
    
        
    def killYArrays(self):
        """
        Kills the y array which store the intermediate results of the fixpoints
        from the computation of the winning region.
        """
        self.__yArray = None

        
    def killTransitions(self):
        self.__transition1 = None
        self.__transition2 = None
        self.__transition12 = None
        self.__transitionjx = None

    def killWinReg(self):
        """
        Kills the BDD representing the winning region.
        """
        self.__winningRegion = None

    def killAssumptionsAndGuarantees(self):
        self.__guarantees = None
        self.__assumptions = None

###################### get functions ########################################
            

    def getWinningRegion(self):
        if self.__winningRegion == None:
            raise Exception("WinningRegion not initialized or killed!")
        return self.__winningRegion.copy()
    winRegion = property(getWinningRegion)

    def getyArray(self):
        if self.__yArray == None:
            raise Exception("yArray BDD not initialized or killed!")
        return self.__yArray
    Y = property(getyArray)

    def getxArray(self):
        if self.__xArray == None:
            raise Exception("xArray BDD not initialized or killed!")        
        return self.__xArray
    X = property(getxArray)

    def getGuarantees(self):
        if self.__guarantees:
            return self.__guarantees
        else:
            raise MardukException("Guarantees not initialized or killed.")
    guarantees = property(getGuarantees)

    def getAssumptions(self):
        if self.__assumptions:
            return self.__assumptions
        else:
            raise MardukExeption("Assumptions not initialized or killed.")
    assumptions = property(getAssumptions)

    def getTransition1(self):
        if self.__transition1:
            return self.__transition1.copy()
        else:
            raise MardukException("Transition1 not initialized or killed.")
    trans1 = property(getTransition1)

    def getTransition2(self):
        if self.__transition2:
            return self.__transition2.copy()
        else:
            raise MardukException("Transition2 not initialized or killed.")
    trans2 = property(getTransition2)

    def getTransition12(self):
        if self.__transition12:
            return self.__transition12.copy()
        else:
            raise MardukException("Transition12 not initialized or killed.")
    trans12 = property(getTransition12)

    #def getTransition(self):
    #    return self.__transition.copy()
    #trans = property(getTransition)
    
    def getTransitionjx(self):
        if self.__transitionjx:
            return self.__transitionjx.copy()
        else:
            raise MardukException("Transitionjx not initialized or killed.")
        
    transjx = property(getTransitionjx)
    
    def getInit1(self):
        if self.__init1:
            return self.__init1.copy()
        else:
            raise MardukException("init1 not initialized")
    init1 = property(getInit1)

    def getInit2(self):
        if self.__init2:
            return self.__init2.copy()
        else:
            raise MardukException("init2 not initialized")
    init2 = property(getInit2)

    def getInit12(self):
        return self.__init12.copy()
    init12 = property(getInit12)

    def getInit(self):
        if self.__init:
            return self.__init.copy()
        else:
            raise MardukException("init not initialized")
    init = property(getInit)

    def getInitjx(self):
        return self.__initjx.copy()
    initjx = property(getInitjx)   

    def getJxPsVars(self):
        return [element for element in self.__jx_ps_vars]
    jx_ps_vars = property(getJxPsVars)   

    def getJxNsVars(self):
        return [element for element in self.__jx_ns_vars]
    jx_ns_vars = property(getJxNsVars)   
