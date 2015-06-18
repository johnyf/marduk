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

class Strategy(object):
    """
    This class computes and stores the strategy
    """
    
    def __init__(self, marduk, keep_rhos=False):
        self.__marduk = marduk
        self.__strategy_bdd = None
        self.__rho1_bdd = None
        self.__rho2_bdd = None
        self.__rho3_bdd = None
        self.__keep_rhos = keep_rhos


    def calcStrategy(self):
        marduk_mgr = self.__marduk.dd_mgr
        
        init = self.__marduk.winning_region.init12 
        transitions = self.__marduk.winning_region.trans12
        reachable_states =  self.__marduk.winning_region.reachableStates(init, transitions, BDD.ONE(marduk_mgr))
        reachable_states.name = "reachable_states"
        del init, transitions
        
        n = len(self.__marduk.winning_region.guarantees)
        
        strategy = BDD.ZERO(marduk_mgr)
        strategy.name = "strategy"

        # Build strategy rho3
        strategy += self._calc_rho3(marduk_mgr, n, reachable_states)

        self.__marduk.winning_region.killXArrays()
        
        # Build strategy rho2
        strategy += self._calc_rho2(marduk_mgr, n, reachable_states)

        self.__marduk.winning_region.killYArrays()
        
        # Build strategy rho1
        strategy += self._calc_rho1(marduk_mgr, n)
        

        self.__strategy_bdd = strategy
        
        self.__marduk.winning_region.killArrays() 
        self.__marduk.winning_region.killTransitions() 
        self.__marduk.winning_region.killAssumptionsAndGuarantees() 
        self.__strategy_bdd //= reachable_states

        if False:
            self._dump_strategy()


    def _dump_strategy(self):

        from marduk_utils import comp_name_bdd_tuples
        from nusmv import dd
        from bddwrap import BDD
        list = []
        marduk_mgr = self.__marduk.dd_mgr
        for var in self.__marduk.vars:
            list.append((var.name + '_ps', var.ps.ptr, var.ps.mgr))
            list.append((var.name + '_ns', var.ns.ptr, var.ns.mgr))

        list.sort(cmp=comp_name_bdd_tuples)
                
        names = []
        for element in list:
            names.append(element[0])
            dd.bdd_free(marduk_mgr, element[1])
        list = None
        
        # The list of input names must begin with a dummy entry to match the "mysterious" variable
        # which is always introduced by NuSMV, and which always has the lowest index in the BDD.
        # Without this entry the mapping between BDD nodes and string names would be off-by-one,
        # and _ps and _ns entries would become confused.
        names = ["dummy"] + names

        functions = [self.__strategy_bdd.ptr]
        onames = ["strategy"]
        file = open("strategy.blif", 'w')

        file.write(".model strategy_relation\n")
        file.write(".inputs ")
        inputs = []
        outputs = []
        from marduk_utils import VariableType
        for var in self.__marduk.vars:
            if var.type == VariableType.INPUT:
                inputs += [var.name + "_ps", var.name + "_ns"]
            else:
                inputs += [var.name + "_ps"]
                outputs += [var.name + "_ns"]
                
        signals = inputs + outputs
        for signal in signals:
            file.write(signal + " ")
        file.write("\n")
        file.write("\n# The last %s inputs listed above are the outputs of the relation.\n\n" % len(outputs))
        file.write(".outputs strategy\n")
        
        dd.bdd_DumpBlifBody(marduk_mgr, functions, names, onames, file)
        dd.bdd_free(marduk_mgr, functions[0])

        file.write(".end\n")
        file.close()
        print "Dumped strategy to file 'strategy.blif'. Number of outputs is %d." % len(outputs)
        



    def _calc_rho1(self, marduk_mgr, n):
        mod_trans = self.__marduk.winning_region.transjx
        start_state = self.__marduk.winning_region.initjx
        jx_present_vars = self.__marduk.winning_region.jx_ps_vars
        jx_next_vars = self.__marduk.winning_region.jx_ns_vars
        winRegion = self.__marduk.winning_region.winRegion
        rho1 = BDD.ZERO(marduk_mgr)
        rho1.name = "rho_1"
        jp1 = start_state
        guarantees = self.__marduk.winning_region.guarantees
        transitions = self.__marduk.winning_region.trans12
        from marduk_utils import VariableType
        present_vars = [var.ps for var in self.__marduk.vars if var.type != VariableType.STATE]
        next_vars = [var.ns for var in self.__marduk.vars if var.type != VariableType.STATE]

        jx_equal_j = "" # just initialize variable jx_equal_j, so that it can also be deleted even if (n == 0).
        
        for j in range(0,n):
            jx_equal_j = jp1
            jp1 = mod_trans / jp1
            rho1 += jx_equal_j * guarantees[j] * jp1
            jp1 = jp1.swapVariables(jx_present_vars, jx_next_vars) 
        del jx_equal_j, jp1
        
        next_winRegion = winRegion.swapVariables(present_vars, next_vars)

        rho1 *=  winRegion * transitions * next_winRegion
        if self.__keep_rhos: self.__rho1_bdd = rho1
        self.__rho1_size = rho1.size

        return rho1
        
    
    def _calc_rho2(self, marduk_mgr, n, reachable_states):
        mod_trans = self.__marduk.winning_region.transjx
        start_state = self.__marduk.winning_region.initjx
        jx_present_vars = self.__marduk.winning_region.jx_ps_vars
        jx_next_vars = self.__marduk.winning_region.jx_ns_vars
        transitions = self.__marduk.winning_region.trans12
        rho2 = BDD.ZERO(marduk_mgr)
        rho2.name = "rho_2"
        jp1 = start_state
        yArray = self.__marduk.winning_region.Y
        from marduk_utils import VariableType
        present_vars = [var.ps for var in self.__marduk.vars if var.type != VariableType.STATE]
        next_vars = [var.ns for var in self.__marduk.vars if var.type != VariableType.STATE]

        jx_equal_j = "" # just initialize variable jx_equal_j, so that it can also be deleted even if (n == 0).
        
        for j in range(0,n):            
            low = yArray[j][0]
            next_low = ""  # just initialize variable next_low, so that it can also be deleted even if (maxr == 1).
            rho2_tmp = BDD.ZERO(marduk_mgr)

            maxr = len(yArray[j])
            for r in range(1,maxr):
                next_low = low.swapVariables(present_vars, next_vars)
                rho2_tmp += (yArray[j][r]//reachable_states) * ((~low)//reachable_states) * next_low
                low += yArray[j][r]
            del low, next_low
            
            jx_equal_j = jp1
            jp1 = jp1.swapVariables(jx_present_vars, jx_next_vars)
            rho2 += rho2_tmp * jx_equal_j * jp1
            del rho2_tmp
            jp1 = mod_trans / jx_equal_j 
            jp1 = jp1.swapVariables(jx_present_vars, jx_next_vars)
        del jp1, jx_equal_j
        
        rho2 *= transitions
        if self.__keep_rhos: self.__rho2_bdd = rho2
        self.__rho2_size = rho2.size

        return rho2

    
    def _calc_rho3(self, marduk_mgr, n, reachable_states):
        mod_trans = self.__marduk.winning_region.transjx
        start_state = self.__marduk.winning_region.initjx
        jx_present_vars = self.__marduk.winning_region.jx_ps_vars
        jx_next_vars = self.__marduk.winning_region.jx_ns_vars
        assumptions = self.__marduk.winning_region.assumptions
        transitions = self.__marduk.winning_region.trans12
        rho3 = BDD.ZERO(marduk_mgr)
        rho3.name = "rho_3"
        jp1 = start_state
        xArray = self.__marduk.winning_region.X
        from marduk_utils import VariableType
        present_vars = [var.ps for var in self.__marduk.vars if var.type != VariableType.STATE]
        next_vars = [var.ns for var in self.__marduk.vars if var.type != VariableType.STATE]

        jx_equal_j = "" # just initialize variable jx_equal_j, so that it can also be deleted even if (n == 0).
        
        for j in range(0,n):   
            low = BDD.ZERO(marduk_mgr)
            rho3_tmp = BDD.ZERO(marduk_mgr)
            
            maxr = len(xArray[j])
            for r in range(0,maxr):
                
                m = len(xArray[j][r])
                for i in range(0,m):
                    next_x = xArray[j][r][i].swapVariables(present_vars, next_vars)
                    rho3_tmp += (xArray[j][r][i]//reachable_states) * ((~low)//reachable_states) * (~assumptions[i]) * next_x
                    del next_x
                    low += xArray[j][r][i]

            jx_equal_j = jp1
            jp1 = jp1.swapVariables(jx_next_vars, jx_present_vars)
            rho3 += rho3_tmp * jx_equal_j * jp1
            del rho3_tmp
            jp1 = mod_trans / jx_equal_j 
            jp1 = jp1.swapVariables(jx_present_vars, jx_next_vars)
        del jx_equal_j, jp1

        rho3 *= transitions
        if self.__keep_rhos: self.__rho3_bdd = rho3
        self.__rho3_size = rho3.size

        return rho3

    
    def killStrategy(self):
        """
        Kills the strategy (and its parts rho1-3) and the x and y arrays with the intermediate results from
        winning region computation
        """
        self.__strategy_bdd = None
        self.__rho1_bdd = None
        self.__rho2_bdd = None
        self.__rho3_bdd = None
        self.__marduk.winning_region.killArrays()
        self.__marduk.winning_region.killAssumptionsAndGuarantees()
        self.__marduk.winning_region.killWinReg()
        




###################### get functions ########################################

    def get_strategy_bdd(self):
        if self.__strategy_bdd == None:
            raise Exception("Strategy BDD not initialized or killed!")
        return self.__strategy_bdd.copy()

    strategy_bdd = property(get_strategy_bdd)

    def get_rho1_bdd(self):
        if self.__rho1_bdd == None:
            raise Exception("rho1 BDD not initialized or killed!")
        return self.__rho1_bdd.copy()

    rho1_bdd = property(get_rho1_bdd)

    def get_rho2_bdd(self):
        if self.__rho2_bdd == None:
            raise Exception("rho2 BDD not initialized or killed!")
        return self.__rho2_bdd.copy()

    rho2_bdd = property(get_rho2_bdd)

    def get_rho3_bdd(self):
        if self.__rho3_bdd == None:
            raise Exception("rho3 BDD not initialized or killed!")
        return self.__rho3_bdd.copy()

    rho3_bdd = property(get_rho3_bdd)


    def get_rho1_size(self):
        return self.__rho1_size
    rho1_size = property(get_rho1_size)

    def get_rho2_size(self):
        return self.__rho2_size
    rho2_size = property(get_rho2_size)

    def get_rho3_size(self):
        return self.__rho3_size
    rho3_size = property(get_rho3_size)
