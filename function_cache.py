##  ===========================================================================
##  Author: Martin Weiglhofer <weiglhofer@ist.tugraz.at>
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

import random
import resource
import time
from marduk_utils import MardukException
from marduk_utils import VariableType
from bddwrap import BDD
from cache_tree import CacheTree
from nusmv import dd

class Logic:
    NO_LOGIC_OP = 0x0000
    NOT         = 0x0001
    AND         = 0x0010
    OR          = 0x0100
    IMPLIES     = 0x1000

class FunctionCache(object):
    """
    Implements caching for bdd objects.

    
    """

    #======================================================================
    #  PROPERTIES
    #======================================================================

    #----------------------------------------------------------------------
    def __get_num_class_vectors(self, value):
        return self.__num_class_vectors

    #----------------------------------------------------------------------
    def __get_cache_size(self):
        return len(self.__cachetree)

    #----------------------------------------------------------------------
    def __set_cache_size(self, value):
        self.__max_cache_size = value
        self.__caching_enabled = (self.__max_cache_size != 0)

        if self.__max_cache_size == 0:
            self.__cachetree.clear()
        else:
            if(self.__max_cache_size != None):
                while(self.__max_cache_size < len(self.__cachetree)):
                    self.__cachetree.remove_biggest()

    #----------------------------------------------------------------------
    def __get_check_logic_gates(self):
        return self.__check_logic_gates

    #----------------------------------------------------------------------
    def __set_check_logic_gates(self, value):
        self.__check_logic_gates = value

    #----------------------------------------------------------------------
    def __get_update_sigs(self):
        return self.__update_sigs_size

    #----------------------------------------------------------------------
    def __set_update_sigs(self, value):
        if value > self.__num_class_vectors:
            self.__update_sigs_size = self.__num_class_vectors
        else:
            self.__update_sigs_size = value


    #----------------------------------------------------------------------
    def __get_num_hits(self):
        return self.__num_hits

    #----------------------------------------------------------------------
    numClassVectors = property(__get_num_class_vectors)
    """
    Number of classification vectors that are used to check if a
    function matches a given interval. If all classification vectors
    give the same result for the function and the interval, then the
    BDDs of the function and the interval are compared.
    """

    #----------------------------------------------------------------------
    cacheSize = property(__get_cache_size, __set_cache_size)
    """
    Limit the size of the cache. The cache size unit is 'number of
    stored objects'.  'None' denotes a cache that is always big enough
    to take a new object into the cache. If the cache size is set to
    zero then caching is turned off.
    """

    #----------------------------------------------------------------------
    checkLogicGates = property(__get_check_logic_gates, __set_check_logic_gates)
    """
    Additionally, to test only cached object we can also use imaginary
    constructed gates. For example, for any cached function f one can
    use not(f). Or one may like to check for any two cached functions
    f1 and f2 if (f1 /\ f2) fits into the given interval. This
    property allows you to select the type of logic gates used.

    Use any combination of the values declared in the class Logic, e.g.,
    (NOT | OR) tests for not and or combinations.
    """

    #----------------------------------------------------------------------
    updateSignatures = property(__get_update_sigs, __set_update_sigs)
    """
    If we do a reconstruction of a bdd, but the bdd does not fit into
    the interval, then we calculate a discriminating classification
    vector. This vector is stored in a list. The property
    updateSignatures specifies the max. length of this list. If the
    max. length is reached, then all signatures are recalculated.
    """

    #----------------------------------------------------------------------
    numHits = property(__get_num_hits)
    """
    Return the number of cache hits
    """

    #======================================================================
    #  METHODS
    #======================================================================

    #----------------------------------------------------------------------
    def __init__(self, marduk_vars, dd_mgr, code_generator=None, num_class_vectors=1024, strat_dc=None):
        """
        The 'code_generator' is used to translate wires to bdds from
        previously constructed circiuts.
        """

        #random.seed(time.time())    # Bad idea --> Not deterministic across runs
        random.seed(1468192489)      # Use "magic number" as seed, so that subsequent runs produce the same results.
        
        self.__dd_mgr = dd_mgr
        self.__marduk_vars = marduk_vars[:] # copy list instead of using reference to original, in order to keep order of elements

        # create a list of combinational inputs from the marduk_vars. Only this ones should be used for the class-vectors
        self.__combinational_inputs = []
        for var in marduk_vars:
            if var.type == VariableType.INPUT:
                self.__combinational_inputs += [var.ps, var.ns]
            else:
                self.__combinational_inputs += [var.ps]
                
        self.__code_generator = code_generator
        self.__max_cache_size = None
        self.__caching_enabled = (self.__max_cache_size != 0)
        self.__check_logic_gates = Logic.NOT
        self.__update_sigs_size = 32
        self.__strat_dc = strat_dc

        self.__num_class_vectors = num_class_vectors
        self.__generate_class_vectors()
        self.clear_cache()

    #----------------------------------------------------------------------
    def clear_cache(self):
        """
        Clear the cache used for storing intermediate functions
        """
        self.__cachetree = CacheTree(self.__class_vectors, self.__cubes, self.__dd_mgr)

        self.__num_hits = 0
        self.__num_hits_logic_combination = { Logic.NOT : 0, Logic.AND : 0, Logic.OR : 0, Logic.IMPLIES : 0 }
        self.__num_miss = 0
        self.__bdd_reconstructs = 0
        self.__num_invald_reconstructs = 0
        self.__cache_shrinks = 0
        self.__bdd_reconstruct_time = 0
        self.__num_sigmatch = 0
        self.__sigmatch_time = 0
        self.__shared_size = 0
        self.__total_lookup_time = 0
        self.__total_sigcalc_time = 0
        self.__num_sigcalc = 0
        self.__num_reorganize = 0
        self.__reorganize_time = 0
        self.__new_classifiers = []

        #self.__errors = 0
    #----------------------------------------------------------------------

    def find_suitable_function(self, f, fd, find_closest=False):
        """
        This is just a wrapper to allow accurate timing.
        """
        begin = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        result = self._find_suitable_function(f, fd, find_closest)
        end = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime

        self.__total_lookup_time += end - begin
        return result

    def _find_suitable_function(self, f, fd, find_closest = False):
        """
        Given an interval, i.e., f and fd, this function checks if we
        have already encountered another function within that
        interval. If yes, we return that function. If no, we return 'None'

        If the find_closest flag is True, and no hit is found, the return value
        is a tuple (None, None, closest) where 'closest' is a list of close matches.
        """
        if(self.__caching_enabled):

            if find_closest:
                (wires, closest) = self.__cachetree.find(f, fd, find_closest)
                if wires:
                    closest = wires
            else:
                wires = self.__cachetree.find(f, fd, find_closest)
            wires.sort()
            for wire in wires:
                bdd = self.__timed_reconstruct_bdd(wire, f, fd)
                if bdd != None:
                    self.__num_hits += 1
                    self.__shared_size += self.__code_generator.circuit_size(wire)
                    print "### Reusing wire", wire
                    print "### Candidates were:", [w for w in wires]
                    
                    if not find_closest:
                        return(bdd, wire)
                    else:
                        return(bdd, wire, None)

            if self.__check_logic_gates & Logic.NOT:
                wires = self.__cachetree.find(~fd, ~f)
                wires.sort()
                for wire in wires:
                    bdd = self.__timed_reconstruct_bdd(wire, ~fd, ~f)
                    if bdd != None:
                        wire = self.__code_generator.add_not(wire)
                        self.__num_hits_logic_combination[Logic.NOT] += 1
                        self.__shared_size += self.__code_generator.circuit_size(wire)
                        print "### Reusing (negated) wire", wire
                        print "### Candidates were:", [w for w in wires]

                        if not find_closest:
                            return(~bdd, wire)
                        else:
                            return(~bdd, wire, None)
                    
            self.__num_miss += 1
            if not find_closest:
                return (None, None)
            else:
                return (None, None, closest)
    
            
        self.__num_miss += 1
        if not find_closest:
            return (None, None)
        else:
            return (None, None, None)
    
            

    #----------------------------------------------------------------------
    def __timed_reconstruct_bdd(self, wire, f, fd):
        self.__bdd_reconstructs += 1
        before = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        bdd = self.__code_generator.wire2BDD(wire, self.__marduk_vars)
        self.__bdd_reconstruct_time += (resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime - before)
                        
        if((bdd >= f) and (bdd <= fd)):
            return bdd
        elif self.__update_sigs_size > 0:    
            print "construct discriminating vector"
            discriminator = self.__calculate_discriminator(bdd, f, fd)
            # put vector into list
            self.__new_classifiers.append(discriminator)
            # if limit is reached, then recalculate all signatures
            if len(self.__new_classifiers) >= self.__update_sigs_size:
                print "### REORGANIZE CACHE"
                cv = self.__class_vectors[len(self.__new_classifiers):]
                self.__cubes = self.__cubes[len(self.__new_classifiers):]
                self.__class_vectors = cv + self.__new_classifiers
                for vect in self.__new_classifiers:
                    self.__cubes.append(self.__calc_cube4vec(vect))
               
                print "New classification vectors: " , self.__class_vectors
                before = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
                self.__cachetree.reorganize(self.__cubes, self.__class_vectors, len(self.__new_classifiers), self.__code_generator, self.__marduk_vars)
                self.__reorganize_time += (resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime - before)

                self.__num_reorganize += 1
                self.__new_classifiers = []

        self.__num_invald_reconstructs += 1
        return None

    #----------------------------------------------------------------------
    def __calculate_discriminator(self, bdd, f, fd):
        d = (~bdd & f) | (bdd & ~fd)
        #cube = d.bddLargestCube()
        ptr = d.ptr
        (largest_cube_ptr, length) = dd.bdd_largest_cube(d.mgr, ptr)
        largest_cube = BDD(largest_cube_ptr, d.mgr, "largest_cube")
        dd.bdd_free(d.mgr, largest_cube_ptr)
        dd.bdd_free(d.mgr, ptr)

      
        vec = []
        for input in self.__combinational_inputs:

            tmp = largest_cube & input
            if tmp == largest_cube:
                vec.append(1)
            else:
                tmp3 = largest_cube & (~input)
                if tmp3 == largest_cube:
                    vec.append(0)
                else:
                    vec.append(random.randint(0, 1))
        
        return vec


    #----------------------------------------------------------------------
    def update(self, r, signal):
        """
        Given an bdd r and a signal that has been generated by the
        code_generator, this function updates the internal cache.
        That is, it stores the function for later reuse.
        """

        if(self.__caching_enabled):
            if self.__max_cache_size != None and len(self.__cachetree) > self.__max_cache_size:
                print "[DBG]: Shrink cache!"
                self.__cache_shrinks += 1
                self.__cachetree.remove_biggest()

            bdd = r
            support_size = self._get_support_size(bdd)
            signature = self.__calculate_signature(r)

            self.__cachetree.insert(signature, signal, support_size)
            print "[DBG]: Function cache updated with wire '%s': New size %d!" % (signal, len(self.__cachetree))


    #----------------------------------------------------------------------
    def print_stats(self):
        """
        Print caching statistics.
        """
        total = (self.__num_hits +
                 self.__num_miss + self.__num_hits_logic_combination[Logic.NOT] +
                 self.__num_hits_logic_combination[Logic.AND] +
                 self.__num_hits_logic_combination[Logic.OR] +
                 self.__num_hits_logic_combination[Logic.IMPLIES])
        
        print "Caching Statistics:"
        # Current size of the cache
        print "  Cache size:   %d" % len(self.__cachetree)
        # The total number of 'find_suitable_function' calls, i.e.
        # the number of cache accesses
        print "  No. accesses: %d" % total
        # How much time did we spend on lookups? Total and average.
        print "  Total time for lookups: %f (avg: %f)" % (self.__total_lookup_time, self.__total_lookup_time / total if total > 0 else 0)
        # Hit/Miss statistics: How often did we find a suitable function (hit) versus
        # how often a cache access did end without finding a suitable function (miss)
        print "  Hit/Miss:   : %d/%d (%f/%f)" % (self.__num_hits, self.__num_miss, self.__in_percent(total-self.__num_miss, total), self.__in_percent(self.__num_miss, total))
        print "  Sharing size %d (avg: %f)" % (self.__shared_size, (self.__shared_size / (total-self.__num_miss))
                                                                                         if self.__shared_size else 0)

        print "  Logic Gates Hits (not/and/or/implies): %d/%d/%d/%d" % (self.__num_hits_logic_combination[Logic.NOT], self.__num_hits_logic_combination[Logic.AND], self.__num_hits_logic_combination[Logic.OR], self.__num_hits_logic_combination[Logic.IMPLIES])
        # How often did we reconstruct a bdd from wires
        print "  No. BDD reconstruct: %d" % self.__bdd_reconstructs
        if self.__bdd_reconstructs > 0:
            print "  Time reconstruct: %f (avg: %f)" %  (self.__bdd_reconstruct_time, self.__bdd_reconstruct_time / self.__bdd_reconstructs)
        # How often did we reconstruct a function that did not fit the interval?
        print "  No. useless BDD reconstructs: %d" % self.__num_invald_reconstructs
        # How often did we call a signature match
        #print "  No. Sig. matches: %d" % self.__num_sigmatch
        if self.__num_sigmatch > 0:
            print "  Time for sig. comparison: %f (avg: %f)" % (self.__sigmatch_time, self.__sigmatch_time / self.__num_sigmatch)
        # How often did we remove an element from the cache (due to
        # the size restriction)
        print "  No. Cache shrinks: %d" % self.__cache_shrinks
        # How often did we compute signatures?
        print "No. of signature calculations: %d" % self.__num_sigcalc
        # How long did signature calculation take?
        print "Time for signature calculation: %f (avg: %f)" % (self.__total_sigcalc_time, self.__total_sigcalc_time / float(self.__num_sigcalc) if self.__num_sigcalc else 0)
        # Maximum length of collision lists in the cache tree.
        print "Max. length of collision lists:", self.__cachetree.max_collision_length
        # Average length of collision lists in the cache tree.
        print "Avg. length of collision lists:", self.__cachetree.avg_collision_length
        # Number of leafs in cache tree
        from cache_tree import Leaf
        print "Number of Leaf instances alive:", Leaf.num_instances
        print "Number of Leafs in current cache tree:", len(self.__cachetree._get_all_leafs(self.__cachetree.root))
        print "Collision List Lengths:", self.__cachetree.get_collision_lengths()

        print "Number of cache reorganizations:", self.__num_reorganize
        print "Time for cache reorganizations:", self.__reorganize_time
        #print "Errors:", self.__errors

        
    #----------------------------------------------------------------------
    def __in_percent(self, x, total):
        if total == 0:
            return 0.0
        else:
            return 100.0/total * x

    #----------------------------------------------------------------------
    def _get_support_size(self, f):
        """
        Return the support of a function (given as bdd)
        """
        return (f.support()).get_size()

    #----------------------------------------------------------------------
    def __generate_class_vectors(self):
        max_vecs = pow(2, len(self.__combinational_inputs))
        num_vecs = min(self.__num_class_vectors, max_vecs)
        print "[DBG]: Generating %d classification vectors." % num_vecs

        self.__class_vectors = [];
        if(self.__num_class_vectors >= max_vecs):
            print "[DBG]: Use exhaustive classification vector generation. (%d vectors)" % max_vecs
            for num in range(0, max_vecs):
                vec = [((num >> y) & 1) for y in range((len(self.__combinational_inputs))-1, -1, -1)]
                self.__class_vectors.append(vec)
        else:
            while len(self.__class_vectors) < num_vecs:
                vec = self.__generate_random_vector()
                if not self.__comprises_vect(vec, self.__class_vectors):
                    self.__class_vectors.append(vec)

        #print "[DBG]: Classification vectors: ", self.__class_vectors
        self.__num_class_vectors = len(self.__class_vectors)

        self.__cubes = []
        for vect in self.__class_vectors:
            cube = self.__calc_cube4vec(vect)
            self.__cubes.append(cube)

    #----------------------------------------------------------------------
    def __generate_random_vector(self):

        if not self.__strat_dc:
            return [random.randint(0, 1) for varindex in range(0, len(self.__combinational_inputs))]
        
        else: # Use don't care information
            vec = []
            relevant_vertices = ~self.__strat_dc
            for input in self.__combinational_inputs:

                tmp = relevant_vertices & input
                if tmp == relevant_vertices:
                    vec.append(1)
                else:
                    tmp3 = relevant_vertices & (~input)
                    if tmp3 == relevant_vertices:
                        vec.append(0)
                    else:
                        vec.append(random.randint(0, 1))
            return vec
    
    #----------------------------------------------------------------------
    def __calc_cube4vec(self, vect):
        index = 0
        cube = BDD.ONE(self.__dd_mgr)
        for input in self.__combinational_inputs:
            if vect[index] == 1:
                cube &= input
            else:
                cube &= ~input
                    
            index += 1

        return cube
    
    #----------------------------------------------------------------------
    def __comprises_vect(self, vec, class_vectors):
        for vec1 in class_vectors:
            if vec == vec1:
                return True

        return False

    #----------------------------------------------------------------------
    def __calculate_signature(self, bdd):

        begin = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        sig = []
        for i in range(0, len(self.__class_vectors)):
            vect = self.__class_vectors[i]
            cube = self.__cubes[i]
            value = (cube <= bdd)           
            sig.append(value)

        end = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
        self.__total_sigcalc_time += end - begin
        self.__num_sigcalc += 1
        return sig
        
