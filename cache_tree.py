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


from bddwrap import BDD

#======================================================================
class NodeType:
    NODE = 0x01
    LEAF = 0x02
    

#======================================================================
class Node:
    #----------------------------------------------------------------------
    def __init__(self, n_type = NodeType.NODE, index = 0, max_index = 0, parent = None):
        self.node_type = n_type
        self.one_child = None
        self.zero_child = None
        self.parent = parent
        self.index = index
        self.max_index = max_index
        self._max_support = 0

    #----------------------------------------------------------------------
    def __get_max_support(self):
        return self._max_support

    maxSupport = property(__get_max_support)


    #----------------------------------------------------------------------
    def remove_wire(self, support, index=0):
        assert(self._max_support == support)
        if self.one_child != None and self.one_child.maxSupport == support:
            self.one_child.remove_wire(support, index+1)
        else:
            if self.zero_child != None:
                self.zero_child.remove_wire(support, index+1)
                

        one_support = 0
        if self.one_child != None:
            one_support = self.one_child.maxSupport
        zero_support = 0
        if self.zero_child != None:
            zero_support = self.zero_child.maxSupport
            
        self._max_support = max(one_support, zero_support)

    #----------------------------------------------------------------------
    def get_child(self, signature, support, index=0):

        if self._max_support < support:
            self._max_support = support
            
        if index == self.max_index:
            if signature[index]:
                if self.one_child == None:
                    self.one_child = Leaf(parent = self)
                return self.one_child
            else:
                if self.zero_child == None:
                    self.zero_child = Leaf(parent = self)
                return self.zero_child
        else:
            next_index = index + 1
            if signature[index]:
                if self.one_child == None:
                    self.one_child = Node(NodeType.NODE, next_index, max_index=self.max_index, parent = self)
                return self.one_child.get_child(signature, support, next_index)
            else:
                if self.zero_child == None:
                    self.zero_child = Node(NodeType.NODE, next_index, max_index=self.max_index, parent = self)
                return self.zero_child.get_child(signature, support, next_index)

    #----------------------------------------------------------------------
    def clear_leafs(self):
        if self.one_child != None:
            if self.one_child.node_type == NodeType.LEAF:
                self.one_child = Leaf(parent=self)
            else:
                self.one_child.clear_leafs()

        if self.zero_child != None:
            if self.zero_child.node_type == NodeType.LEAF:
                self.zero_child = Leaf(parent=self)
            else:
                self.zero_child.clear_leafs()

    #----------------------------------------------------------------------
    def clear_childs(self):
        if self.one_child != None:
            self.one_child.clear_childs()
            self.one_child = None
        if self.zero_child != None:
            self.zero_child.clear_childs()
            self.zero_child = None

    #----------------------------------------------------------------------
    def dump_tree(self, offset = ""):
         print offset, "[Index: ", self.index, ", Support: ", self._max_support,"]"
         if self.one_child != None:
             self.one_child.dump_tree(offset + "  ")
         else:
             print offset, "  [One Child: Not yet constructed]"

         if self.zero_child != None:
             self.zero_child.dump_tree(offset + "  ")
         else:
             print offset, "  [Zero Child: Not yet constructed]"


#======================================================================
class Leaf (Node):

    num_instances = 0  # Static instance counter to compute average collision length list (num_wires / num_leafs)
    #----------------------------------------------------------------------
    def __init__(self, parent):
        Leaf.num_instances += 1
        Node.__init__(self, NodeType.LEAF, 0, parent = parent)
        self.__wires = []

    #----------------------------------------------------------------------
    def __del__(self):
        Leaf.num_instances -= 1
        
    #----------------------------------------------------------------------
    def add_wire(self, wire, support):
        if(self._max_support < support):
            self._max_support = support
            
        self.__wires.append((wire, support))

    #----------------------------------------------------------------------
    def get_wires(self):
        return self.__wires

    #----------------------------------------------------------------------
    def dump_tree(self, offset = ""):
        print offset, "[Leaf]: ", self.__wires

    #----------------------------------------------------------------------
    def remove_wire(self, support, index=0):
        new_max = 0
        new_wires = []
        for (wire, wire_supp) in self.__wires:
            if support != wire_supp:
                if wire_supp > new_max:
                    new_max = wire_supp
                
                new_wires.append((wire, wire_supp))
            else:
                support = -1

        self.__wires = new_wires
        print "remove wire, new max: ", new_max
        self._max_support = new_max
                

#======================================================================
class CacheTree:
    #----------------------------------------------------------------------
    def __init__(self, vectors, cubes, dd_mgr):
        self.__num_entries = 0
        self.__vectors = vectors
        self.__cubes = cubes
        self.root = Node(max_index=len(vectors)-1)
        self.__dd_mgr = dd_mgr
        self.__max_collision_length = 0

    #----------------------------------------------------------------------
    def get_max_collision_length(self):
        return self.__max_collision_length
    max_collision_length = property(get_max_collision_length)

    #----------------------------------------------------------------------
    def get_avg_collision_length(self):
        num_leafs = len(self._get_all_leafs(self.root))
        if num_leafs:
            return float(self.__num_entries) / num_leafs
        else:
            return None
    avg_collision_length = property(get_avg_collision_length)

    #----------------------------------------------------------------------
    def _get_all_leafs(self, node):
        if node == None:
            return []
        elif node.node_type == NodeType.LEAF:
            return [node]
        
        return self._get_all_leafs(node.zero_child) + self._get_all_leafs(node.one_child)
    
    #----------------------------------------------------------------------
    def get_collision_lengths(self):
        return [len(leaf.get_wires()) for leaf in self._get_all_leafs(self.root)]
    
    #----------------------------------------------------------------------
    def insert(self, signature, wire, support):
        self.__num_entries += 1
        leaf = self.root.get_child(signature, support)
        leaf.add_wire(wire, support)
        if len(leaf.get_wires()) > self.__max_collision_length:
            self.__max_collision_length = len(leaf.get_wires())

    #----------------------------------------------------------------------
    def __len__(self):
        return self.__num_entries

    #----------------------------------------------------------------------
    def remove_biggest(self):
        self.__num_entries -= 1
        self.root.remove_wire(self.root.maxSupport)

    #----------------------------------------------------------------------
    def clear(self):
        self.root.clear_leafs()

    #----------------------------------------------------------------------
    def find(self, f, fd, find_closest = False):
        """
        Returns a list of possible matches, or closest matches, if there are no matches.
        The return value is either (matches, []) or ([], closest_matches), or ([], []) if
        the cache is empty. If the "find_closest" flag is False, then just the list of
        matches (possibly empty) is returned.
        """

        wires = []

        closest_node = self.root
        
        next_nodes = [self.root]
        while len(next_nodes) > 0:
            node = next_nodes.pop()
            if(node.node_type == NodeType.LEAF):
                wires += [wire for (wire, support) in node.get_wires()]
                closest_node = node
            else:                
                if (self.__cubes[node.index] <= f):  # val_f
                    if node.one_child != None:
                        next_nodes += [node.one_child]
                elif (self.__cubes[node.index] <= fd): # val_fd
                    if node.one_child != None:
                        next_nodes += [node.one_child]
                    if node.zero_child != None:
                        next_nodes += [node.zero_child]
                else:
                    if node.zero_child != None:
                        next_nodes += [node.zero_child]

                if len(next_nodes) == 0:  # No further nodes to process. This one is the closest.
                    closest_node = node

        if not find_closest:
            return wires
                    
        if len(wires):
            return (wires, [])

        close_wires = []
        while(len(close_wires) == 0):
            next_nodes = [closest_node]
            while len(next_nodes) > 0:
                node = next_nodes.pop()
                if(node.node_type == NodeType.LEAF):
                    close_wires += [wire for (wire, support) in node.get_wires()]
                else:
                    if node.one_child != None:
                        next_nodes += [node.one_child]
                    if node.zero_child != None:
                        next_nodes += [node.zero_child]

            if len(close_wires) == 0:
                closest_node = closest_node.parent

            if not closest_node:
                assert(self.__num_entries == 0)  # Reaching this point means that the cache is empty, or that there is a bug.
                return ([], [])
        assert(len(close_wires))
        return ([], close_wires)
        
        

    #----------------------------------------------------------------------
    def reorganize(self, new_cubes, class_vectors, num_new, code_generator, marduk_vars):

        self.__cubes = new_cubes
        all_wires = []
        next_nodes = [(self.root, [])]
        while len(next_nodes) > 0:
            (node, sig) = next_nodes.pop()
            if(node.node_type == NodeType.LEAF):
                node_wires = node.get_wires()
                all_wires += [(wire, support, sig) for (wire, support) in node_wires]
            else:
                if node.one_child != None:
                    sig.append(1)
                    next_nodes += [(node.one_child, sig)]
                if node.zero_child != None:
                    sig.append(0)
                    next_nodes += [(node.zero_child, sig)]

        self.root.clear_childs()
        
        for (wire, support, signature) in all_wires:
            sig = signature[num_new:]
            bdd = code_generator.wire2BDD(wire, marduk_vars)
            index = len(class_vectors)-num_new
            for vect in class_vectors[len(class_vectors)-num_new:]:
                sig.append((self.__cubes[index]) <= bdd)
                index += 1
                
            leaf = self.root.get_child(sig, support)
            leaf.add_wire(wire, support)

