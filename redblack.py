#!/usr/bin/env python3
'An implementation of red-black trees'

from enum import Enum
import random

class Color(Enum):
    RED = 0
    BLACK = 1

class RedBlackTree:
    def __init__(self):
        self.root = None

    def insert(self, item):
        if self.root is None:
            self.root = Node(item=item, color=Color.BLACK)
            return self.root

        new_node = self.root._insert(item)
        new_node._insert_repair()

        self.root = self.root.root()

    def check(self):
        self.root.check()

    def __repr__(self):
        return self.root.reprwithcolor()

class Node:
    def __init__(self, item=None, parent=None, left=None, right=None, color=None):
        self.item = item
        self.parent = parent
        self.left = left
        self.right = right
        self.color = color

    def sibling(self):
        if not self.parent:
            return None
        if self == self.parent.left:
            return self.parent.right
        elif self == self.parent.right:
            return self.parent.left
        assert False

    def uncle(self):
        if not self.parent:
            return None
        return self.parent.sibling()

    def grandparent(self):
        if not self.parent:
            return None
        return self.parent.parent

    def root(self):
        if not self.parent:
            return self
        return self.parent.root()

    def check(self):
        # every node has a color
        if self.color not in (Color.RED, Color.BLACK):
            raise Exception('color is not real: {}'.format(self.color))

        # the root must be black
        if self.parent is None and self.color is not Color.BLACK:
            raise Exception('root nodes must be black: {}'.format(self.item))

        # if a node is red then both of it's children are black
        def red(node):
            return node != None and node.color == Color.RED
        if self.color == Color.RED and (red(self.left) or red(self.right)):
            raise Exception('red nodes must have black children: {}'.format(self.item))

        left_height = self.left.check() if self.left else 0
        right_height = self.right.check() if self.right else 0

        if left_height != right_height:
            raise Exception(
                'all paths must have the same number of black nodes: {}'.format(self.item)
            )

        if self.color == Color.BLACK:
            return left_height + 1
        return left_height

    def _insert(self, item):
        "A binary-search-tree insert, doesn't try to maintain any of the invariants"
        if item < self.item:
            if self.left:
                return self.left._insert(item)
            else:
                self.left = Node(item=item, parent=self, color=Color.RED)
                return self.left
        else:
            if self.right:
                return self.right._insert(item)
            else:
                self.right = Node(item=item, parent=self, color=Color.RED)
                return self.right

    def _insert_repair(self):
        "we've just been created and the tree is possibly out of balance, let's fix that!"
        if self.parent == None:
            # repaint ourselves black if necessary
            self.color = Color.BLACK
            return

        if self.parent.color == Color.BLACK:
            # the happiest case, everything is already done
            return

        def uncle_color(node):
            if not node.uncle():
                return Color.BLACK
            return node.uncle().color

        # okay, our parent is RED

        if uncle_color(self) == Color.RED:
            # repaint both the parent and the uncle BLACK
            self.parent.color = Color.BLACK
            self.uncle().color = Color.BLACK  # don't need to None check, RED nodes exist
            self.grandparent().color = Color.RED

            # fixup the grandparent, we just added a BLACK to some paths
            self.grandparent()._insert_repair()
            return

        # the most complicated case
        # the parent is red but the uncle is BLACK
        if self.grandparent().left and self == self.grandparent().left.right:
            rotate_left(self.parent)
            node = self.left
        elif self.grandparent().right and self == self.grandparent().right.left:
            rotate_right(self.parent)
            node = self.right
        else:
            node = self

        grandparent = node.grandparent()
        if node == node.parent.left:
            rotate_right(grandparent)
        else:
            rotate_left(grandparent)
        node.parent.color = Color.BLACK
        grandparent.color = Color.RED

    def set_left(self, left):
        self.left = left
        if left:
            left.parent = self

    def set_right(self, right):
        self.right = right
        if right:
            right.parent = self

    def __repr__(self):
        items = [
            item.__repr__()
            for item in [self.left, self.item, self.right]
            if item is not None
        ]
        return '<{}>'.format(','.join(items))

    def reprwithcolor(self):
        items = []

        if self.left:
            items.append(self.left.reprwithcolor())

        assert self.color in (Color.RED, Color.BLACK)
        color = 'R' if self.color == Color.RED else 'B'
        items.append('{}({})'.format(self.item, color))

        if self.right:
            items.append(self.right.reprwithcolor())

        return '<{}>'.format(','.join(items))

def traverse(node):
    'Given a node return the items in order'
    if node == None:
        return []
    return traverse(node.left) + [node.item] + traverse(node.right)

left = Node(item=10)
right = Node(item=20)
root = Node(item=15, left=left, right=right)
assert traverse(root) == [10, 15, 20]

one = Node(item=1)
two = Node(item=2,left=one)
three = Node(item=3,left=two)
assert traverse(three) == [1, 2, 3]

def reassign_parent(node, new_node):
    '''
    we want to replace node with new_node, new_node needs to be put into the same
    place in the parent as node was previously

    careful! after this node will have a "parent" which doesn't actually contain node
    '''

    if not node.parent:
        # we're done!
        new_node.parent = None
        return

    assert node in (node.parent.left, node.parent.right)
    on_left = (node == node.parent.left)

    new_node.parent = node.parent
    if on_left:
        node.parent.left = new_node
    else:
        node.parent.right = new_node

class assert_fixed_traversal:
    'the rotations should not change the order of the nodes'
    def __init__(self, func):
        self.func = func
    def __call__(self, node):
        old_traversal_order = traverse(node)
        result = self.func(node)
        new_traversal_order = traverse(result)
        assert old_traversal_order == new_traversal_order
        return result

@assert_fixed_traversal
def rotate_left(node):
    '''
    Take the given node and replace it with node.right, where the given node becomes the
    new parent's .left

    Returns the new parent.
    '''
    new_node = node.right

    # first update the parent, it should point to our new root node
    reassign_parent(node, new_node)

    # you're about to go into new_node.left, so first handle the node already there
    node.set_right(new_node.left)

    # move ourselves into position
    new_node.set_left(node)

    return new_node

@assert_fixed_traversal
def rotate_right(node):
    'Same idea as rotate_left but move everything to the right'
    new_node = node.left

    reassign_parent(node, new_node)

    # you're about to go into new_node.right, so first handle the node already there
    node.set_left(new_node.right)

    # move ourselves into position
    new_node.set_right(node)

    return new_node

one = Node(item=1)
two = Node(item=2)
three = Node(item=3)
four = Node(item=4)
five = Node(item=5)
six = Node(item=6)
seven = Node(item=7)

four.set_left(two)
four.set_right(six)
two.set_left(one)
two.set_right(three)
six.set_left(five)
six.set_right(seven)

# rotation should be invertable
original_repr = four.__repr__()
rotated = rotate_left(four)
rotate_back = rotate_right(rotated)
assert original_repr == rotate_back.__repr__()

# rotation should also work when there are parents and missing nodes
rotate_left(two)
rotate_right(three)
assert original_repr == four.__repr__()

# unbalance it all the way
rotate_left(two)
rotate_left(four)
rotate_left(four)
rotate_left(six)
assert seven.__repr__() == '<<<<<<<1>,2>,3>,4>,5>,6>,7>'

# test _insert()ion
root = Node(4)
root._insert(2)
root._insert(1)
root._insert(3)
assert root.__repr__() == '<<<1>,2,<3>>,4>'

root = Node(4)
root._insert(1)
root._insert(1)
root._insert(2)
root._insert(3)
assert root.__repr__() == '<<1,<1,<2,<3>>>>,4>', root.__repr__()

if __name__ == '__main__':
    tree = RedBlackTree()
    [tree.insert(i) for i in range(10)]
    tree.check()

    for _ in range(30):
        tree = RedBlackTree()
        [tree.insert(i) for i in random.sample(range(10), 10)]
        print(tree)
        tree.check()
