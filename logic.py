#!/usr/bin/env python3

import unittest
import functools
import itertools

'''
A substitution is a set of bindings for variables
Goals accept substitutions and return streams of substitutions
'''

'''
When you add a new type, it needs to be added to a few places:
    - unify, obviously!
    - the occurs check
    - walk star
    - reify
    - make sure equality works too!
Is there a way to write code which works for all of these at once?
'''

'''
Okay, I'm rewriting this to use generators.
A goal is a function which accepts a binding and emits a stream of bindings
Where a stream is a generator
'''

class ListMeta(type):
    '''
    A helper which lets us unify lists, we use a metaclass so we can do something like
    List[head:tail].
    '''
    def __getitem__(self, key):
        if not isinstance(key, slice):
            raise Exception('List expects to be used like: List[head:tail]')
        if key.start is None or key.stop is None or key.step is not None:
            raise Exception('List expects to be used like: List[head:tail]')
        return List(key.start, key.stop)

class List(metaclass=ListMeta):
    def __init__(self, head, tail):
        self.head = head
        self.tail = tail
    def __repr__(self):
        return 'List[{}:{}]'.format(self.head, self.tail)
    def __eq__(self, other):
        return (
            isinstance(other, List)
            and self.head == other.head and self.tail == other.tail
        )

class Var:
    # the actual bindings are kept elsewhere, this is just a placeholder
    pass

def vars(count):
    # make it convenient to make a few of these at once
    return [Var() for _ in range(count)]

empty_subs = dict()

def walk(subs, variable):
    '''find the value of this variable, it'll either be ground or an unbound variable'''
    result = variable
    while isinstance(result, Var) and result in subs:
        result = subs[result]
    return result

def occurs(subs, var, struct):
    '''Given a set of bindings, does var occur in struct? Prevent cycles from forming'''
    assert isinstance(var, Var)

    struct = walk(subs, struct) # first decide what struct is actually pointing at

    if isinstance(struct, Var):
        return struct == var
    if isinstance(struct, list):
        return any(occurs(subs, var, elem) for elem in struct)
    # TODO: this needs to also check List's!
    return False

def extend_subs(subs, key, value):
    if occurs(subs, key, value):
        return False
    result = subs.copy()
    result[key] = value
    return result

def unify(subs, left, right):
    '''
    Given a left and a right and a set of substitutions, return bindings where the given
    left and right are unified.
    '''
    if subs is False:
        return False
    left, right = walk(subs, left), walk(subs, right)

    if left == right:
        return subs
    if isinstance(left, Var):
        return extend_subs(subs, left, right)
    if isinstance(right, Var):
        return extend_subs(subs, right, left)
    if isinstance(left, list) and isinstance(right, list):
        # this doesn't support pairs of Head|Tail, add those too?
        if len(left) != len(right):
            return False
        for i in range(len(left)):
            subs = unify(subs, left[i], right[i])
        return subs
    if isinstance(left, List) and isinstance(right, list):
        subs = unify(subs, left.head, right[0])
        subs = unify(subs, left.tail, right[1:])
        return subs
    if isinstance(right, List) and isinstance(left, list):
        # I don't want to write the above code twice
        return unify(subs, right, left)
    if isinstance(left, List) and isinstance(right, List):
        subs = unify(subs, left.head, right.head)
        subs = unify(subs, left.tail, right.tail)
        return subs

    return False

def walkstar(subs, var):
    '''
    given some subs find the value of var, but also walk value and resolve any vars it
    contains. Will return either ground or a value containing unbound variables
    '''

    var = walk(subs, var)

    if isinstance(var, Var):
        return var
    if isinstance(var, list):
        return [walkstar(subs, elem) for elem in var]
    if isinstance(var, List):
        return List(walkstar(subs, var.head), walkstar(subs, var.tail))

    # this should mean it's an integer
    # TODO: decide the domain of variables and constrain them appropriately
    return var

def reify_subs(var, subs):
    '''
    Given a var and a list of substitutions, extends substitutions with var. If all the
    Vars in var have already been seen then nothing changes, but if there are any new vars
    they're given a name.
    '''

    var = walkstar(subs, var) # returns a value where all remaining Vars are unbound

    if isinstance(var, Var):
        name = '_{}'.format(len(subs))
        return extend_subs(subs, var, name)

    if isinstance(var, list):
        for elem in var:
            subs = reify_subs(elem, subs)
        return subs

    if isinstance(var, List):
        subs = reify_subs(var.head, subs)
        subs = reify_subs(var.tail, subs)

    # we're probably at an integer, so subs should remain unchanged
    return subs

def reify(subs, var):
    '''
    Given a set of substitutions, and a variable, returns a value where all Vars have
    been replaced by prettier names
    '''
    var = walkstar(subs, var)
    names = reify_subs(var, {})
    return walkstar(names, var)

'''
Okay, a goal returns a lambda which consumes some bindings and emits a stream of bindings

A stream can be either: None, a pair, or a thunk
'''

def always():
    def run(s):
        while True:
            yield s
    return run

def never():
    def run(s):
        return
        yield  # tell Python that this is a generator
    return run

def eq(left, right):
    def run(s):
        result = unify(s, left, right)
        if result is not False:
            yield result
        return
    return run

def disj(*goals):
    # only one of these must be true
    def run(s):
        # careful! This is DFS, ala Prolog. We'd probably prefer BFS, ala Kanren
        for goal in goals:
            stream = goal(s)
            yield from stream
    return run

def conj(*goals):
    # every goal must be true
    # say you manage to satisfy the first goal, you must also satisfy the rest with some
      # part of the resulting stream

    def emit(stream, subgoals):
        # there's nothing else to match against, this stream is the final one!
        if not subgoals:
            yield from stream
            return

        first, *rest = subgoals
        for binding in stream:
            substream = first(binding)
            yield from emit(substream, rest)

    def run(s):
        first, *rest = goals
        stream = first(s)

        # now, for every part of stream, try to satisfy the rest of the goals with it
        yield from emit(stream, rest)
    return run

# some list helpers

def head(head, l):
    # head is the first element of the list represented by l
    tail = Var()
    return eq(List[head:tail], l)

def tail(tail, l):
    head = Var()
    return eq(List[head:tail], l)

# try to build some relations!

def cons(h, t, l):
    # l is a list starting with head and continuing with tail ([] if no tail)
    return conj(
        head(h, l),
        tail(t, l)
    )

def null(var):
    return eq([], var)

def member(elem, l):
    # elem is a member of list if it's the head, or a member of the tail
    h, t = vars(2)
    # we have infinite recursion here, we can't build the entire tree until we need it
    return lambda: disj(
        conj(head(h, l), eq(elem, h)),
        conj(tail(t, l), member(elem, t))
    )

def append(head, tail, appended):
    return disj(
        conj(null(head), eq(tail, appended))  # an empty head means appended is tail

    )

# we have some basic goals, let's learn how to read their results:

def taken(n, stream):
    return list(itertools.islice(stream, n))

def run(n, goal, var):
    empty_subs = {}
    results = taken(n, goal(empty_subs))
    return [reify(result, var) for result in results]

# some quick tests

class TestCases(unittest.TestCase):
    def testWalk(self):
        x, y = vars(2)
        subs = {x: y, y: 10}
        self.assertTrue(walk(subs, x) == 10)

    def testOccurs(self):
        x, y = vars(2)
        self.assertFalse(occurs({}, x, 10))
        self.assertFalse(occurs({}, x, y))
        self.assertTrue(occurs({}, x, x))
        self.assertFalse(occurs({}, x, [y]))
        self.assertTrue(occurs({}, x, [x]))

    def testOccursPreventsCycles(self):
        x, y, z = vars(3)
        self.assertTrue(occurs({y: x}, x, y))
        self.assertTrue(occurs({y: z, z: x}, x, y))
        self.assertTrue(occurs({y: z, z: x}, x, [10, y, 5]))
        self.assertFalse(occurs({y: z, z: 5}, x, [10, y, 5]))

    def testExtendsRequiresVar(self):
        with self.assertRaises(AssertionError):
            extend_subs({}, 'hello', 'there')

    def testExtendsMakesCopy(self):
        x, subs = Var(), {}
        newsubs = extend_subs(subs, x, 'hello')
        self.assertFalse(x in subs)
        self.assertTrue(x in newsubs)

    def testWalkDoesNotFollowLists(self):
        x, y, z = vars(3)
        
        subs = extend_subs({}, x, [5, y])
        subs = extend_subs(subs, y, z)
        self.assertTrue(walk(subs, x) == [5, y])

    def testWalkStarDoesFollowLists(self):
        x, y, z = vars(3)
        
        subs = extend_subs({}, x, [5, y])
        subs = extend_subs(subs, y, z)
        self.assertTrue(walkstar(subs, x) == [5, z])

    def testReify(self):
        x, y = vars(2)

        self.assertEqual(reify({x: 10}, x), 10)
        self.assertEqual(reify({x: y}, x), '_0')
        self.assertEqual(reify({x: [y, 10], y: 5}, x), [5, 10])
        self.assertEqual(reify({}, [x, y]), ['_0', '_1'])

    def testUnify(self):
        x = Var()
        subs = unify(empty_subs, x, 10)
        self.assertTrue(subs[x] == 10)

        subs = unify(empty_subs, 10, x)
        self.assertTrue(subs[x] == 10)

        self.assertFalse(unify(empty_subs, 10, [x]))
        self.assertTrue(unify(empty_subs, 10, 10) == {})
        self.assertTrue(unify(empty_subs, [x], [x]) == {})

        self.assertFalse(unify(empty_subs, x, [x]))

        y = Var()
        self.assertTrue(unify(empty_subs, x, y), {x: y})

        self.assertTrue(unify(empty_subs, [x], [y]) == {x: y})

    def testComplexUnify(self):
        x, y, z = vars(3)

        subs = unify(empty_subs, [10, x, 5], [x, y, z])
        self.assertTrue(walk(subs, x) == 10)
        self.assertTrue(walk(subs, y) == 10)
        self.assertTrue(walk(subs, z) == 5)

    def testFailReassign(self):
        x = Var()

        self.assertFalse(unify({}, [10, x], [x, 5]))

        subs = unify({}, x, 5)
        self.assertFalse(unify(subs, 10, x))

    def testTakeDisj(self):
        x = Var()

        stream = disj(eq(x, 10), eq(x, 5))(empty_subs)
        results = taken(3, stream)

        self.assertTrue(len(results) == 2)
        first, second = results

        self.assertTrue(walk(first, x) == 10)
        self.assertTrue(walk(second, x) == 5)

    def testRun(self):
        x = Var()

        goal = eq(x, 10)
        self.assertEqual(run(1, goal, x), [10])
        self.assertEqual(run(2, goal, x), [10])

        goal = disj(eq(x, 10), eq(x, 5))
        self.assertEqual(run(3, goal, x), [10, 5])

        goal = conj(eq(x, 10), eq(x, 5))
        self.assertEqual(run(3, goal, x), [])

    def testNull(self):
        x = Var()

        goal = null(x)
        self.assertEqual(run(1, goal, x), [[]])

    def testListUnification(self):
        x, y, z = vars(3)

        goal = eq(List[x:y], [1, 2])
        self.assertEqual(run(1, goal, [x, y]), [[1, [2]]])

        goal = eq(List[x:y], [1])
        self.assertEqual(run(1, goal, [x, y]), [[1, []]])

        goal = eq([1, 2], List[x:y])
        self.assertEqual(run(1, goal, [x, y]), [[1, [2]]])

        goal = eq([1], List[x:y])
        self.assertEqual(run(1, goal, [x, y]), [[1, []]])

        # unify x with itself
        goal = eq([x], List[x:y])
        self.assertEqual(run(1, goal, [x, y]), [['_0', []]])

        # unify x with y (it must be empty!)
        goal = eq([x], List[y:x])
        self.assertEqual(run(1, goal, [x, y]), [[[], []]])

        # the right list has more elements than the left list
        goal = eq([x, y], List[1:[2, 3]])
        self.assertEqual(run(1, goal, [x, y]), [])

        # both lists are the same size
        goal = eq([x, y, z], List[1:[2, 3]])
        self.assertEqual(run(1, goal, [x, y, z]), [[1, 2, 3]])

    def testHeadandTail(self):
        h, t, l = vars(3)

        goal = head(h, l)
        self.assertEqual(run(1, goal, h), ['_0'])
        self.assertEqual(run(1, goal, l), [List['_0':'_1']])

        goal = tail(t, l)
        self.assertEqual(run(1, goal, t), ['_0'])
        self.assertEqual(run(1, goal, l), [List['_0':'_1']])

        goal = conj(
            tail(t, l),
            head(h, l),
            eq(l, [1, 2, 3])
        )
        self.assertEqual(run(1, goal, h), [1])
        self.assertEqual(run(1, goal, t), [[2, 3]])

    def testAlways(self):
        x = Var()

        goal = conj(eq(x, 10), always())
        self.assertEqual(run(3, goal, x), [10, 10, 10])

#    def testMember(self):
#        one = Var()

#        goal = member(one, [1, 2, 3])
#        self.assertEqual(run(5, goal, one), [1, 2, 3])

if __name__ == '__main__':
    unittest.main()
