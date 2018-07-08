#!/usr/bin/env python3

import unittest
import functools
import itertools
from inspect import signature

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

TODO:
    Add an event log, so we can return an execution trace?
    How would you create an interactive debugger?
    Create a decorator which makes goals easier to write?
    I like logpy's idea of returning a tuple to represent goal lambdas
      I think a decorator which wraps goals would be even simpler?

Constraints (http://scheme2011.ucombinator.org/papers/Alvis2011.pdf)
    - where there was previously an asociation store, there's now:
      - a domain store
      - a constraint store (careful that all constraints have at least one variable)
    - a constraint is (op, *args), where op is the name of the function to call
    - a domain is a list of natural numbers

    cKanren relies on 3 functions to be available:
    - process-prefix:      called when a unification happens, updates constraints?
    - enforce-constraints: runs before reification, checks the constraint store
    - reify-constraints:   pretty-print the constraint store

    - goal-construct takes a goal and succeeds if constraints successfully apply?

    - when we unify, if we fail or fail to update the store then nothing changes
      - if we update the store then we call (process-prefix) with the association delta
        (and return the store that process-prefix returns)

    - run-constraints is a function which re-runs every constraint until fixpoint
      (you should call it when implementing process-prefix for your constraint system)
      - that's too slow, so it's passed a list of relevant vars,
        and only runs the constraints which involve those vars

      - a constraint is a function which takes the current state and returns the next
        state

    Finite Domain
    - process-prefix is called when new associations are made and runs on each new one
      - if the new association is to a value:
        - if that value is a Var, then intersect the domains
          - if the domains are disjoint, fail the unification!
          - if the intersection is a singleton, add it to the substitution
            - this triggers run-constraints on the Var we just assigned to
        - if that value is a constant in the domain, nice!
        - if that value is a constant outside the domain, fail the unification
      - it then calls run-constraints on the new store

    - enforce-constraints
      - if we're reifying then we'd prefer to associate our variable with a value, if
        that's possible (the domain is a singleton), now is the time to do it!
      - we should also make sure that there exists a solution before reifying, try to
        force an answer, if that fails then fail reification!
        (somehow this is specific to the finite domain?)

    Disequality (no domain information is stored, just constraints)
    - process-prefix just runs the constraints on all new associations
    - enforce-constraints does nothing, constraints already fail immediately if they're
      unsatisfiable
    - reify-constraints returns the list of constraints attached to the specified variable

    - neq is a new goal which takes a left and a right
      - if left and right are not unifiable then this will never be violated, so no-op
      - if left and right are unifiable
        - p is the set of associations which will change when they're unified
        - if p is empty then your two things are already equal, fail!
        - okay, p is the set of things which should never become true
          - add it to the constraint store!
          - the extra constraint might cause redundency
            - subsume means: unifying the smaller one with the bigger one causes no change
          - after adding, drop any subsumed constraints, you don't need them!

    Misc:
    - unify(pairs, subs) takes a list of new pairs to add and adds them all at once!
    - test => (\(s) body) means only run the body if (test) succeeds
      (and run it with the result of (test)
    - cKanren doesn't support simultanious types of constraints. To do that you need to
      write your own composite constraint functions

Notes:
- if you had added type annotations would it have been easier to migrate from subs -> state?
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

class State:
    'Stores the current execution state'
    def __init__(self, subs=None):
        self.subs = subs if subs is not None else dict()

    def ext_subs(self, key, value):
        if occurs(self.subs, key, value):
            return False
        newsubs = self.subs.copy()
        newsubs[key] = value
        return State(newsubs)

    def __eq__(self, other):
        if not isinstance(other, State):
            return False
        return self.subs == other.subs

def extend_subs(subs, key, value):
    'Helper function for parts of the code which have not yet migrated'
    return State(subs).ext_subs(key, value).subs

empty = State()

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

def unify(state, left, right):
    '''
    Given a left and a right and a set of substitutions, return bindings where the given
    left and right are unified.
    '''
    if state is False:
        return False
    subs = state.subs
    left, right = walk(subs, left), walk(subs, right)

    if left == right:
        return state
    if isinstance(left, Var):
        return state.ext_subs(left, right)
    if isinstance(right, Var):
        return state.ext_subs(right, left)
    if isinstance(left, list) and isinstance(right, list):
        if len(left) != len(right):
            return False
        for i in range(len(left)):
            state = unify(state, left[i], right[i])
        return state
    if isinstance(left, List) and isinstance(right, list):
        if len(right) == 0:
            return False
        state = unify(state, left.head, right[0])
        state = unify(state, left.tail, right[1:])
        return state
    if isinstance(right, List) and isinstance(left, list):
        # I don't want to write the above code twice
        return unify(state, right, left)
    if isinstance(left, List) and isinstance(right, List):
        state = unify(state, left.head, right.head)
        state = unify(state, left.tail, right.tail)
        return state

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
        rest = walkstar(subs, var.tail)
        if isinstance(rest, list):
            return [walkstar(subs, var.head)] + rest
        return [walkstar(subs, var.head), rest]

        # this is what was returned before List was converted into lists on reification
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

def raw_goal(func):
    '''
    A goal is a function which takes:
        s, a dict of substitutions,
    And returns a generator which yields all the substitutions for which this goal passes

    raw_goal(func) makes it easier to write goal-returning functions
        (it's not meant to be called by users)
        it returns a wrapper which, when called with arguments, returns a goal which,
        when called with substitutions calls the body of func with an additional kwarg:
            _s <- the set of substitutions
        (but only if the goal accepts kwargs, if you don't care about s then it isn't passed)
    '''
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        def run(s):
            if '_s' in signature(func).parameters:
                kwargs['_s'] = s
            return func(*args, **kwargs)
        return run
    return wrapper

@raw_goal
def always(_s):
    while True:
        yield _s

@raw_goal
def never():
    return
    yield  # tell Python that this is a generator

@raw_goal
def eq(left, right, _s):
    result = unify(_s, left, right)
    if result is not False:
        yield result
    return

def call_goal(goal, state):
    'A hack to allow recursion. Sometimes the goals are wrapped in lambdas we must unpack'
    assert(callable(goal))

    sig = signature(goal)
    if len(sig.parameters) == 0:
        goal = goal()

    sig = signature(goal)
    assert(len(sig.parameters) == 1)

    return goal(state)

@raw_goal
def disj(*goals, _s):
    # disjunction, provable if any of the goals are provable
    # careful! This is DFS, ala Prolog. We'd probably prefer BFS, ala Kanren
    for goal in goals:
        stream = call_goal(goal, _s)
        yield from stream

@raw_goal
def conj(*goals, _s):
    # every goal must be true
    # say you manage to satisfy the first goal, you must also satisfy the rest with some
      # part of the resulting stream

    def emit(stream, subgoals):
        # there's nothing else to match against, this stream is the final one!
        if not subgoals:
            yield from stream
            return

        first, *rest = subgoals
        for state in stream:
            substream = call_goal(first, state)
            yield from emit(substream, rest)
            # TODO: all these yield from's lead to an insane stack depth
            # could we do something trampoline-like and just return the new generator?

    first, *rest = goals
    stream = call_goal(first, _s)

    # now, for every part of stream, try to satisfy the rest of the goals with it
    yield from emit(stream, rest)

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
    # add the lambda to prevent infinite recursion when building out goals
    # because Python is not lazy, the (huge!) tree of goals is built before we run
    return disj(
        conj(head(h, l), eq(elem, h)),
        conj(tail(t, l), lambda: member(elem, t))
    )

#def append(head, tail, appended):
#    return disj(
#        conj(null(head), eq(tail, appended))  # an empty head means appended is tail
#
#    )

# we have some basic goals, let's learn how to read their results:

def taken(n, stream):
    return list(itertools.islice(stream, n))

def run(n, goal, var):
    empty = State()
    results = taken(n, goal(empty))
    return [reify(result.subs, var) for result in results]

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
        state = unify(empty, x, 10)
        self.assertTrue(state.subs[x] == 10)

        state = unify(empty, 10, x)
        self.assertTrue(state.subs[x] == 10)

        self.assertFalse(unify(empty, 10, [x]))
        self.assertEqual(unify(empty, 10, 10), State())
        self.assertEqual(unify(empty, [x], [x]), State())

        self.assertFalse(unify(empty, x, [x]))

        y = Var()
        self.assertEqual(unify(empty, x, y), State({x: y}))

        self.assertEqual(unify(empty, [x], [y]), State({x: y}))

    def testComplexUnify(self):
        x, y, z = vars(3)

        state = unify(empty, [10, x, 5], [x, y, z])
        self.assertTrue(walk(state.subs, x) == 10)
        self.assertTrue(walk(state.subs, y) == 10)
        self.assertTrue(walk(state.subs, z) == 5)

    def testFailReassign(self):
        x = Var()

        self.assertFalse(unify(empty, [10, x], [x, 5]))

        subs = unify(empty, x, 5)
        self.assertFalse(unify(subs, 10, x))

    def testTakeDisj(self):
        x = Var()

        stream = disj(eq(x, 10), eq(x, 5))(empty)
        results = taken(3, stream)

        self.assertTrue(len(results) == 2)
        first, second = results

        self.assertTrue(walk(first.subs, x) == 10)
        self.assertTrue(walk(second.subs, x) == 5)

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
        self.assertEqual(run(1, goal, l), [['_0', '_1']])

        goal = tail(t, l)
        self.assertEqual(run(1, goal, t), ['_0'])
        # this syntax is not ideal, I preferred: List['_0': '_1']
        # I can't think of something which is both computable and also makes it explicit
        # that this really means: [_0 | _1]
        self.assertEqual(run(1, goal, l), [['_0', '_1']])

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

    def testMember(self):
        one = Var()

        goal = member(one, [1, 2, 3])
        self.assertEqual(run(5, goal, one), [1, 2, 3])

        goal = member(1, one)
        self.assertEqual(run(5, goal, one), [
            [1, '_0'],
            ['_0', 1, '_1'],
            ['_0', '_1', 1, '_2'],
            ['_0', '_1', '_2', 1, '_3'],
            ['_0', '_1', '_2', '_3', 1, '_4'],
        ])

    def testGoalWrapperWithS(self):

        @raw_goal
        def uni(left, right, _s):
            result = unify(_s, left, right)
            if result is not False:
                yield result

        x, y = vars(2)

        self.assertEqual(
            run(1, uni(x, y), x),
            ['_0']
        )

if __name__ == '__main__':
    unittest.main()
