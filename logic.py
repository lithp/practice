#!/usr/bin/env python3

from collections import defaultdict
import unittest
import functools
import itertools
from inspect import signature
import queue

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

TODO:
- Add dif/2 reification, right now they're hidden
- Is there a way to add hooks so you can add constraints which are written in-domain?
  - It'd be cool if you didn't need to call out to Python to write a constraint
- How inefficient is this, really? Are there any obvious performance/memory wins?
- How could you integrate this with real python objects for use in real programs?
- What does support for SLG (tabling) require?

Goals + Streams:
- currently, when you build goals they're immediately called and turned into a tree of
  generators we can pull from. This isn't very conducive for tracing support!
  - Maybe we could pass provenance? Some generator is member.disj.conj.head.eq?
  - Python is strict, so this would require some kind of special trick
  - A @goal decorator which takes the result and marks it with a special variable before
    returning it? This could also prevent you from needing lambda: during recursion?
- Tracing might be made easier by embedding special goals?
'''

class Tracer:
    def __init__(self):
        self.queue = queue.Queue()  # we don't really need thread safety but here it is

    def event(self, *event):
        self.queue.put(event)

    def events(self):
        items = []
        try:
            while True:
                items.append(self.queue.get_nowait())
        except queue.Empty:
            return items

    def wrap_goal(self, stream):
        first_time = True
        self.event(stream.__name__, 'CALL')
        try:
            while True:
                result = next(stream)
                if first_time:
                    first_time = False
                else:
                    self.event(stream.__name__, 'REDO')
                yield result
        except StopIteration:
            self.event(stream.__name__, 'FAIL')

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

    def __init__(self, subs=None, constraints=None, tracer=None):
        self.subs = subs if subs is not None else dict()
        self.constraints = constraints if constraints is not None else list()
        self.tracer = tracer if tracer is not None else Tracer()

    def ext_subs(self, key, value):
        if occurs(self.subs, key, value):
            return False
        newsubs = self.subs.copy()
        newsubs[key] = value
        return State(newsubs, self.constraints, self.tracer)

    def ext_constraints(self, constraint):
        newc = self.constraints.copy()
        newc.append(constraint)
        return State(self.subs, newc, self.tracer)

    def trace(self, *args):
        args = reify(self.subs, args)
        self.tracer.event(*args)

    def __eq__(self, other):
        if not isinstance(other, State):
            return False
        return self.subs == other.subs and self.constraints == other.constraints

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

    This copies State for every single change. It might be more efficient to return a list
    of changes which should be made? This would also make dif/2 more efficient.
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
    if isinstance(var, tuple):
        return (*(walkstar(subs, elem) for elem in var),)

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

    if isinstance(var, tuple):
        for elem in var:
            subs = reify_subs(elem, subs)
        return subs

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

# some decorators

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
    def wrapper(*args, **kwargs):
        def run(s):
            if '_s' in signature(func).parameters:
                kwargs['_s'] = s
            return func(*args, **kwargs)
        run.__name__ = func.__name__
        return run
    return wrapper

def semidet(func):
    'Takes a function which returns a State or None and wraps it in a generator'
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        result = func(*args, **kwargs)
        if result:
            yield result
        return
    return wrapper

# some goals

@raw_goal
def always(_s):
    while True:
        yield _s

@raw_goal
def never():
    return
    yield  # tell Python that this is a generator

@raw_goal
@semidet
def eq(left, right, _s):
    result = unify(_s, left, right)
    if result is False:
        _s.trace('eq', 'NOT-UNIFIABLE', left, right)
        return

    # if nothing has changed there's no need to run the constraints
    if result == _s:
        _s.trace('eq', 'NOCHANGE', left, right)
        return result

    result = run_constraints(result)

    if result is not None:
        _s.trace('eq', 'SUCCESS', left, right)
        return result

def run_constraints(state):
    '''
    does a single-pass down all the constraints, assumes that a single pass is enough
    to come up with a fixpoint

    TODO: accept a set of variables which have changed and only consider relevant
    constraints

    It might be convenient here to have some kind of StateDelta which goals return, you
    could use that to easily tell what the new constraints are and add them at the end
    '''
    result = state
    for constraint in state.constraints:
        func = constraint[0]
        args = constraint[1:]

        # if the constraint wants to remain around it must re-add itself
        result.constraints.remove(constraint)  # relies on proper constraint equality

        goal = func(*args)
        stream = call_goal(goal, result)
        try:
            result = next(stream)
        except StopIteration:
            return None
    return result

def call_goal(goal, state):
    'A hack to allow recursion. Sometimes the goals are wrapped in lambdas we must unpack'
    assert(callable(goal))

    sig = signature(goal)
    if len(sig.parameters) == 0:
        goal = goal()

    sig = signature(goal)
    assert(len(sig.parameters) == 1)

    # trace execution of this goal
    stream = goal(state)
    stream.__name__ = goal.__name__
    return state.tracer.wrap_goal(stream)

@raw_goal
def disj(*goals, _s):
    # TODO: I think it'd be cool if we kept a flag in State which specified which
    # resolution order should be used. Then you could add goals, bfs/0, dfs/0, which
    # changed the resolution order for all subgoals. disj/* could read that flag when
    # determining what to do.

    # disjunction, provable if any of the goals are provable
    # careful! This is DFS, ala Prolog. We'd probably prefer BFS, ala Kanren
    for goal in goals:
        # this logic is duplicated by @pattern/MultiGoal, if you change this
        # then that should also change
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

def conde(*options):
    '''
    conde(
      (goal1, goal2),
      (goal3, goal3)
    ) -> disj(
      conj(goal1, goal2),
      conj(coal3, goal4)
    )
    '''
    return disj(*(
        conj(*goals) for goals in options
    ))

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

def append(front, back, appended):
    '''
    append([], X, X).
    append([FHead|FRest], Other, [FHead|ARest]) :-
      append(FRest, Other, ARest).

    Pattern matching is pretty nice, isn't it?
    '''
    front_head, front_rest, appended_rest = vars(3)
    return conde(
        (null(front), eq(back, appended)),
        (
            cons(front_head, front_rest, front),
            lambda: append(front_rest, back, appended_rest),
            cons(front_head, appended_rest, appended)
        )
    )

class key_defaultdict(defaultdict):
    def __missing__(self, key):
        if self.default_factory is None:
            raise KeyError(key)
        result = self[key] = self.default_factory(key)
        return result

class MultiGoal:
    goals = key_defaultdict(lambda name: MultiGoal(name))

    def __init__(self, name):
        self.name = name  # the name of the function we're wrapping
        self.signatures = list()
    def __call__(self, *args):
        '''
        This call happens when you call something like member(x, [1, 2, 3]), we're passed
        some arguments and asked to return a goal (a function :: state -> [state])

        We have a couple potential goals though! And we won't know which one matches until
        we can look at state. So, defer that decision for now. Just return a wrapper which
        figures out which goal matches and delegates to it
        '''
        def run(s):
            funcs = MultiGoal.find_funcs(s, args, self.signatures)
            if not funcs:
                return
            for func, state in funcs:
                # TODO: this duplicates logic!
                # when disj changes this also needs to change
                goal = func(*args)
                stream = call_goal(goal, state)
                yield from stream

        run.__name__ = self.name
        return run

    def register(self, func, args):
        # TODO: maybe we could throw an error here if you provide overlapping definitions?
        self.signatures.append((args, func))

    @staticmethod
    def find_funcs(state, args, signatures):
        '''
        We have:
        - a state
        - some arguments we were passed to construct our goal
        - some signatures of goals we could delegate to

        We want to reify our arguments against the state and return all matching functions
        '''
        args = list(args)  # TODO: tell unify about tuples?
        for sig, func in signatures:
            sig = MultiGoal.preprocess_signature(sig)
            newstate = unify(state, args, sig)
            if newstate:
                yield func, newstate

    @staticmethod
    def preprocess_signature(sig):
        result = []
        for item in sig:
            if item == Var:
                # in order for unification to work we should turn "Var" into real vars
                item = Var()
            result.append(item)
        return result

def pattern(*args):
    def register(func):
        multigoal = MultiGoal.goals[func.__name__]
        multigoal.register(func, args)
        return multigoal
    return register


'''
What about this syntax?

append = match({
    ([], var, var): True,
    (List[front_head:front_rest], back, List[front_head:appended_rest]):
        append(front_rest, back, appended_rest)
})

append = match(
    (([], var, var), True),
    ((List[front_head:front_rest], back, List[front_head:appended_rest]),
        append(front_rest, back, appended_rest))
)

append = match(
    (([], var, var),),
    ((List[front_head:front_rest], back, List[front_head:appended_rest]),
        append(front_rest, back, appended_rest))
)

What about a decorator which intercepts List[:] arguments and creates a goal
which deconstructs them?
- how does it know which bindings to use when deconstructing them?

@pattern([], Var, Var)
def mappend(empty, x, y):
    return eq(x, y)
@pattern(List, Var, List)
def mappend(front, back, appended):
    with List[front] as (ffirst, frest), List[appended] as (afirst, arest):
        return conj(eq(ffirst, afirst), lambda: mappend(frest, back, arest))

(For this, [] is empty list, [Var] is singleton, List is a complete cons-cell)
@pattern(List, Var, List)
def mappend(ffirst, frest, back, afirst, arest):
    return conj(eq(ffirst, afirst), lambda: mappend(frest, back, arest))

My idea is this, but python disallowed tuple unpacking and multiple arguments w/ the same
name:
@pattern(List, Var, List)
def mappend((first, front: list), back, (first, rest: list)):
    return mappend(front, back, rest)

The pythonic way:
@pattern(List[Var('first'):Var('front')], Var('back'), List[Var('first'):Var('rest')])
def mappend(front, back, rest):
    return mappend(front, back, rest)

@pattern(List[Var('first'):], Var, List[Var('first'):])
def mappend(lfirst: Var('first'), front, back, afirst: Var('first'), rest):
    pass
'''


# a goal which adds a constraint

@raw_goal
@semidet
def dif(left, right, _s):
    # TODO: I'm pretty sure I need to add a walk or walkstar somewhere in here?
    # I don't need to, but I think it'll make this more efficient (unify doesn't need to
    # do the full walk every time we check this constraint)

    if not unify(_s, left, right):
        _s.trace('dif', 'will-never-be-equal')
        return _s

    new_bindings = prefix(_s.subs, unify(_s, left, right).subs)
    if not len(new_bindings):
        # if there are no changes then these terms are already equal, we must fail!
        _s.trace('dif', 'terms-already-equal')
        return

    # new_bindings is the list of things which must never become true
    _s.trace('dif', 'deferring-constraint')
    return _s.ext_constraints((dif, left, right))

def prefix(oldsubs, newsubs):
    'Returns the set of new associations'
    return {
        key: value
        for key, value in newsubs.items()
        if key not in oldsubs
    }

# we have some basic goals, let's learn how to read their results:

def taken(n, stream):
    return list(itertools.islice(stream, n))

def run(n, var, *goals, state=None):
    empty = state if state else State()

    if len(goals) == 0:
        return []
    if len(goals) == 1:
        goal = goals[0]
    if len(goals) > 1:
        goal = conj(*goals)

    results = taken(n, goal(empty))
    return [reify(result.subs, var) for result in results]

# some quick tests

def extend_subs(subs, key, value):
    'Helper function for tests which dont care about the entire State'
    # this feels like a sign that I've done something wrong, maybe extend_subs should
    # be a method on Substitutions, a subclass of dict?
    return State(subs).ext_subs(key, value).subs

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
        self.assertEqual(run(1, x, goal), [10])
        self.assertEqual(run(2, x, goal), [10])

        goal = disj(eq(x, 10), eq(x, 5))
        self.assertEqual(run(3, x, goal), [10, 5])

        goal = conj(eq(x, 10), eq(x, 5))
        self.assertEqual(run(3, x, goal), [])

    def testNull(self):
        x = Var()

        goal = null(x)
        self.assertEqual(run(1, x, goal), [[]])

    def testListUnification(self):
        x, y, z = vars(3)

        goal = eq(List[x:y], [1, 2])
        self.assertEqual(run(1, [x, y], goal), [[1, [2]]])

        goal = eq(List[x:y], [1])
        self.assertEqual(run(1, [x, y], goal), [[1, []]])

        goal = eq([1, 2], List[x:y])
        self.assertEqual(run(1, [x, y], goal), [[1, [2]]])

        goal = eq([1], List[x:y])
        self.assertEqual(run(1, [x, y], goal), [[1, []]])

        # unify x with itself
        goal = eq([x], List[x:y])
        self.assertEqual(run(1, [x, y], goal), [['_0', []]])

        # unify x with y (it must be empty!)
        goal = eq([x], List[y:x])
        self.assertEqual(run(1, [x, y], goal), [[[], []]])

        # the right list has more elements than the left list
        goal = eq([x, y], List[1:[2, 3]])
        self.assertEqual(run(1, [x, y], goal), [])

        # both lists are the same size
        goal = eq([x, y, z], List[1:[2, 3]])
        self.assertEqual(run(1, [x, y, z], goal), [[1, 2, 3]])

    def testHeadandTail(self):
        h, t, l = vars(3)

        goal = head(h, l)
        self.assertEqual(run(1, h, goal), ['_0'])
        self.assertEqual(run(1, l, goal), [['_0', '_1']])

        goal = tail(t, l)
        self.assertEqual(run(1, t, goal), ['_0'])
        # this syntax is not ideal, I preferred: List['_0': '_1']
        # I can't think of something which is both computable and also makes it explicit
        # that this really means: [_0 | _1]
        self.assertEqual(run(1, l, goal), [['_0', '_1']])

        goal = conj(
            tail(t, l),
            head(h, l),
            eq(l, [1, 2, 3])
        )
        self.assertEqual(run(1, h, goal), [1])
        self.assertEqual(run(1, t, goal), [[2, 3]])

    def testAlways(self):
        x = Var()

        goal = conj(eq(x, 10), always())
        self.assertEqual(run(3, x, goal), [10, 10, 10])

    def testMember(self):
        one = Var()

        goal = member(one, [1, 2, 3])
        self.assertEqual(run(5, one, goal), [1, 2, 3])

        goal = member(1, one)
        self.assertEqual(run(5, one, goal), [
            [1, '_0'],
            ['_0', 1, '_1'],
            ['_0', '_1', 1, '_2'],
            ['_0', '_1', '_2', 1, '_3'],
            ['_0', '_1', '_2', '_3', 1, '_4'],
        ])

        goal = conj(member(one, [1, 2, 3]), member(one, [2, 3, 4]))
        self.assertEqual(run(5, one, goal), [2, 3])

    def testGoalWrapperWithS(self):

        @raw_goal
        @semidet
        def uni(left, right, _s):
            result = unify(_s, left, right)
            if result is not False:
                return result

        x, y = vars(2)

        self.assertEqual(
            run(1, x, uni(x, y)),
            ['_0']
        )

    def testPrefix(self):
        self.assertEqual(
            prefix({1: 1}, {1: 1}),
            {}
        )

        self.assertEqual(
            prefix({1: 1}, {1: 1, 2: 2}),
            {2: 2}
        )

        self.assertEqual(
            prefix({}, {1: 1, 2: 2}),
            {1: 1, 2: 2}
        )

    def testDifAddsConstraint(self):
        x, y = vars(2)
        state = State()

        gen = dif(x, y)(state)
        state = taken(1, gen)[0]
        constraint = state.constraints[0]

        self.assertEqual(len(constraint), 3)
        self.assertEqual(constraint[0], dif)

    def testDifFailsIfAlreadyEqual(self):
        x, y = vars(2)

        self.assertEqual(
            run(1, x, eq(x, y), dif(x, y)),
            []
        )

        self.assertEqual(
            run(1, x, eq(x, 10), dif(10, x)),
            []
        )

    def testDifFailsWhenBecomeEqual(self):
        x, y = vars(2)
        state = State()

        self.assertEqual(
            run(1, x, dif(x, y), eq(x, y), state=state), []
        )

        self.assertEqual(
            run(1, x, dif(x, y), eq(x, 10), eq(y, 10)),
            []
        )

        self.assertEqual(
            run(1, x, dif(x, y), eq(x, 10), eq(y, 9)),
            [10]
        )

    def testDifSticksAroundWhenNecessary(self):
        x, y = vars(2)

        self.assertEqual(
            # when you run an unrelated goal the constraints are checked
            # make sure the constraint re-adds itself so it can fire later
            run(1, x, dif(x, 10), eq(y, 4), eq(x, 10)),
            []
        )

        self.assertEqual(
            # dif() should notice that the second goal doesn't sasitfy it and stick
            # around to fail the third goal
            run(1, x, dif(x, y), eq(y, 4), eq(x, 4)),
            []
        )

    def testTracing(self):
        # should probably rip this out, not sure it adds much value
        x = Var()
        state = State()

        self.assertEqual(
            run(1, x, eq(x, 10), eq(x, 5), state=state),
            []
        )

        self.assertEqual(
            state.tracer.events(),
            [('eq', 'CALL'),
             ('eq', 'SUCCESS', '_0', 10),
             ('eq', 'CALL'),
             ('eq', 'NOT-UNIFIABLE', 10, 5),
             ('eq', 'FAIL'),
             ('eq', 'FAIL')]
        )

    def testAppend(self):
        left, right, appended = vars(3)

        self.assertEqual(
            run(2, left, append([], [1, 2, 3], [1, 2, 3])),
            ['_0']
        )

        self.assertEqual(
            run(2, appended, append([], [1, 2, 3], appended)),
            [[1, 2, 3]]
        )

        self.assertEqual(
            run(2, appended, append([1], [2, 3], appended)),
            [[1, 2, 3]]
        )

        self.assertEqual(
            run(2, right, append([1], right, [1, 2, 3])),
            [[2, 3]]
        )

        self.assertEqual(
            run(2, right, append([1, 2, 3], right, [1, 2, 3])),
            [[]]
        )

        # TODO: asking for 2 results gets us into an infinite loop...
        self.assertEqual(
            run(1, left, append(left, [1, 2, 3], [1, 2, 3])),
            [[]]
        )

        # TODO: asking for 5 results gets us into an infinite loop...
        self.assertEqual(
            run(4, right, append(left, right, [1, 2, 3])),
            [
                [1, 2, 3], [2, 3], [3], []
            ]
        )

        self.assertEqual(
            run(5, left, append(left, right, appended)),
            [
                [], ['_0'], ['_0', '_1'], ['_0', '_1', '_2'], ['_0', '_1', '_2', '_3']
            ]
        )

        self.assertEqual(
            run(5, right, append(left, right, appended)),
            ['_0']*5
        )

    def testConde(self):
        x, y = vars(2)

        def either():
            return conde(
                (eq(x, 5), eq(x, 5)),
                (eq(x, 5), eq(x, 10)),
                (eq(x, y), eq(y, 4))
            )

        self.assertEqual(
            run(2, x, either()),
            [5, 4]
        )

    def testFacts(self):
        # a hacky and slow way of adding data:
        # could you add a way which:
        # - had better syntax
        # - indexed things better so the right option was quickly chosen?
        def child_of(child, parent):
            return conde(
                (eq(child, 'bob'), eq(parent, 'alice')),
                (eq(child, 'bob'), eq(parent, 'drew'))
            )

        x, y = vars(2)
        self.assertEqual(
            run(2, x, child_of(x, 'alice')),
            ['bob']
        )

    def testPatternAgainstEmptyList(self):
        '''
        We can match a constant against an empty list
        '''

        @pattern([Var], Var)
        def length(l, size):
            return eq(size, 1)

        @pattern([], Var)
        def length(l, size):
            # todo: should we drop constants like [] when passing in args?
            return eq(size, 0)

        y = Var()
        self.assertEqual(
            run(1, y, length([], y)),
            [0]
        )

        # this should also work when the thing we're unifying against is a Var
        empty = Var()
        self.assertEqual(
            run(1, y, eq(empty, []), length(empty, y)),
            [0]
        )

    def testPatternActsAsDisj(self):
        '''
        If there are multiple matching patterns, we should return both answers
        '''

        @pattern([Var], Var)
        def length(l, size):
            return eq(size, 1)

        @pattern([], Var)
        def length(l, size):
            return eq(size, 0)

        x, y = vars(2)
        self.assertEqual(
            run(2, y, length(x, y)),
            [1, 0]
        )

    def testPattern(self):
        @pattern([], 'x', 'x')
        def mappend():
            return True

        @pattern(['first', 'rest'], 'back', ['first', 'appended'])
        def mappend(rest, back, appended):
            return mappend(rest, back, appended)

        mappend('hi')

if __name__ == '__main__':
    unittest.main()
