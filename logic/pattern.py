#!/usr/bin/env python3

from collections import defaultdict
import unittest

from logic import Var, vars, run, unify, eq, call_goal, List

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
            funcs = self.find_funcs(s, args)
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
        self.signatures.append((args, func))

    def find_funcs(self, state, args):
        '''
        We have:
        - a state
        - some arguments we were passed to construct our goal
        - some signatures of goals we could delegate to

        We want to reify our arguments against the state and return all matching functions
        '''
        returned_any = False
        args = list(args)  # TODO: tell unify about tuples?
        for sig, func in self.signatures:
            sig = MultiGoal.preprocess_signature(sig)
            newstate = unify(state, args, sig)
            if newstate:
                state.trace(self.name, 'match', args, sig)
                yield func, newstate
                returned_any = True
        if not returned_any:
            state.trace(self.name, 'no-match', args)

    @staticmethod
    def preprocess_signature(sig):
        result = []
        for item in sig:
            if item == Var:
                # in order for unification to work we should turn "Var" into real vars
                item = Var()
            result.append(item)
        return result

    @staticmethod
    def empty():
        MultiGoal.goals = key_defaultdict(lambda name: MultiGoal(name))

def pattern(*args):
    def register(func):
        multigoal = MultiGoal.goals[func.__name__]
        multigoal.register(func, args)
        return multigoal
    return register

class TestCases(unittest.TestCase):
    def testPatternAgainstEmptyList(self):
        '''
        We can match a constant against an empty list
        '''
        MultiGoal.empty()

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
        'If there are multiple matching patterns, we should return both answers'
        MultiGoal.empty()

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

    def testPatternUnpacksLists(self):
        'Make sure unification is working as expected'
        MultiGoal.empty()

        @pattern([10], Var)
        def length(l, size):
            return eq(size, 1)
        @pattern(List[1:2], Var)
        def length(l, size):
            return eq(size, 2)

        l, size = vars(2)
        self.assertEqual(
            run(2, [l, size], length(l, size)),
            [
                [[10], 1],
                [[1, 2], 2]
            ]
        )

        self.assertEqual(
            [2],
            run(1, size, length(List[1:2], size)),
        )

        self.assertEqual(
            [],
            run(1, size, length([1, 2], size)),
        )

        @pattern(List[1:List[2:[]]], Var)
        def length(l, size):
            return eq(size, 2)

        self.assertEqual(
            [2],
            run(1, size, length([1, 2], size)),
        )

    def testPatternTurnsStringsIntoVars(self):
        '''
        If you want to say things like "these two things must be equal" then you need to
        be able to name your Vars
        '''

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
