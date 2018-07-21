import unittest

from logic import (
    raw_goal, semidet, Var, vars, run, conde, cons, eq, State
)

# a goal which adds some constraints
@raw_goal
@semidet
def leq(left, right, _s):
    # first determine where each argument is pointing
    left = _s.walk(left)
    right = _s.walk(right)

    # this goal only allows integers
    # TODO: test this, how does this framework handle exceptions?
    # how could we create reasonable stack traces?
    if type(left) not in (Var, int):
        raise Exception('left must be an integer: {}'.format(left))
    if type(right) not in (Var, int):
        raise Exception('right must be an integer: {}'.format(right))

    if isinstance(left, int) and isinstance(right, int):
        if left <= right:
            _s.trace('leq', 'COMPARE', 'success', left, right)
            return _s
        _s.trace('leq', 'COMPARE', 'failure', left, right)
        return

    # one of the arguments is uninstantiated so defer this constraint for later
    _s.trace('leq', 'deferring-constraint', left, right)
    return _s.ext_constraints((leq, left, right))

def select(elem, lis, rest):
    '''
    elem is an element of lis and rest is a list with every other element of lis

    select(Elem, [Elem|Rest], Rest).
    select(Elem, [Head|More], [Head|Remaining]) :-
        select(Elem, More, Remaining).
    '''
    head, more, remaining = vars(3)
    return conde(
        (cons(elem, rest, lis),),
        (
            cons(head, more, lis),
            cons(head, remaining, rest),
            lambda: select(elem, more, remaining)
        )
    )

def permutation(lis, perm):
    '''
    permutation([], []).
    permutation(List, [First|PermRest]) :-
      select(First, List, Rest),
      permutation(Rest, PermRest).
    '''
    first, rest, permRest = vars(3)
    return conde(
      (eq(lis, []), eq(perm, [])),
      (
          cons(first, permRest, perm),
          select(first, lis, rest),
          lambda: permutation(rest, permRest)
      )
    )

def sorted(lis):
    '''
    sorted([X]).
    sorted([First, Second|Rest]) :-
      First =< Second,
      sorted([Second|Rest]).
    '''
    first, second, rest1, rest2 = vars(4)
    return conde(
        (cons(first, [], lis),), # lis only has one element... it's sorted!
        (
            cons(first, rest1, lis),
            cons(second, rest2, rest1),
            leq(first, second),
            lambda: sorted(rest1)
        )
    )

class TestCases(unittest.TestCase):
    def testLeq(self):
        left, right, x = vars(3)

        # if both are instantiated checks for less-or-equal
        self.assertEqual([5], run(1, x, leq(4, 5), eq(x, 5)))
        self.assertEqual([], run(1, x, leq(6, 5), eq(x, 5)))

        # defers the check if just one is instantiated
        self.assertEqual([5], run(1, left, leq(left, 5), eq(left, 5)))
        self.assertEqual([], run(1, left, leq(left, 5), eq(left, 6)))

        # defers the check when both uninstantiated
        self.assertEqual([6], run(1, left, leq(left, right), eq(left, 6), eq(right, 8)))
        self.assertEqual([], run(1, left, leq(left, right), eq(left, 8), eq(right, 6)))

    def testSelect(self):
        elem, lis, rest = vars(3)

        self.assertEqual(
            [1, 2, 3],
            run(5, elem, select(elem, [1, 2, 3], rest))
        )

        self.assertEqual(
            [[2, 3], [1, 3], [1, 2]],
            run(5, rest, select(elem, [1, 2, 3], rest))
        )

        self.assertEqual(
            [[1, 2, 3], [2, 1, 3], [2, 3, 1]],
            run(5, lis, select(1, lis, [2, 3]))
        )

    def testPermutation(self):
        perm = Var()

        self.assertEqual(
            [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]],
            run(10, perm, permutation([1, 2, 3], perm))
        )

    def testSorted(self):
        x = Var()

        # single element lists are sorted
        self.assertEqual(['_0'], run(1, x, sorted([2])))
        self.assertEqual(['_0'], run(1, x, sorted([x])))

        # fails when the input list is not sorted
        self.assertEqual([], run(1, x, sorted([2, 1])))
        self.assertEqual([], run(1, x, sorted([1, 3, 2])))
        self.assertEqual([], run(1, x, sorted([1, 2, 4, 3])))

        # succeeds when it is!
        self.assertEqual(['_0'], run(1, x, sorted([1, 2])))
        self.assertEqual(['_0'], run(1, x, sorted([1, 2, 3])))
        self.assertEqual(['_0'], run(1, x, sorted([1, 2, 3, 4])))
        self.assertEqual(['_0'], run(1, x, sorted([1, x, 3, 4])))

        # here's a bug, it doesn't propogate constraints to realize this is impossible:
        # x cannot be both larger or equal to five, and less than or equal to 3
        self.assertEqual(['_0'], run(1, x, sorted([5, x, 3, 4])))

        # the right thing happens if you try to assign to x
        self.assertEqual([2], run(1, x, sorted([1, x, 3, 4]), eq(x, 2)))

        # sorted adds a constraint to variables it sees
        self.assertEqual([], run(1, x, sorted([3, x]), eq(x, 2)))
        self.assertEqual([4], run(1, x, sorted([3, x]), eq(x, 4)))

        y, z = vars(2)
        self.assertEqual([], run(1, x, sorted([x, y, z]), eq(x, 2), eq(y, 3), eq(z, 1)))
        self.assertEqual([2], run(1, x, sorted([x, y, z]), eq(x, 2), eq(y, 3), eq(z, 4)))
        self.assertEqual([], run(1, x, sorted([x, y, z]), eq(x, 2), eq(z, 4), eq(y, 5)))

        # a real bug, this definitely shouldn't happen (it should fail):
        # it seems we drop the constraints somewhere!
        # I think it's because we keep making new Var's, but the constraints are on
        # the old Vars
        # that doesn't seem to be it, the constraints are deferred but never show up
        # in the state, maybe we backtrack outselves out of it? we have bad logic?
        state = State()
        self.assertEqual(
            [],
            run(1, x, sorted([3, x, 3, 4]), eq(x, 2), state=state, trace=True)
        )

#        for c in state.constraints:
#            print(c)

if __name__ == '__main__':
    unittest.main()
