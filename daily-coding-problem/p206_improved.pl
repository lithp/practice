/*
Problem statement:

A permutation can be specified by an array P, where P[i] represents the location of
the element at i in the permutation. For example, [2, 1, 0] represents the permutation
where elements at the index 0 and 2 are swapped.

Given an array and a permutation, apply the permutation to the array. For example,
given the array ["a", "b", "c"] and the permutation [2, 1, 0], return ["c", "b", "a"].
*/

% what we'd like to be able to do is generate a body like this and run it:
list_perm_list_ex(Left, [2, 1, 0], Right) :-
  nth0(0, Right, Elem0), nth0(2, Left, Elem0),
  nth0(1, Right, Elem1), nth0(1, Left, Elem1),
  nth0(2, Right, Elem2), nth0(0, Left, Elem2).

/*
This solution is, unfortunately, O(n^2).
we run N checks, and for every check our calls to nth0 take O(n) time, because Prolog
lists are linked lists.

Someone who was better at Prolog could probably write a O(n) solution by using either
compound terms and setarg/3 or dicts.

Here it is anyway:
*/

:- use_module(library(clpfd)). % this lets us write is_permutation/1.

list_perm_list(Left, Perm, Right) :-
  /* no matter which terms were instantiated we want to play with three partially
     instantiated lists of equal length */
  same_length(Left, Perm, Right),

  /* if Perm is a real list then verify that it specifies a permutation.
     if Perm is partially instantiated then constrain it so that it can only ever
       become a permutation.
     (permutation means no duplicates: [0, 0, 1] is not bijective and therefore
      not a permutation).
  */
  is_permutation(Perm),

  maplist(
    {Left}/[PermMember, RightMember]>>nth0(PermMember, Left, RightMember),
    Perm, Right
  ).

same_length([], [], []).
same_length([_|First], [_|Second], [_|Third]) :-
  same_length(First, Second, Third).

is_permutation(List) :-
  length(List, Length),
  MaxLen #= Length - 1,
  List ins 0..MaxLen, % the elements of List are integers in range(len(List)-1)
  all_distinct(List).

check_perm(_Perm, _Left, _Right).

:- begin_tests(p206).

% something I don't like about Prolog is how, even if you're writing a simple function,
% you ned to write a lot of test cases, there are so many different ways your function
% can be called!

test(example) :- list_perm_list([a, b, c], [2, 1, 0], [c, b, a]).

test(backwards, true(X == [a, b, c])) :-
  % use true to ensure there's only one solution and we don't leave a choicepoint behind
  list_perm_list(X, [1, 2, 0], [b, c, a]).

test(find_permutation, all(Perm == [[2, 1, 0]])) :-
  % we're allowed to leave a choicepoint here because there genuinely might be more
  % solutions!
  list_perm_list([a, b, c], Perm, [c, b, a]).

test(find_multi_permutation, all(Perm == [[0, 1, 2], [2, 1, 0]])) :-
  list_perm_list([a, b, a], Perm, [a, b, a]).

test(fail_to_find_perm, [fail]) :-
  % make sure we don't loop forever searching for solutions
  list_perm_list([a, b, c], _Perm, [a, b, a]).

test(fail_invalid_perm, [fail]) :-
  list_perm_list(_, [1, 2, 1], _).

test(both_at_once, all([X, Perm] == [[a, [0, 1, 2]], [a, [2, 1, 0]]])) :-
  list_perm_list([a, b, X], Perm, [a, b, a]).

test(generate_perms, all(perm_result(Perm, Result) == [
    perm_result([0, 1, 2], [a, b, c]),
    perm_result([0, 2, 1], [a, c, b]),
    perm_result([1, 0, 2], [b, a, c]),
    perm_result([1, 2, 0], [b, c, a]),
    perm_result([2, 0, 1], [c, a, b]),
    perm_result([2, 1, 0], [c, b, a])
    ])) :-
  list_perm_list([a, b, c], Perm, Result).

test(generate_left_right, true(soln(Left, Right) = soln([a, b, c], [a, c, b]))) :-
  list_perm_list(Left, [0, 2, 1], Right).

test(most_general_query, true(Result = [
    soln([], [], []),
    soln([a], [0], [a]),
    soln([a, b], [0, 1], [a, b]),
    soln([a, b], [1, 0], [b, a]),
    soln([a, b, c], [0, 1, 2], [a, b, c]),
    soln([a, b, c], [0, 2, 1], [a, c, b]),
    soln([a, b, c], [1, 0, 2], [b, a, c])
    % etc.
  ])) :-
  % we can even generate every possible answer(!) to list_perm_list
  once(findnsols(7, soln(Left, Perm, Right), list_perm_list(Left, Perm, Right), Result)).

:- end_tests(p206).
