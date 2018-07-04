:- use_module(library(random)).

/*
* In all of them performance is dominated by nth0
* fisher_yates_dl 20,000 elems: 11.22, 11.00, 11.02, 10.93, 11.00, 11.14
* fisher_yates_accum: 11.06, 11.03, 10.92, 10.86
* fisher_yates: 11.09, 11.08, 11.08, 11.19
* These are all O(N^2) because getting an element of a list takes linear time...
*/

% deterministically shuffles the array
fisher_yates([X], [X]) :- !.
fisher_yates(List, [Head|Rest]) :-
  random_select(Head, List, List1),
  fisher_yates(List1, Rest).

fisher_yates_forever(List, Shuffled) :-
  % a straightforward way to turn a det predicate into a nondet one
  repeat,
  fisher_yates(List, Shuffled).

% build up the result in an accumulator:

fisher_yates_accum(List, Shuffled) :-
  fisher_yates_accum(List, [], Shuffled).

fisher_yates_accum([], X, X) :- !. % copy the accumulator into the result
fisher_yates_accum(List, Shuffled, Result) :-
  random_select(Elem, List, List1),
  fisher_yates_accum(List1, [Elem|Shuffled], Result).

% build up the result as a difference list:

fisher_yates_dl(List, Shuffled) :-
  fisher_yates_dl(List, Accum-Accum, Shuffled).
fisher_yates_dl([], Accum-[], Accum) :- !.
fisher_yates_dl(List, Accum-Hole, Result) :-
  random_select(Elem, List, List1),
  Hole = [Elem|Hole1],
  fisher_yates_dl(List1, Accum-Hole1, Result).

% TODO: create one of these matrices?
% https://bost.ocks.org/mike/shuffle/compare.html

n_times(N, Goal, Result) :-
  N > 0,
  N1 is N - 1,
  call(Goal, Ans),
  ( Result = Ans
  ; n_times(N1, Goal, Result)).

% TODO: what would it take to support partially instantiated lists?
%   e.g. fisher_yates([1, 2, 3], [1, X, Y]).
%   a cheating answer is... it works great with fisher_yates_forever!
%    (assuming your partial list unifies with a shuffle...)

% this runs in: 0.04, 0.04, 0.03, 0.04 sec, also with 20k elements...
% a million elements takes 1.38s, and most of the time is spent in is/2 (!?).

fisher_yates_ct(List, Shuffled) :-
  Term =.. [items|List],
  length(List, Length),
  fisher_yates_ct(1, Length, Term, Shuffled).
fisher_yates_ct(Max, Max, Term, Result) :-
  Term =.. [items|Result], !.
fisher_yates_ct(N, Max, Term, Shuffled) :-
  N < Max,
  random_between(N, Max, Position),
  swap(Term, N, Position),
  N1 is N + 1,
  fisher_yates_ct(N1, Max, Term, Shuffled).

swap(Term, LeftPos, RightPos) :-
  arg(LeftPos, Term, Left),
  arg(RightPos, Term, Right),
  setarg(LeftPos, Term, Right),
  setarg(RightPos, Term, Left).
