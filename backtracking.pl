% play around with backtracking, do non-logical things

/*
This predicate returns each result in the chain of calling Goal over and over again:
  Goal(N0, N1),
  Goal(N1, N2),
  Goal(N2, N3),
  ...
*/
iterate(Goal, N0, N) :-
  call(Goal, N0, N1),
  ( N = N1;
    iterate(Goal, N1, N)).

/*
Now, I want to implement "dropn", which ignores the first n successes of Goal, then
succeeds with all the rest of them.

This is extra-logical because it relies on the solution ordering and is
therefore extremely bad style. Let's do it anyway.
*/

dropn1(N, Template, Goal, Result) :-
  /* I'm cheating here by using a built-in and it doesn't do what we want
     anyway, it onlyreturns the second success */
  succ(N, N1),
  findnsols(N1, Template, Goal, Sols), !,
  last(Sols, Result).

/*
the next method is even uglier:
*/

dropn2(N, Goal) :-
  must_be(nonneg, N),
  Counter = counter(0),
  call(Goal),
  ( arg(1, Counter, N) % start succeeding, we've hit N
  ; arg(1, Counter, Count),
    Count < N, % guard against backtracking
    NewCount is Count + 1,
    nb_setarg(1, Counter, NewCount),
    fail % backtrack to `call` and handle the next solution
  ).

/*
the above isn't very satisfying. 

it's very imperative and fights Prolog in order to get the desired control
flow, the control flow is therefore pretty difficult to understand.

I'd must prefer to be able to somehow pass a continuation around. Luckily,
engines let us do exactly this!
*/

dropn3(N, Template, Goal, Result) :-
  /* there's no need to call engine_destroy because we always consume every
     result, it destroys itself! */
  engine_create(Template, Goal, Engine),
  nth_result(Engine, Result, Nth),
  Nth >= N.

nth_result(Engine, Result, N) :-
  nth_result(0, Engine, Result, N).

nth_result(CurrentDepth, Engine, Result, Nth) :-
  engine_next(Engine, Ans),
  ( Result = Ans, Nth = CurrentDepth
  ; NextDepth is CurrentDepth + 1, nth_result(NextDepth, Engine, Result, Nth)).

/* it's annoying how much overhead the above has, but I find it pretty! */

% you can also drop all results until an arbitrary condition is hit:

dropuntil(Template, Condition, Goal, Result) :-
  /* ignore every success of Goal until it causes Condition to succeed, then return
     every success */
  engine_create(Template, Goal, Engine),
  dropuntil_s(Engine, Condition, Result).

dropuntil_s(Engine, Condition, Result) :-
  engine_next(Engine, Answer),
  ( call(Condition, Answer), !, (Result = Answer; return_rest(Engine, Result))
  ; dropuntil_s(Engine, Condition, Result)).

return_rest(Engine, Result) :-
  engine_next(Engine, Ans),
  ( Result = Ans
  ; return_rest(Engine, Result)).

:- begin_tests(dropuntil).

test(example_usage, all(Y = [3, 4, 5])) :-
  % drop all results until X is 3, then succeed with all values of X
  dropuntil(X, '='(3), member(X, [1, 2, 3, 4, 5]), Y).

:- end_tests(dropuntil).
