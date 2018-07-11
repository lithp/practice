/*
Let's define a "sevenish" number to be one which is either a power of 7, or the sum of
unique powers of 7. The first few sevenish numbers are 1, 7, 8, 49, and so on. Create an
algorithm to find the nth sevenish number.
*/

:- use_module(library(clpfd)).

number_bitlist(_, 0, []).
number_bitlist(Base, Number, [Bit|Rest]) :-
  /* number is the decimal representation of the bitlist on the right (most significant
     bit first) */
  Number #> 0, % guard
  Bit #= Number mod Base,
  NewNumber #= Number div Base,
  number_bitlist(Base, NewNumber, Rest).

nth_sevenish(Nth, Sevenish) :-
  /* #=< is kind of a hack, it tells clpfd not to search forever if we can't find
     Sevenish, without it a query like nth_sevenish(X, 58) would search forever for
     possible Nth's */
  Nth #=< Sevenish,
  number_bitlist(2, Nth, Bitlist),
  number_bitlist(7, Sevenish, Bitlist),
  labeling([ffc], [Nth, Sevenish]).

:- begin_tests(p221).

test(simple, [nondet]) :-
  nth_sevenish(16, 2401).

test(simple_failure, [fail]) :-
  nth_sevenish(15, 2401).

test(generates_answer, [all(X == [1, 7, 8, 49, 50, 56, 57])]) :-
  between(1, 7, Nth), nth_sevenish(Nth, X).

test(generates_question, [all(X == [1, 2, 3, 4, 5, 6, 7])]) :-
  member(Sevenish, [1, 7, 8, 49, 50, 56, 57]),
  nth_sevenish(X, Sevenish).

test(most_general_query, [all(
      [Nth, Sevenish] == [
        [0, 0], [1, 1], [2, 7], [3, 8], [4, 49], [5, 50],
	[6, 56], [7, 57], [8, 343], [9, 344]
      ]
    )]) :-
  Nth #< 10,  % we only want to prove we can generate the first few answers
  nth_sevenish(Nth, Sevenish).

:- end_tests(p221).
