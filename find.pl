#!/home/brian/Prolog/swivm/versions/7.7.16/bin/swipl

:- use_module(library(process)).  % things like process_create/3 so we can shell out
:- use_module(library(pcre)).     % regular expressions
:- use_module(library(filesex)).  % helpers for dealing with files
:- use_module(library(yall)).     % lambda expressions
:- initialization(main, main).

/*
You can run commands such as:

./find.pl "size(max, 4000), size(min, 2000)"
  find files between 2000 and 4000 bytes in size

size(max, 4000), parent(v(Parent)), size(max, 5000, Parent)
  It's at most 4000 bytes, and it's parent is as most 5000 bytes
  (always succeeds, directories are 4096 bytes)

type(file)
  "f" also works

type(d), maxdepth(2)
  All directories which are at most 2 directories deep from here

type(f), depth(2)
  All files which are exactly 2 deep from here

type(f), name('pl$')
  Find all Prolog/Perl files, accepts PCRE syntax

type(d), \+(parent(r(git)))
  Find all directories which don't have "git" somewhere in the name of their parents

type(d), parent(v(Parent)), \+(parent(r(git), Parent))
  find all directories which don't have directories matching "git" as a grandparent

type(d), parent(g(File), Child), name('pl$', Child)
  find all the directories which contain Prolog/Perl files

*/

main(Argv) :-
  ( term_for_argv(Argv, Term, File)
  ; format('was not able to parse argument "~w"~n', Argv), halt),
  rewrite_term(Term, Processed, File),
  (
    each_file('.', File),
    once(call(Processed)), % it only needs to match once for it to be worth printing
    pretty_print_file(File),
    fail  % repeat, run the above for every file
  ; true). % suppress swipl's complaints that we can't prove anything

pretty_print_file(File) :-
  file_mode(File, Mode),
  size_file(File, Size),
  format('~w ~|~w ~6+ ~w~n', [Mode, Size, File]).

term_for_argv(Argv, Term, File) :-
  % we now have a list of Vars, we want to unify the 'File' one with File
  % leave the others alone, hopefully they're not important
  concat_atom(Argv, ' ', SingleArg),
  ( read_term_from_atom(SingleArg, Term, [variable_names(Vars)]),
    member('File'=File, Vars), !  % Prolog has occasional moments of clarity. This is one!
  ; % it's also allowed to provide no Var
    read_term_from_atom(SingleArg, Term, []) ).

rewrite_term(Var, Var, _File) :- var(Var), !.
rewrite_term(Atom, Atom, _File) :- atom(Atom), !.
rewrite_term(Number, Number, _File) :- number(Number), !.
rewrite_term(Term, Rewritten, File) :-
  /* walk the term, find any predicates which are almost right, replace them with
     predicates with File added to the end  */
  Term =.. Args,
  maplist({File}/[Left, Right]>>rewrite_term(Left, Right, File), Args, NewArgs),
  NewTerm =.. NewArgs,
  add_argument(NewTerm, Rewritten, File).

% if adding an argument would make this predicate callable rewrite it, adding File
add_argument(Term, Term, _File) :-
  functor(Term, Name, Arity),
  current_predicate(Name/Arity), !.
add_argument(Term, Rewritten, File) :-
  functor(Term, Name, Arity),
  Arity1 is Arity + 1,
  current_predicate(Name/Arity1),
  Term =.. Args,
  append(Args, [File], NewArgs),
  Rewritten =.. NewArgs, !.
% if it's not callable either with or without the argument leave it alone
add_argument(Term, Term, _File).

each_file(Directory, File) :-
  directory_files(Directory, Files),
  member(SubFile, Files),
  directory_file_path(Directory, SubFile, SubFilePath),
  \+(member(SubFile, ['.', '..'])),
  ( exists_directory(SubFilePath),
    each_file(SubFilePath, File)
  ; SubFilePath = File ).

file_mode(File, Mode) :-
  process_create(path(stat), ['-c', '%A', File], [stdout(pipe(Pipe))]),
  read_string(Pipe, eof, "\n", _End, Mode),
  close(Pipe).

% a difference list would be more efficient
path_string_list('.', []) :- !.
path_string_list(PathString, [Name|ListRest]) :-
  % .git/logs/regs/remotes/origin -> [origin, remotes, refs, logs, .git]
  directory_file_path(PathRest, Name, PathString),
  path_string_list(PathRest, ListRest).

% what we want to do is take a predicate and run it against every File
% instead of using call(), can we treat user input as terms to be matched against?

type(file, File) :-
  exists_file(File).
type(directory, File) :-
  exists_directory(File).
type(f, File) :- type(file, File).
type(d, File) :- type(directory, File).
type(any, File) :-
  type(file, File).
type(any, File) :-
  type(directory, File).

name(Name, File) :-
  re_match(Name, File).

parent(r(ParentRegex), File) :- !,
  directory_file_path(Parent, _, File),
  re_match(ParentRegex, Parent).
% there must be a better way to do the matching here
parent(v(Parent), File) :-
  directory_file_path(Parent, _, File).
parent(g(Parent), File) :-
  directory_files(Parent, Files),
  member(SubFile, Files),
  directory_file_path(Parent, SubFile, File).

maxdepth(MaxDepth, File) :-
  /* this is wildly inefficient, instead of generating every file and then checking
     depth we should be only generating files up to a certain depth */
  path_string_list(File, PathList),
  length(PathList, Depth),
  Depth =< MaxDepth.

depth(DesiredDepth, File) :-
  /* this is wildly inefficient, instead of generating every file and then checking
     depth we should be only generating files up to a certain depth */
  path_string_list(File, PathList),
  length(PathList, Depth),
  Depth == DesiredDepth.

size_between(Min, Max, File) :-
  size_file(File, Size),
  between(Min, Max, Size).

size(min, Min, File) :-
  size_file(File, Size),
  Size > Min.
size(max, Max, File) :-
  size_file(File, Size),
  Size < Max.
size(exact, Exact, File) :-
  size_file(File, Size),
  Size =:= Exact.

