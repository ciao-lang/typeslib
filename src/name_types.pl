% (included from typeslib.pl)
%! # Name of types
% TODO: document

:- data pgm_type_name/3. %% User programs type names.
:- data typ_name_counter/1.
:- data pgm_equiv_name/2.

:- data lib_type_name/3. %% Library type names.
:- data lib_typ_name_counter/1.
:- data lib_equiv_name/2.

cleanup_type_names :-
    retractall_fact(pgm_type_name(_,_,_)),
    retractall_fact(typ_name_counter(_)),
    retractall_fact(pgm_equiv_name(_,_)).

type_name(Name, List, Count):-
    pgm_type_name(Name, List, Count).
type_name(Name, List, Count):-
    lib_type_name(Name, List, Count).

equiv_name(A,B):-
    pgm_equiv_name(A,B).
equiv_name(A,B):-
    lib_equiv_name(A,B).

new_type_name(NewTyp):-
    new_counter_value(typ_name, N),
    name(N, NName),
    append("name", NName, TypName),
    name(NewTyp, TypName).

insert_type_name(Name,List,Count):-
    asserta_fact(pgm_type_name(Name,List,Count)).

retract_type_name(Name,List,Count):-
    retract_fact(pgm_type_name(Name,List,Count)).
% retract_type_name(Name,_,_):-
%       nonvar(Name),
%       display(user,'FFFFFFFFFFFFFFFFFFailllllllllllllllll'),display(user,Name),nl(user),fail.

get_type_name(Name,List):- 
    type_name(Name,List,_).
% get_type_name(Name,_):- 
%       nonvar(Name),
%       display(user,'FFFFFFFFFFFFFFFFFFailllllllllllllllll'),display(user,Name),nl(user),fail.



insert_equiv_name(Name,Canonical):-
    asserta_fact(pgm_equiv_name(Name,Canonical)).

retract_equiv_name(Name,Canonical):-
    retract_fact(pgm_equiv_name(Name,Canonical)).

get_equiv_name(Name,Canonical):- 
    equiv_name(Name,Canonical).



get_equiv_names(Names):-
    findall(equiv_name(X,Y), equiv_name(X,Y), Names).

get_type_names(Names):-
    findall(type_name(X,Y,Z), type_name(X,Y,Z), Names).

% ---------------------------------------------------------------------------

:- use_module(library(sets), [ord_union/3]).

% TODO: document: merge N1 and N2 names?
:- export(lab_intersect/2). % (internal?)
lab_intersect(N,N):- !.
lab_intersect(N1,N2):-
    retract_type_name(N1,L1,C),
    retract_type_name(N2,L2,_C2),
    ord_union(L1,L2,L),
    insert_type_name(N1,L,C),
    insert_equiv_name(N2,N1),
%       insert_type_name(N2,L,C2),
    replace_all_type_names(N2,N1),
    replace_all_equiv_names(N2,N1),!.

replace_all_equiv_names(N2,N1):-
    retract_equiv_name(N,N2),
    insert_equiv_name(N,N1),
    fail.
replace_all_equiv_names(_,_).

replace_all_type_names(N2,N1):-
    setof(N,L^S^(get_type_name(N,L),member((S,N2),L)),List),!,
%       ord_delete(List,N2,List_s),
    replace_all_type_name0(List,N2,N1).
replace_all_type_names(_,_).

replace_all_type_name0([],_,_).
replace_all_type_name0([N|List],N2,N1):-
    retract_type_name(N,L,C),
    replace_type_names(L,N2,N1,NL),
    sort(NL,NL_s),
    insert_type_name(N,NL_s,C),     
    replace_all_type_name0(List,N2,N1).

replace_type_names([],_N2,_N1,[]).
replace_type_names([(S,N2)|L],N2,N1,[(S,N1)|NL]):- 
    !,
    replace_type_names(L,N2,N1,NL).
replace_type_names([(S,N)|L],N2,N1,[(S,N)|NL]):- 
    replace_type_names(L,N2,N1,NL).

