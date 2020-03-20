:- module(_, _, [hiord, fsyntax]).

% TODO: improve this test

:- use_module(library(streams)).
:- use_module(typeslib(typeslib)).

test1 :-
    cleanup_types,
    insert_user_type_pred_def(foo(_), [foo(a), foo(b)]),
    insert_user_type_pred_def(bar(_), [bar(b), bar(c)]),
    type_intersection_2(foo,bar,T),
    display(intersection(foo,bar,T)), nl,
    show_types.

def_foo :-
    insert_user_type_pred_def(foo(_), [
        (foo(X) :- int(X)),
        (foo(X) :- flt(X))
    ]).

def_bar :-
    insert_user_type_pred_def(bar(_), [
        (bar(X) :- int(X)),
        (bar(X) :- atm(X))
    ]).

def_pair :-
    insert_user_type_pred_def(pair(_,_), [
        (pair(p(X,Y),T) :- T(X), T(Y))
    ]).

test2 :-
    cleanup_types,
    def_foo,
    def_bar,
    type_intersection_2(foo,bar,T),
    display(intersection(foo,bar,T)), nl,
    show_types.

test3 :-
    cleanup_types,
    def_foo,
    def_bar,
    def_pair,
    type_intersection_2(pair(foo),pair(bar),T1),
    display(intersection(pair(foo),pair(bar),T1)), nl,
    show_types.

test4 :-
    cleanup_types,
    def_foo,
    def_bar,
    def_pair,
    type_intersection_2(foo,bar,T0),
    display(intersection(foo,bar,T0)), nl,
    type_intersection_2(pair(foo),pair(bar),T1),
    display(intersection(pair(foo),pair(bar),T1)), nl,
    % TODO: use "required types" to do garbage collection of unneeded types
    % TODO: test transformation to go back to parametric types?
    show_types.
    

