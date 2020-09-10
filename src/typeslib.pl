:- module(typeslib, [
    % Operations
    dz_type_included/2,
    edz_type_included/5, % for sized types
    dz_equivalent_types/2,
    is_ground_type/1,
    type_intersection_0/3, % for nfsets
    type_intersection_2/3,  % for eterms domain
    is_infinite_type/1, % for non-failure
    finite_unfold/2, % for non-failure
    not_expandible_type/1, % for non-failure
    belongs_to_type/2,
    create_new_type_rule/2,
    find_type_functor/5,
    equivalent_to_top_type/1,
    equivalent_to_numeric/1,
    % Checks
    is_empty_type/1, % for eterms domain
    % Type symbols
    type_symbol/1,
    lattice_type_symbol/1,
    is_type_param_symbol/1,
    new_type_symbol/1,
    rule_type_symbol/1, % (internal)
    % Type terms
    type_escape_term_list/2,
    % Type names
    get_type_name/2,
    insert_type_name/3, 
    new_type_name/1,
    retract_type_name/3,
    get_equiv_name/2,
    insert_equiv_name/2,
    retract_equiv_name/2,
    % Type rules
    get_type_definition/2,
    insert_rule/2,
    remove_rule/1,
    insert_user_type_pred_def/2,
    legal_user_type_pred/1,
    prop_to_type/3,
    retract_rule/1,
    % Support
    equiv_type/2,
    get_required_types/1,
    pretty_type_lit_rules/4,
    pretty_type_lit_rules_desimp/2,
    assert_required_type/1,
    %
    show_types/0,
    show_type_db/0,
    %
    simplify_step2/0,
    typedef_to_pred/3,
    cleanup_types/0,
    % assert_initial_types/0,
    create_defined_types_filters/0,
    % approx_as_defined/2, % TODO: not used, see def_type_approx_as_defined/2
    gen_lib_type_info/1,
    load_lib_type_info/1,
    cleanup_lib_type_info/0,
    set_param_matching_mode/1,
    get_preprocessing_unit_types/1,
    match_one_rule_as_parametric/2,
    get_compatible_types/4,
    assert_and_propagate_type_equivalence/2,
    contains_type_param/1,
    % Widenings
    terms_naive_ewiden_el/2,
    shortening_el/3
], [assertions, basicmodes, regtypes, datafacts, hiord, nativeprops]).

% -----------------------------------------------------------------------

:- doc(title,"Operations on Regular Types").  

:- doc(author, "Pedro L@'{o}pez").  
:- doc(author, "The Ciao Development Team").

:- doc(module, "This library implements routines for manipulating
   regular types.  Some of the procedures are adaptations of the work
   @em{A regular type language for logic programs} P.W. Dart and
   J. Zobel.  In F. Pfenning, editor, @em{Types in Logic Programming},
   pages 157--187.  MIT Press, 1987.").

:- doc(appendix, "@section{Regular Type Syntax}
    @include{regular_type_syntax.lpdoc}").

:- doc(bug,"1. Check that a proper cleaning-up is performed (eterms loops
    in a second call, now).").
:- doc(bug,"2. Implement a proper initialization (initial types) and
    finalization (required_types).").
:- doc(bug,"3. Check imports like database and builtintables.").
:- doc(bug,"4. Provide for distinct type names: now, if rt18 already exists
    in the source, we will have a clash!").
:- doc(bug,"5. No way with types like p::=list(p)!!!").
:- doc(bug,"6. insert_user_type_pred_def seems to loop when the type
    definition either: has a cut, a builtin, or a call to a predicate
    undefined (as a type), e.g., with gnd/1.").
% (PBC) Looks like this has been solved:
%:- doc(bug,"7. Has to use native_to_prop(Goal,regtype(G)) to change Goal
%       in the definition of user types when asserting them. Otherwise, in,
%       e.g., example7_2.pl:
%{WARNING (typeslib): Type 'basic_props:int' not defined, assumed bot}.").
:- doc(bug,"8. typeslib:dz_type_included(rt1,pt3) fails
    with asserted type definitions:
    typedef(rt1,[[[^(a)]]]).
    param_type_symbol_renaming(
                 'basic_props:list'('basic_props:gnd'),pt3).
    See bugs/assumed_bot.pl").

% ---------------------------------------------------------------------------
% (options for typeslib)

:- include(typeslib(typeslib_hooks)).

% ---------------------------------------------------------------------------

% ciao library
:- use_module(library(aggregates)).
:- use_module(library(sort)).
:- use_module(library(write)).
% :- use_module(library(formulae), [list_to_conj/3]).
:- use_module(library(lists), [member/2, append/3, reverse/2]).
:- use_module(library(llists), [flatten/2]).
:- use_module(library(idlists), [member_0/2, subtract/3]).
:- use_module(library(messages)).
:- use_module(library(terms_vars), [varset/2]).
%:- use_module(library(sets), [insert/4]).

% own library
:- use_module(typeslib(type_errors)).
:- reexport(typeslib(regtype_basic_lattice)). % TODO: do not reexport all?
%:- reexport(typeslib(regtype_rules)).
%:- reexport(typeslib(basic_type_operations)).

% includes:
:- include(typeslib(type_ops)).
:- include(typeslib(basic_type_operations)).
:- include(typeslib(basic_type_operations_edz)).
:- include(typeslib(operations)).
:- include(typeslib(detunion)).
:- include(typeslib(type_simplification)).
:- include(typeslib(type_translate)).
:- include(typeslib(ppoint)).
%:- include(typeslib(fd_reg_type_lattice)).
:- include(typeslib(typedef_to_pred)).
:- include(typeslib(pred_to_typedef)).
:- include(typeslib(name_types)).  % for eterms domain
:- include(typeslib(type_widen)).
:- include(typeslib(typeslib_deftypes)).

% ---------------------------------------------------------------------------

:- use_module(typeslib(typedef)).

% TODO: reexports of internal preds, improve?
:- reexport(typeslib(typedef), [
    typedef/2,
    paramtypedef/2,
    param_type_symbol_renaming/2
]).

:- include(typeslib(regtype_rules)).

:- prop type_symbol/1.

type_symbol(Type) :-
    atom(Type),
    \+ Type = [].

%% :- pred type_symbol(Type)
%% 
%% ; "@var{Type} is a type symbol.".
%% 
%% type_symbol(Type):- 
%%     top_type(Type); 
%%     bot_type(Type); 
%%     ground_type(Type); 
%%     base_type_symbol(Type);
%%     rule_type_symbol(Type).

% -----------------------------------------------------------------------
% Counters

lib_counter_value(typ_name, Count) :- lib_typ_name_counter(Count).
lib_counter_value(typ_sym, Count) :- lib_typ_sym_counter(Count).
lib_counter_value(param_typ_sym, Count) :- lib_param_typ_sym_counter(Count).
lib_counter_value(typ_param_sym, Count) :- lib_typ_param_sym_counter(Count).

counter_value(typ_name, Count) :- typ_name_counter(Count).
counter_value(typ_sym, Count) :- typ_sym_counter(Count).
counter_value(param_typ_sym, Count) :- param_typ_sym_counter(Count).
counter_value(typ_param_sym, Count) :- typ_param_sym_counter(Count).

set_counter(typ_name, Count) :- set_fact(typ_name_counter(Count)).
set_counter(typ_sym, Count) :- set_fact(typ_sym_counter(Count)).
set_counter(param_typ_sym, Count) :- set_fact(param_typ_sym_counter(Count)).
set_counter(typ_param_sym, Count) :- set_fact(typ_param_sym_counter(Count)).

% Initialize the type symbol counter to 0 or to the last value
% registered in the builtintables (lib_* facts).
init_counter(Counter) :-
    ( lib_counter_value(Counter, Count) -> true ; Count = 0 ),
    set_counter(Counter, Count).

% Obtain the current type symbol counter value and increment the
% counter.
new_counter_value(Counter, N):-
    ( counter_value(Counter, N0) -> true
    ; init_counter(Counter),
      counter_value(Counter, N0)
    ),
    N1 is N0 + 1, 
    set_counter(Counter, N1),
    N = N0.

% -----------------------------------------------------------------------
% TODO:[new-resources] reliminary support for var_type (for etermsvar domain)

:- export(type_intersection_2_VR/3).
:- include(typeslib(basic_type_operations_vr)).
:- include(typeslib(ppoint_vr)).

% ---------------------------------------------------------------------------

:- export(post_init_types/0).
% Post-initialization once types are loaded using insert_user_type_pred_def/2
post_init_types :-
    remove_parametric_types_from_rules,
    simplify_step1,
    ( typeslib_flag(use_deftypes) ->
        ( typeslib_flag(use_defined_types_filters) ->
            create_defined_types_filters
        ; true
        ),
        build_defined_types_lattice
    ; true
    ).

% ---------------------------------------------------------------------------

cleanup_types:- 
    cleanup_type_equivs,
    retractall_fact(pgm_typedef(_, _)),
    retractall_fact(param_typ_sym_counter(_)),
    retractall_fact(pgm_param_type_symbol_renaming(_, _)),
    retractall_fact(pgm_paramtypedef(_, _)),
    retractall_fact(types_used_to_colapse_others(_)),
    retractall_fact(type_symbols_used_to_colapse_others(_)),
    retractall_fact(pgm_required_type(_)),
    retractall_fact(pgm_user_type(_)),
    retractall_fact(typ_param_sym_counter(_)),
    % typeslib_deftypes
    retractall_fact(pgm_def_equiv_type(_,_)),
    retractall_fact(pgm_def_subtype_basic(_,_)),
    retractall_fact(pgm_param_type_hook(_,_,_)),
    % retractall_fact(pgm_functor_types(_,_,_)), % unused (JFMC)
    %
    retractall_fact(pgm_computed_type_inclusion(_, _)),
    retractall_fact(pgm_dz_pair(_, _)), % currently not needed % TODO: used internally for dz_type_included, do not need to be saved! (JFMC)
    % retractall_fact(simplified_type_symbol_counter(_)),  % not really needed 
    % Assertions
    init_counter(param_typ_sym), % TODO: needed? param_typ_sym_counter is reset before
    retractall_fact(typ_sym_counter(_)),
    cleanup_type_names,
    retractall_fact(functor_types(_,_,_)),
    retractall_fact(param_type_depth(_,_)).

cleanup_type_equivs:-
    retractall_fact(pgm_equiv_type(_,_)).

%% %------------------------------------------------------------------%
%% % :- collect_usedtypes(listtype)::in, list(type)::in,list(type)::out) is det.
%% %------------------------------------------------------------------%
%% % Collects the set of type(names) used in the list of types (and 
%% % their definitions) provided as first argument.
%% %------------------------------------------------------------------%
%% collect_usedtypes([],UsedTypes,UsedTypes).
%% collect_usedtypes([Type|Types],UsedTypes,NUsedTypes):-
%%     collect_usedtype(Type,UsedTypes,UsedTypes0),
%%     collect_usedtypes(Types,UsedTypes0,NUsedTypes).
%%     
%% %------------------------------------------------------------------%
%% % :- collect_usedtypes(type::in, list(type)::in,list(type)::out) is det.
%% %------------------------------------------------------------------%
%% % Adds to UsedTypes the set of type(names) used in Type.
%% %------------------------------------------------------------------%
%% collect_usedtype(Type,UsedTypes,NUsedTypes):-
%%     ( rule_type_symbol(Type) ->
%%         insert(UsedTypes,Type,UsedTypes0,Member),
%%         ( Member = yes -> % already added to UsedTypes
%%             NUsedTypes = UsedTypes
%%         ; get_type_definition(Type,Def) -> 
%%             collect_usedtypes(Def,UsedTypes0,NUsedTypes)
%%         ; NUsedTypes = UsedTypes % parameter type, do not neet to add it
%%         )
%%     ; NUsedTypes = UsedTypes % does not have a definition (any, int, etc)
%%     ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%  The following utilities are for debugging. Comment when included in
%  the source code. 

show_types:-
    nl, write('Type Names:'), nl, nl,
    write_type_names, 
    nl, write('Equiv Names:'), nl, nl,
    write_equivalents_names, 
    nl, write('Non-Parametric type definitions:'), nl, nl,
    write_all_typedef,
    nl, write('Parametric type definitions:'), nl, nl,
    write_all_paramtypedef,
    nl, write('Equivalent types:'), nl, nl,
    write_all_equiv_type,
    nl, write('Parametric type symbol renamings:'), nl, nl,
    write_all_param_type_symbol_renaming,
    nl, write('Required types:'), nl, nl,
    write_all_required_types.

write_type_names:-
    get_type_names(Names),
    write_names(Names).

write_equivalents_names:-
    get_equiv_names(Names),
    write_equiv_names(Names).

write_names([]).
write_names([N|Names]):-
    writeq(N), 
    write('.'),
    nl,     
    write_names(Names).

write_equiv_names([]).
write_equiv_names([N|Names]):-
    writeq(N), 
    write('.'),
    nl,     
    write_equiv_names(Names).

write_all_typedef:-
    % All the non-parametric type rules currently in the database
    findall(typedef(X, Y), typedef(X, Y), Rules),
    write_list2(Rules).

write_all_paramtypedef:-
    findall(paramtypedef(X, Y), paramtypedef(X, Y), Rules),
    write_list2(Rules).

write_all_equiv_type:-
    findall(equiv_type(X, Y), equiv_type(X, Y), Z),
    write_list2(Z). 

write_all_param_type_symbol_renaming:-
    findall(param_type_symbol_renaming(ParTyp, NPartyp),
            param_type_symbol_renaming(ParTyp, NPartyp),    
            Renamings), 
    write_list2(Renamings).  

write_list2([]).
write_list2([H|L]) :-
    writeq(H), 
    write('.'),
    nl, 
    write_list2(L).

write_all_required_types:-
    required_type(T),
    write(T), nl,
    fail.
write_all_required_types.

%%

show_type_db:-
     nl, write('Non-Parametric type definitions:'), nl, nl,
     write_all_typedef,
     nl, write('Parametric type definitions:'), nl, nl,
     write_all_paramtypedef,
     nl, write('Equivalent types:'), nl, nl,
     write_all_equiv_type,
     nl, write('Parametric type symbol renamings:'), nl, nl,
     write_all_param_type_symbol_renaming, nl, 
     write_typ_sym_counter, nl,
     write_param_typ_sym_counter, nl,
     nl, write('Internal auxiliary info:'),
     nl, write('computed_type_inclusion'),
     nl, write_all_computed_type_inclusion,
     nl, write('no_simplified_type:'),
     nl, write_all_no_simplified_type,
     nl, write('computed_type_intersec:'),
     nl, write_all_computed_type_intersec,
     nl, write('computed_empty_type:'),
     nl, write_all_computed_empty_type,
     nl, write('computed_infinite_type:'),
     nl, write_all_computed_infinite_type,
     nl, write('already_validated:'),
     nl, write_all_already_validated.

write_typ_sym_counter :-
    typ_sym_counter(N), 
    !,
    write('Type symbol counter = '), 
    write(N). 
write_typ_sym_counter :-
    write('*There is no type symbol counter*'). 

write_param_typ_sym_counter :-
    param_typ_sym_counter(N), 
    !,
    write('Parametric type symbol counter = '), 
    write(N). 
write_param_typ_sym_counter :-
    write('*There is no parametric type symbol counter*'). 


write_all_computed_type_intersec :-
    findall(computed_type_intersec(A, B, C), computed_type_intersec(A, B, C), L),
    write_list2(L). 

write_all_already_validated :-
    findall('$already_validated$'(A), '$already_validated$'(A), L),
    write_list2(L). 

write_all_computed_infinite_type :-
    findall(computed_infinite_type(A), computed_infinite_type(A), L),
    write_list2(L). 

write_all_computed_empty_type :-
    findall(computed_empty_type(A), computed_empty_type(A), L),
    write_list2(L). 

write_all_no_simplified_type :-
    findall(no_simplified_type(A), no_simplified_type(A), L),
    write_list2(L). 

%%%%%

%%  %% print_type_rules([], _Modes).
%%  %% print_type_rules([Entry|Tab], Modes):-
%%  %%     Entry = st(Pred/_Arity, Clauses, _),
%%  %%     print_typedef(Modes, Pred, Clauses), %nd-PLG 
%%  %%     (define_numeric_type(Pred) -> 
%%  %%          true ; 
%%  %%          predicate_2_type_rule(Pred, Clauses, TypeRule),
%%  %%          internal_rule_translate(TypeRule, NewRule),
%%  %%          print_type_rule(Modes, NewRule)
%%  %%          % print_type_rule(Modes, TypeRule)
%%  %%     ),
%%  %%     print_type_rules(Tab, Modes).
%% 
%% print_type_rule(cl, TypeDef):-
%%      write(':- '), writeq(TypeDef), write('.'), nl.
%% print_type_rule(pl, TypeDef):-
%%      print_rul(TypeDef).
%% 
%% print_typedef(cl, Type, TypeDef):-
%%      write('%:- typedef( '), write(Type), 
%%      write(' , '), writeq(TypeDef), 
%%      write(' ).'),
%%      nl.
%% print_typedef(pl,_,TypeDef):-
%%      print_rul(TypeDef).
%% 
%% print_rul([Cl|TypeDef]):-
%%      write('%  '), writeq(Cl), nl,
%%      print_rul(TypeDef).
%% print_rul([]).

% ---------------------------------------------------------------------------

:- export(show_types_raw_printer/0).
show_types_raw_printer :- % TODO: it was in raw_printer.pl; deprecate and use proper printing?
    typedef(A, B),
    is_new_type(A),
    show_data(typedef(A, B)),
    fail.
show_types_raw_printer.

show_data(R) :-
    \+ \+ (numbervars(R, 0, _), show_data_(R)).

show_data_(X) :-
    write(X), nl.

:- export(is_new_type/1).
is_new_type(A) :-
    atom_concat('rt', N, A),
    atom_number(N,_).

%----------------------------------------------------------------------%

get_module_types([term,bot|Types]):-
    get_preprocessing_unit_types(Types).

 %% :- data get_module_types/1.
 %% 
 %% assert_initial_types:-
 %%         get_module_types0(Types),       
 %%         set_fact(get_module_types([term,bot|Types])).
 %% 
 %% get_module_types0(Module_Types):-
 %%     findall(Typ,typedef(Typ, _Def),Module_Types).

contain_this_type([],_Type,[]).
contain_this_type([S|List],Type,[S|SuperSet]):-
    dz_type_included(Type,S),!,
    contain_this_type(List,Type,SuperSet).
contain_this_type([_S|List],Type,SuperSet):-
    contain_this_type(List,Type,SuperSet).

% TODO: not used, see def_type_approx_as_defined/2
%% approx_as_defined(Type,ApproxType):-
%%     \+ internally_defined_type_symbol(Type,_),
%%     !,
%%     ApproxType = Type.
%% approx_as_defined(Type,ApproxType):-
%%     internal_approx_as_defined(Type,ApproxType).

internal_approx_as_defined(Type,ApproxType):-
    is_type_param_symbol(Type),
    param_matching_mode(on),!,
    ApproxType = Type.
internal_approx_as_defined(Type,ApproxType):-
    prlb(Type,Fs),
    gather_cands_decide(Fs,Type,SuperSet),
    reverse(['basic_props:term'|SuperSet], SS1),
    minimaltype(SS1,ApproxType),!.

gather_cands_decide(_Fs,Type,[ParType]):- % parametric rule
    match_one_rule_as_parametric(Type, ParType).
gather_cands_decide(Fs,Type,Cs):-
    gather_cands(Fs,Type,[],Cs).

gather_cands([],_,Cs,Cs) :-!.
gather_cands([F|Fs],Type,Seen,Cs) :-    
    get_functor_types(F,Ts),
    filter_cands(Ts,Type,Seen,Seen1),
    gather_cands(Fs,Type,Seen1,Cs).
    

get_functor_types(F,Ts) :-
    native_type_symbol(F),!,
    functor_types(F,Ts,basic).
get_functor_types(F,Ts) :-
    functor_types(F,Ts,rule),!.
get_functor_types(F,Ts) :-
    findall(T, (
        functor_types(B,T,basic),
        prepare_functor(F,F_ok),
        dz_type_included(F_ok,B)
    ), TTs),
    flatten(TTs,Ts).


prepare_functor(N/A,Term) :-
    !,
    functor(T0,N,A),
    Term = ^T0.
prepare_functor(F,F).


filter_cands([],_,Seen,Seen).
filter_cands([S|Cands],Type,Seen,SeenOut) :-
    \+ member(S,Seen),
    dz_type_included(Type,S),!,
    filter_cands(Cands,Type,[S|Seen],SeenOut).
filter_cands([_S|Cands],Type,Seen,FCands):-
    filter_cands(Cands,Type,Seen,FCands).


minimaltype([T],T).
minimaltype([T1,T2|List],T):-
    dz_type_included(T2,T1),!,
    minimaltype([T2|List],T).
minimaltype([T1,_T2|List],T):-
    minimaltype([T1|List],T).

:- pred lattice_type_symbol(+Type)
   # "Succeeds if and only if @var{Type} is a rule type symbol that is
      defined by an (asserted) type rule or @var{Type} is a constant
      defining a @tt{native type} of the lattice (bottom point excluded).".

lattice_type_symbol(Type):- 
    native_type_symbol(Type), 
    !.
lattice_type_symbol(Type):- 
    get_typedef(Type, _Defin).


:- data functor_types/3. 
:- data param_type_depth/2.


create_defined_types_filters :-
    get_preprocessing_unit_types(Types),
    create_defined_types_filters_x(Types).

create_defined_types_filters_x([]).
create_defined_types_filters_x([T|Ts]) :-
    prlb(T,Fs),
    add_to_each_functor(Fs,T),
    create_defined_types_filters_x(Ts).

add_to_each_functor([],_).
add_to_each_functor([F|Fs],T) :-
    ( retract_fact(functor_types(F,Ts,_)) ->
        append(Ts,[T],Ts1)
    ; Ts1 = [T]
    ),
    ( native_type_symbol(F) ->
        M = basic
    ; M = rule
    ),
    assertz_fact(functor_types(F,Ts1,M)),
    add_to_each_functor(Fs,T).

:- pred prlb(+Type,-Lab): pure_type_term * list
   # "It obtains the principal labels of the type graph @var{Type},
      i.e. the sorted set of functor/arity terms or basic type terms
      which are the principal function symbols or basic type terms of
      the type term @var{Type}.".

prlb(T,Lab):-
    prlb0(T,L,[],[]),
    sort(L,Lab).
prlb0(T,Lab,L,Seen):-
    get_typedef(T,Def),!,
    ( member(T,Seen) ->
        Lab = L
    ; prlblist(Def,Lab,L,[T|Seen])
    ).
prlb0(T,[Name/Arity |L],L,_Seen):-
    compound_pure_type_term(T,_Term,Name,Arity),!.
prlb0(T,[T|L],L,_Seen).

prlblist([],L,L,_Seen).
prlblist([T|RestT],Lab,L,Seen):-
    prlb0(T,Lab,L1,Seen),
    prlblist(RestT,L1,L,Seen).


match_one_rule_as_parametric(Type, NewType):-
    param_type_symbol_renaming(_,Type),
    !,
    NewType = Type.
match_one_rule_as_parametric(Type, NtypSymbol1):-
    get_type_definition(Type,Def),
    TypeDef = typedef(Type,Def),
    paramtypedef(Head,Body), 
    ParRule = paramtypedef(Head,Body), 
    copy_term(ParRule, Rule),
    TypeDef = typedef(NTypeSymbol, NDefin), non_par_rule_type_symbol(NTypeSymbol), % TODO: non_par_rule_type_symbol/1 check needed?
    Rule = paramtypedef(PTypeSymbol, PDefin), par_rule_type_symbol(PTypeSymbol), % TODO: par_rule_type_symbol/1 check needed?
%        order_type_defin(PDefin, OrPDefin), !, 
    match_defin(NDefin, PDefin, PDefin), 
    ground(PTypeSymbol),
    assert_param_type_rule_instance(PTypeSymbol, Cand),
%       display(assert_param_type_rule_instance(PTypeSymbol, Cand)),nl,
    dz_type_included(NTypeSymbol, Cand),
    !,
    assert_and_propagate_type_equivalence(NTypeSymbol, Cand),
    check_max_depth(Cand,3,NtypSymbol1).


match_defin([], RestPDefin, PDefin) :-
    RestPDefin \= PDefin, % some parts of the parametric rule have
                          % been matched
    varset(RestPDefin,FreeParams),
    bind_to_bot(FreeParams).
match_defin([NType|NDefin], PDefin, OrigPDefin):-
    match_with_some_type(PDefin, NType, RestPDefin),
    match_defin(NDefin, RestPDefin, OrigPDefin).

match_with_some_type([PType|PDefin], NType, PDefin):-
    type_match(NType, PType), !.
match_with_some_type([PType|PDefin], NType, [PType|RestPDefin]):-
    match_with_some_type(PDefin, NType, RestPDefin).

type_match(NType, PType):-
    var(PType),
    internal_approx_as_defined(NType,DefType),
    !,
    PType = DefType.
type_match(NType, PType):- 
    NType == PType,
    !.
type_match(NType, PType):-
    compound_pure_type_term(NType, NComp, Name, Arity),
    compound_pure_type_term(PType, PComp, Name, Arity), % PType is not a variable.
    !,
    compound_type_match(Arity, NComp, PComp).
type_match(_NType, PType):-
    % non_par_rule_type_symbol(NType),
    par_rule_type_symbol(PType), !.
type_match(NType, PType):-
    non_par_rule_type_symbol(NType),
    non_par_rule_type_symbol(PType).

compound_type_match(0, _NComp, _PComp):-!.
compound_type_match(ArgNum, NComp, PComp):-
    ArgNum > 0, 
    arg(ArgNum, NComp, NArg),
    arg(ArgNum, PComp, PArg),
    type_match(NArg, PArg),
    NArgNum is ArgNum - 1,
    compound_type_match(NArgNum, NComp, PComp).

bind_to_bot([]).
bind_to_bot([bot|Ps]):-
    bind_to_bot(Ps).

check_max_depth(_,0,term) :- !. % TODO: added missing cut, OK?
check_max_depth(PType,Depth,NewType) :-
    param_type_symbol_renaming(Def,PType),!,
    Def =.. [NDef,NextType|Rest],
    Depth1 is Depth - 1,
    check_max_depth(NextType,Depth1,NewNextType),
    ( NewNextType \= NextType ->
        NewDef =.. [NDef,NewNextType|Rest],
        assert_param_type_rule_instance(NewDef, NewType)
    ; NewType = PType
    ).
check_max_depth(Type,_,Type).

set_param_matching_mode(M) :-
    set_fact(param_matching_mode(M)).

% TODO: potentially slow
contains_type_param(T) :-
    compute_transitive_closure([T],[],Types),
    member(T0,Types),
    is_type_param_symbol(T0),!.

%-----------------------------------------------------------
% TODO: document

:- export(concrete/4).
concrete(Type,List1,List2,Seen):-
    % TODO: add cut? reverse equiv_type/2 call?
    ( Type1 = Type
    ; equiv_type(Type,Type1)
    ),
    get_typedef(Type1,Def),
    !,
    ( member(Type,Seen) ->
        fail
    ; concret_def(Def,List1,List2,[Type|Seen])
    ).
concrete(Type,List1,List2,Seen):-
    compound_pure_type_term(Type,Term,F,A),!,
    functor(Seed,F,A),
    concret_arg(A,Term,[Seed|List2],List1,List2,Seen).
%       append(List,List2,List1).
concrete(^(Term),[Term|List],List,_).
concrete(Term,[Term|List],List,_):- number(Term).
concrete(Term,[Term|List],List,_):- Term = [_|_].
concrete(Term,[Term|List],List,_):- Term = [].
    
concret_def([],L,L,_).
concret_def([T1|Def],List1,List2,Seen):-
    concrete(T1,List1,List0,Seen),
    concret_def(Def,List0,List2,Seen).

concret_arg(0,_,P,P,_,_).
concret_arg(A,Term,Prev,List,List2,Seen):-
    arg(A,Term,Arg1),
    concrete(Arg1,ListArg1,[],Seen),
%       concrete(Arg1,ListArg1,List2,Seen),
    buildarg(Prev,NewPrev,List2,A,ListArg1),
    A1 is A -1,
    concret_arg(A1,Term,NewPrev,List,List2,Seen).

buildarg(L,M,M,_,_):- var(L),!.
buildarg([],M,M,_,_):- !.
buildarg([F|Prev],L,T,A,ListArg):-
    addarg(ListArg,F,A,L,L2),
    buildarg(Prev,L2,T,A,ListArg).

addarg([],_,_,L,L).
addarg([C|ListArg],F,A,[Term|L1],L2):-
    copy_term(F,Term),
    arg(A,Term,C),
    addarg(ListArg,F,A,L1,L2).
    
%-----------------------------------------------------------
% TODO: document (used in eterms)

:- export(partial_concrete/4).
partial_concrete(Type,List1,List2,Seen):-
    % TODO: add cut? reverse equiv_type/2 call?
    ( Type1 = Type
    ; equiv_type(Type,Type1)
    ),
    get_typedef(Type1,Def),
    !,
    ( member(Type,Seen) ->
        new_type_name(N),
        insert_type_name(N,[],0),
        List1 = [(A,[A:(N,Type)])|List2]
    ; partial_concret_def(Def,List1,List2,[Type|Seen])
    ).
partial_concrete(Type,List1,List2,Seen):-
    compound_pure_type_term(Type,Term,F,A),!,
    functor(Seed,F,A),
    partial_concret_arg(A,Term,[(Seed,[])|List2],List1,List2,Seen).
partial_concrete(^(Term),[(Term,[])|List],List,_) :- !.
partial_concrete(Term,[(Term,[])|List],List,_):- number(Term),!.
partial_concrete(Term,[(Term,[])|List],List,_):- Term = [_|_],!.
partial_concrete(Term,[(Term,[])|List],List,_):- Term = [],!.
partial_concrete(Type,[(A,[A:(N,Type)])|List],List,_):-
    new_type_name(N),
    insert_type_name(N,[],0).

partial_concret_def([],L,L,_).
partial_concret_def([T1|Def],List1,List2,Seen):-
    partial_concrete(T1,List1,List0,Seen),
    partial_concret_def(Def,List0,List2,Seen).

partial_concret_arg(0,_,P,P,_,_) :- !.
partial_concret_arg(A,Term,Prev,List,List2,Seen):-
    arg(A,Term,Arg1),
    partial_concrete(Arg1,ListArg1,[],Seen),
    partial_buildarg(Prev,NewPrev,List2,A,ListArg1),
    A1 is A -1,
    partial_concret_arg(A1,Term,NewPrev,List,List2,Seen).

% TODO: why different than buildarg?
partial_buildarg(L,M,M,_,_):- var(L),M=L, !. % TODO: move cut?
partial_buildarg([(F,S)|Prev],L,T,A,ListArg):-
    partial_addarg(ListArg,F,A,S,L,L2),
    partial_buildarg(Prev,L2,T,A,ListArg).

% TODO: why different than addarg?
partial_addarg([],_,_,_,L,L).
partial_addarg([(C,CS)|ListArg],F,A,S,[(Term,TermS)|L1],L2):-
    copy_term((F,S),(Term,Term1S)),
    arg(A,Term,C),
    append(CS,Term1S,TermS),
    partial_addarg(ListArg,F,A,S,L1,L2).

%----------------------------------------------------------------------%

:- export(normalize_type/2).
normalize_type(Type,NType):-
    nonvar(Type),
    ( number(Type)
    ; Type = []
    ; Type = [_|_]
    ; Type = ^(_)
    ),!,
    new_type_symbol(NType),
    insert_rule(NType,[Type]).
normalize_type(Type,Type).

%----------------------------------------------------------------------%
% TODO: put together with prop_to_type, type_to_prop, etc.?

:- export(make_prop_type_unary/2).
% If T=P(X,A) obtain a new Pa(X) (unary), otherwise keep unchanged
% Note: T is a prop, not a typeslib type
make_prop_type_unary(T, NonPT) :-
    functor(T,_,2),!,
    prop_unapply(T,TypeInstance,V),
    assert_param_type_rule_instance(TypeInstance, NonPType),
    functor(NonPT,NonPType,1),
    arg(1,NonPT,V).
make_prop_type_unary(T,T).

%----------------------------------------------------------------------%
% Generation of source code for storing types from libraries.
%----------------------------------------------------------------------%

:- pred cleanup_lib_type_info
   # "Cleans up all facts of lib_* predicates.".

cleanup_lib_type_info:-
    retractall_fact(lib_computed_type_inclusion(_,_)),
    retractall_fact(lib_dz_pair(_,_)),
    retractall_fact(lib_type_name(_,_,_)),
    retractall_fact(lib_typ_name_counter(_)),
    retractall_fact(lib_equiv_name(_,_)),
    retractall_fact(lib_equiv_type(_,_)),
    retractall_fact(lib_typ_sym_counter(_)),
    retractall_fact(lib_param_typ_sym_counter(_)),
    retractall_fact(lib_param_type_symbol_renaming(_,_)),
    retractall_fact(lib_typedef(_,_)),
    retractall_fact(lib_paramtypedef(_,_)),
    retractall_fact(lib_user_type(_)),
    retractall_fact(lib_required_type(_)),
    retractall_fact(lib_types_used_to_colapse_others(_)),
    retractall_fact(lib_type_symbols_used_to_colapse_others(_)),
    retractall_fact(lib_typ_param_sym_counter(_)),
    % typeslib_deftypes
    retractall_fact(lib_def_equiv_type(_,_)),
    retractall_fact(lib_def_subtype_basic(_,_)),
    retractall_fact(lib_param_type_hook(_,_,_)).
    % retractall_fact(lib_functor_types(_,_,_)). % unused (JFMC)    

%% ---------------------------------------------------------------------------

:- use_module(engine(io_basic)).
:- use_module(library(read), [read/2]).

load_lib_type_info(Stream):-
    repeat,
    read(Stream,Fact),
    ( Fact = end_of_file ->
        true
    ; assertz_fact(Fact),
      fail
    ).

%% ---------------------------------------------------------------------------

gen_lib_type_info(Stream) :-
    nl(Stream), % TODO: needed?
    ( % (failure-driven loop)
      lib_type_data(Data),
        displayq(Stream,Data),
        display(Stream,'.'),nl(Stream),
        fail
    ; true
    ).
gen_lib_type_info(_Stream).  

lib_type_data(lib_computed_type_inclusion(A,B)) :- pgm_computed_type_inclusion(A,B).
lib_type_data(lib_dz_pair(A,B)) :- pgm_dz_pair(A,B).
lib_type_data(lib_type_name(A,B,C)) :- pgm_type_name(A,B,C).
lib_type_data(lib_typ_name_counter(A)) :- typ_name_counter(A).
lib_type_data(lib_equiv_name(A,B)) :- pgm_equiv_name(A,B).
lib_type_data(lib_equiv_type(A,B)) :- pgm_equiv_type(A,B).
lib_type_data(lib_typ_sym_counter(A)) :- typ_sym_counter(A).
lib_type_data(lib_param_typ_sym_counter(A)) :- param_typ_sym_counter(A).
lib_type_data(lib_param_type_symbol_renaming(A,B)) :- pgm_param_type_symbol_renaming(A,B).
lib_type_data(lib_typedef(A,B)) :- pgm_typedef(A,B).
lib_type_data(lib_paramtypedef(A,B)) :- pgm_paramtypedef(A,B).
lib_type_data(lib_user_type(A)) :- pgm_user_type(A).
lib_type_data(lib_required_type(A)) :- pgm_required_type(A).
lib_type_data(lib_types_used_to_colapse_others(A)) :- types_used_to_colapse_others(A).
lib_type_data(lib_type_symbols_used_to_colapse_others(A)) :- type_symbols_used_to_colapse_others(A).
lib_type_data(lib_typ_param_sym_counter(A)) :- typ_param_sym_counter(A).
% typeslib_deftypes
lib_type_data(_) :-
    build_defined_types_lattice, % TODO: also in post_init_types/0, move above??
    fail.
lib_type_data(lib_def_equiv_type(A,B)) :- pgm_def_equiv_type(A,B).
lib_type_data(lib_def_subtype_basic(A,B)) :- pgm_def_subtype_basic(A,B).
lib_type_data(lib_param_type_hook(A,B,C)) :- pgm_param_type_hook(A,B,C).
% lib_type_data(lib_functor_types(A,B,C)) :- pgm_functor_types(A,B,C).

% ---------------------------------------------------------------------------
%! # Dump and restore types

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(assoc), [ord_list_to_assoc/2, get_assoc/3]).

:- export(dump_types/2).
:- meta_predicate dump_types(?, pred(1)).
dump_types(Types, AssertPred) :-
    compute_transitive_closure(Types, [], Types1),
    ( typeslib_flag(use_deftypes) ->
        filter_out_lib_types(Types1,Types2)
    ; Types2 = Types1
    ),
    select_rules_3(Types2,UsedRules0), % TODO: difference w.r.t. get_required_rules/2?; add filter here instead?
    ( typeslib_flag(use_deftypes) ->
        get_necessary_param_renamings(Types2,UsedRules0,UsedRules) % TODO: why?
    ; UsedRules = UsedRules0
    ),
    dump_rules(UsedRules,AssertPred).

:- export(is_dump_types_fact/1).
% (Use when merging dump facts) % TODO: find a better solution (e.g., mark type dump end)
is_dump_types_fact(typedef(_,_)).
is_dump_types_fact(param_type_symbol_renaming(_,_)).

:- meta_predicate dump_rules(?,pred(1)).
dump_rules([],_AssertPred).
dump_rules([X|Xs],AssertPred):-
    AssertPred(X),
    dump_rules(Xs,AssertPred).

filter_out_lib_types([],[]).
filter_out_lib_types([T|Ts],FTs) :-
    ( not_lib_type(T) ->
        FTs = [T|FTs0]          
    ; FTs = FTs0
    ),
    filter_out_lib_types(Ts,FTs0).

not_lib_type(T) :- is_param_type_symbol(T), !.
not_lib_type(T) :- internally_defined_type_symbol(T,_), !.
not_lib_type(T) :- is_user_defined_type_symbol(T), !.

get_necessary_param_renamings([],Rules,Rules).
get_necessary_param_renamings([T|Ts],Rules0,Rules) :-
    ( param_type_symbol_renaming(Ren,T) ->
        Rules1 = [param_type_symbol_renaming(Ren,T)|Rules0] % TODO: must be before typedef rules!
    ; Rules1 = Rules0
    ),
    get_necessary_param_renamings(Ts,Rules1,Rules).

%% get_necessary_rules_non_param(Types,Rules) :-
%%      remove_param_types(Types,NParamTypes),
%%      get_necessary_rules(NParamTypes,Rules).
%% 
%% remove_param_types([],[]).
%% remove_param_types([T|Ts],NParam) :-
%%      ( param_type_symbol_renaming(_,T) ->
%%        NParam = NParam1
%%      ; NParam = [T|NParam1]
%%      ),
%%      remove_param_types(Ts,NParam1).

:- data tmp_param_type_symbol_renaming/2.
:- data tmp_tyren/2. % temporary type renaming
:- data tmp_tydef/2. % temporary type definition
:- data tmp_parren/2.

clean_tmp_restore :-
    retractall_fact(tmp_param_type_symbol_renaming(_,_)),
    retractall_fact(tmp_tyren(_,_)),
    retractall_fact(tmp_tydef(_,_)),
    retractall_fact(tmp_parren(_,_)).

:- export(restore_types/2).
:- meta_predicate restore_types(pred(1),?).
% Rens is an assoc map of Ty-RenTy pairs that relate the saved type
% name from the dump to the current loaded type. Use this to adjust
% ("relocate") type names from other saved data structures.
:- pred restore_types(ConsultPred,-Rens) + not_fails.
restore_types(ConsultPred,_Rens):-
    clean_tmp_restore,
    read_aux_info(ConsultPred,Fact), % backtracking here
    ( Fact = typedef(Type,Def) -> true
    ; Fact = param_type_symbol_renaming(Def,Type) ->
        % TODO: review this for parametric & predefined types
        assertz_fact(tmp_param_type_symbol_renaming(Def,Type)),
        fail
    ; throw(bug)
    ),
    % if there are none, should have failed at this point
    restore_type_symbol(Type,TypeRen,ParRen),
    % TODO: 'Names' are not available because they are not dumped
    asserta_fact(tmp_tyren(Type,TypeRen)),
    asserta_fact(tmp_tydef(TypeRen,Def)),
    ( ParRen = nopar ->
        true
    ; asserta_fact(tmp_parren(TypeRen,ParRen))
    ),
    fail.
restore_types(_ConsultPred,ORens):-
    retractall_fact(tmp_param_type_symbol_renaming(_,_)), % cleanup
    %
    findall(T1-T2, tmp_tyren_nodups(T1,T2), Rens0),
    retractall_fact(tmp_tyren(_,_)),
    sort(Rens0,Rens1),
    ord_list_to_assoc(Rens1,Rens),
    %
    findall(T-D, tmp_tydef(T,D), TyDefs),
    retractall_fact(tmp_tydef(_,_)),
    % assert renamed types before comparing, the types need to be loaded in the db
    insert_renamed_type_defs(TyDefs,Rens),
    %
    ( % (failure-driven loop)
      current_fact(tmp_parren(T,Def)),
        assert_just_param_renaming(Def,T),
        fail
    ; true
    ),
    filter_relevant_rens(Rens1,RRens),
    ord_list_to_assoc(RRens,ORens), % output renaming
    % (rename back to the type definitions that contained duplicated types)
    findall(T1-T2, tmp_tyren(T1,T2), RensBack),
    sort(RensBack,RensBack_s),
    ord_list_to_assoc(RensBack_s,RensBackDict),
    ( % (failure-driven loop)
      member(Ty, TyDefs),
        retract_fact(typedef(Ty,TyDef)),
        rename_typedef(TyDef,RensBackDict,TyDefR),
        assertz_fact(typedef(Ty,TyDefR)),
        fail
    ; true
    ),
    % remove unused types, safe because we renamed back before
    ( % (failure-driven loop)
      retract_fact(tmp_tyren(Ty,_)),
        retractall_fact(typedef(Ty,_)),
        fail
    ; true
    ).

% removing unused restored type definition and marking new definitions to be renamed back
filter_relevant_rens([],[]).
filter_relevant_rens([Ty1-Ty2|Rs],Rens) :-
    ( dz_equivalent_types(Ty1,Ty2) -> % duplicated type definition
        Rens = Rens0,
        assertz_fact(tmp_tyren(Ty2,Ty1))
    ;   Rens = [Ty1-Ty2|Rens0]
    ),
    filter_relevant_rens(Rs,Rens0).

tmp_tyren_nodups(Ty,TyRen) :-
    tmp_tyren(Ty,TyRen), Ty \= TyRen.

:- meta_predicate read_aux_info(pred(1),?).
read_aux_info(ConsultPred,Fact) :-
    ConsultPred(Fact),
    ( Fact = typedef(_,_) -> true
    ; Fact = param_type_symbol_renaming(_,_) -> true
    ; !, % stop reading otherwise
      fail
    ).

restore_type_symbol(Type,RenType,Def) :-
    is_param_type_symbol(Type),
    tmp_param_type_symbol_renaming(Def,Type),!,
    ( param_type_symbol_renaming(Def,RenType) ->
       true
    ; new_param_type_symbol(RenType)
    ).
restore_type_symbol(Type,RenType,nopar) :-
    is_param_type_symbol(Type),!,
    new_param_type_symbol(RenType).
%       display(restore_type_symbol_FAIL(Type)),nl.
restore_type_symbol(Type,RenType,nopar) :-
    internally_defined_type_symbol(Type,_),!,
    new_type_symbol(RenType).
restore_type_symbol(Type,Type,nopar).

insert_renamed_type_defs([],_).
insert_renamed_type_defs([TypeRen-Def|TypeDefs],Rens):-
    rename_typedef(Def,Rens,RenDef),
    insert_rule(TypeRen,RenDef),
    insert_renamed_type_defs(TypeDefs,Rens).

rename_typedef([],_,[]).
rename_typedef([D|Def],Rens,[RD|RenDef]):-
    ( get_assoc(D,Rens,RD0) ->
        RD = RD0
    ; compound_pure_type_term(D, Comp, _, _) ->
        Comp =.. [Fct|Args],
        rename_typedef(Args,Rens,RenArgs),
        RenComp =.. [Fct|RenArgs],
        construct_compound_pure_type_term(RenComp, RD)
    ; RD = D
    ),
    rename_typedef(Def,Rens,RenDef).

% ===========================================================================
%! # Auxiliary

% :- pred insert(+Set1, +Element, -Set2, -Member)
insert([], Element, [Element],no).
insert([Head|Tail], Element, Set, Member) :-
    compare(Order, Head, Element),
    insert_comp0(Order, Head, Tail, Element, Set, Member).

insert_comp0(<, Head, Tail, Element, [Head|Set], Member) :-
    insert(Tail, Element, Set, Member).
insert_comp0(=, Head, Tail, _, [Head|Tail], yes).
insert_comp0(>, Head, Tail, Element, [Element,Head|Tail], no).
