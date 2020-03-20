% (included file)

% :- doc(title, "deftypes operations").
% :- doc(author, "Pawel Pietrzak").
% 
% :- doc(module, "This module implements type operations where only
%    library types, user-defined types and instances of parametric rules
%    are in the domain.  An abstrat sustitution is list of Var:Type
%    elements, where Var is a variable and Type is a pure type term
%    @cite{Dart-Zobel}.").

% ---------------------------------------------------------------------------

:- use_module(engine(internals), [module_concat/3]).

:- use_module(library(lists), [member/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(lists), [append/3, select/3]).

:- use_module(library(aggregates), [findall/3]).

%% ---------------------------------------------------------------------------

:- data pgm_def_equiv_type/2.
:- data lib_def_equiv_type/2.

:- data pgm_def_subtype_basic/2.
:- data lib_def_subtype_basic/2.

:- data pgm_param_type_hook/3.
:- data lib_param_type_hook/3.

% :- data pgm_functor_types/3. % unused (JFMC)
% :- data lib_functor_types/3. % unused (JFMC)

def_subtype_basic(T1,T2) :- pgm_def_subtype_basic(T1,T2).
def_subtype_basic(T1,T2) :- lib_def_subtype_basic(T1,T2).

def_equiv_type(T1,T2) :- pgm_def_equiv_type(T1,T2).
def_equiv_type(T1,T2) :- lib_def_equiv_type(T1,T2).

param_type_hook(A,B,C) :- pgm_param_type_hook(A,B,C).
param_type_hook(A,B,C) :- lib_param_type_hook(A,B,C).

%% ---------------------------------------------------------------------------
    
:- export(build_defined_types_lattice/0).
build_defined_types_lattice :-
    retractall_fact(pgm_def_subtype_basic(_,_)),
    retractall_fact(pgm_def_equiv_type(_,_)),
    retractall_fact(pgm_param_type_hook(_,_,_)),
    % retractall_fact(pgm_functor_types(_,_,_)),
    get_preprocessing_unit_types(Types),
    keep_interesting_types(Types,[],ITypes),
    def_build_lattice(ITypes).

keep_interesting_types([],Ts,Ts).
keep_interesting_types([T|Ts],ITs1,Out) :-
    ( is_interesting_type(T,build) ->
        ITs = [T|ITs1]
    ; ITs = ITs1
    ),
    keep_interesting_types(Ts,ITs,Out).

% :- export(is_interesting_type/1).
is_interesting_type(term,_) :-!.
is_interesting_type(bot,_) :-!.
is_interesting_type(T,_) :-
    base_type_symbol(T),!.
is_interesting_type(T,Mode) :-
    ( param_type_symbol_renaming(Head,T)
    ; param_type_symbol_renaming(T,_), Head = T
    ),!,
    param_type_hook(Head,[V|_],_),
    is_interesting_type(V,Mode).
is_interesting_type(T,Mode) :-
    typeslib_interesting_type(T, Mode).

%% functor_types(F,Ts,B) :-
%%      ( pgm_functor_types(F,Ts1,B); Ts1 = [] ),
%%      ( lib_functor_types(F,Ts2,B); Ts2 = [] ),  
%%      append(Ts1,Ts2,Ts).  

% build the basic graph, can be improved 
def_build_lattice(Ts0) :-
    add_paramdefs(ParamDefs),
    append(ParamDefs,Ts0,Ts05),
    del_equivalent([term|Ts05],Ts), % sort of chapuza
    select(T0,Ts,Ts1),
    select(T1,Ts1,Ts2),
    T1 \= bot,
    dz_type_included(T0,T1), 
    \+ ( member(T2,Ts2), dz_type_included(T2,T1), dz_type_included(T0,T2)),
    assertz_fact(pgm_def_subtype_basic(T0,T1)),
    fail.
def_build_lattice(_) :-
    def_subtype_basic(T,_),
    \+ def_subtype_basic(_,T),
    T \= bot,
    assertz_fact(pgm_def_subtype_basic(bot,T)),
    fail.
%% unused (JFMC)
% def_build_lattice(Types) :-
%     def_create_defined_types_filters_x(Types).
def_build_lattice(_).

%remove_irrelevant_params([T|Ts],Out) :-
%       ( param_to_remove(T) ->
%         Out = Out1
%       ; Out = [T|Out1]
%       ),
%       remove_irrelevant_params(Ts,Out1).
%remove_irrelevant_params([],[]).

%param_to_remove(P) :-
%       param_type_symbol_renaming(Head,P),
%       param_type_hook(Head,Vs,_),
%       \+ keep_interesting_types(Vs,Vs).

%% unused (JFMC)
% def_create_defined_types_filters_x([]).
% def_create_defined_types_filters_x([T|Ts]) :-
%     prlb(T,Fs),
%     def_add_to_each_functor(Fs,T),
%     def_create_defined_types_filters_x(Ts).

%% unused (JFMC)
% def_add_to_each_functor([],_).
% def_add_to_each_functor([F|Fs],T) :-
%     ( retract_fact(pgm_functor_types(F,Ts,_)) ->
%         append(Ts,[T],Ts1)
%     ; Ts1 = [T]
%     ),
%     ( native_type_symbol(F) ->
%         M = basic
%     ; M = rule
%     ),
%     assertz_fact(pgm_functor_types(F,Ts1,M)),
%     def_add_to_each_functor(Fs,T).

add_paramdefs(ParamDefs) :-
    findall(P,add_one_paramdef(P),ParamDefs).

add_one_paramdef(ParSymb) :-
    paramtypedef(Head,_),
    varset(Head,HVs),
    copy_term(Head,CHead),
    varset(CHead,CHVs),
    ground_params_to_top(CHVs),
    assert_param_type_rule_instance(CHead,ParSymb),
    assertz_fact(pgm_param_type_hook(Head,HVs,ParSymb)).
    
ground_params_to_top([]).
ground_params_to_top([term|Ps]) :-
    ground_params_to_top(Ps).

del_equivalent([],[]).
del_equivalent([T|Ts],[T|NoEq]) :-
    del_eq(T,Ts,Ts1),
    del_equivalent(Ts1,NoEq).

del_eq(_T,[],[]).
del_eq(T,[T1|Ts],NoEq) :-
    ( dz_type_included(T,T1), dz_type_included(T1,T) ->
        assertz_fact(pgm_def_equiv_type(T,T1)),
        NoEq = NoEq1
    ; NoEq = [T1|NoEq1]
    ),
    del_eq(T,Ts,NoEq1).

get_param_head(TypeSymb,Head) :-
    ( atom(TypeSymb) ->
        get_canonical_type(TypeSymb,Can),
        param_type_symbol_renaming(Head,Can)
    ; Head = TypeSymb
    ).

:- export(def_subtype/2).
def_subtype(T1,T2) :-
    contains_type_param(T2), % TODO: contains_type_param/2 can be slow, memoize?
    param_matching_mode(on),!,
    dz_type_included(T1,T2).
def_subtype(_,term) :-!.
def_subtype(bot,_) :-!.
% both parametric types
def_subtype(T1,T2) :-
    get_param_head(T1,Par1),
    get_param_head(T2,Par2),!,
    param_type_hook(Par1,Vs1,PT),
    param_type_hook(Par2,Vs2,PT), % same param rule?
    def_subtype_all(Vs1,Vs2).
% first one parametric
def_subtype(T1,T2) :-
    param_type_symbol_renaming(Par1,T1),
    \+ def_subtype_basic(T1,_),
    \+ def_subtype_basic(_,T1), !, % not in the lattice
    param_type_hook(Par1,_,PT),
    def_subtype(PT,T2).
def_subtype(T1,T2) :-
    get_canonical_type(T1,CT1),
    get_canonical_type(T2,CT2),
    def_subtype_x(CT1,CT2),!.

def_subtype_all([],[]).
def_subtype_all([T1|Ts1],[T2|Ts2]) :-
    def_subtype(T1,T2),
    def_subtype_all(Ts1,Ts2).

get_canonical_type(T,CT) :-
    def_equiv_type(CT,T),!.
get_canonical_type(T,CT) :-
    base_type_symbol(T),
    module_concat(basic_props,T,CT),!. % TODO: sure?
% not quite right...
get_canonical_type(T,CT) :- \+ keep_as_canonical(T), !,
    CT = term.
get_canonical_type(T,T).

keep_as_canonical(T) :- number(T).
keep_as_canonical(^(_)).
keep_as_canonical([]).
keep_as_canonical([_|_]).
keep_as_canonical(T) :- is_interesting_type(T,canonical).
keep_as_canonical(T) :- internally_defined_type_symbol(T,1).

def_subtype_x(T,T) :-!.
def_subtype_x(T1,T2) :-
    def_subtype_basic(T1,T2),!.
def_subtype_x(T1,T2) :-
    def_subtype_basic(T1,T3),
    def_subtype(T3,T2).

:- export(def_type_glb/3).
% GLB is not quite safe...
% keep the old version for the time being...
def_type_glb(TY,TX,T) :-
    type_intersection_2(TY,TX,T_tmp),
    def_type_approx_as_defined(T_tmp,T),!.

:- export(def_type_lub/3).
def_type_lub(_,term,term):-!.
def_type_lub(term,_,term):-!.
% not quite complete yet...
def_type_lub(T1,T2,LUB) :-
    def_subtype(T1,T2),
    def_subtype(T2,T1),
    !, 
    ( T1 @> T2 -> LUB = T2; LUB = T1). 
def_type_lub(T1,T2,LUB) :-
    ( def_subtype(T1,T2), LUB=T2
    ; def_subtype(T2,T1), LUB=T1
    ),
    !.
def_type_lub(T1,T2,T3) :-
    get_param_head(T1,Par1),
    get_param_head(T2,Par2),
    param_type_hook(Par1,Vs1,PT),
    param_type_hook(Par2,Vs2,PT), % same param rule?
    !,
    lub_all(Vs1,Vs2,VsLUB),
    param_type_hook(ParLUB,VsLUB,PT),
    assert_param_type_rule_instance(ParLUB,T3).
def_type_lub(T1,T2,LUB) :-
    get_canonical_type(T1,CT1),
    gen_suptype(CT1,Sup1),
    def_subtype(T2,Sup1),!,
    LUB = Sup1.
def_type_lub(_T1,_T2, term).

lub_all([],[],[]).
lub_all([T1|Ts1],[T2|Ts2],[T3|Ts3]) :-
    def_type_lub(T1,T2,T3),
    lub_all(Ts1,Ts2,Ts3).

gen_suptype(T,T).
gen_suptype(T,Sup) :-
    def_subtype_basic(T,Sup1),
    gen_suptype(Sup1,Sup).
gen_suptype(T,S) :-
    get_param_head(T,Par),
    param_type_hook(Par,[V|_],PT),
    gen_subtype(V,SupV),
    param_type_hook(S0,[SupV|_],PT),
    add_param_rule_if_needed(S0,S).

gen_subtype(T,T).
gen_subtype(T,Sub) :-
    def_subtype_basic(Sub1,T),
    gen_subtype(Sub1,Sub).

add_param_rule_if_needed(T,T1) :-
    atom(T),!,
    T1 = T.
add_param_rule_if_needed(T,PT) :-
    param_type_symbol_renaming(T,PT),!.
add_param_rule_if_needed(T,PT) :-
    assert_param_type_rule_instance(T,PT).

% ---------------------------------------------------------------------------
:- export(def_equivalent_types/2).
def_equivalent_types(T0,T1) :-
    T0 == T1,!.
def_equivalent_types(T0,T1) :-
    ( def_equiv_type(T0,T1) ; def_equiv_type(T1,T0) ),!.
def_equivalent_types(T0,T1) :-
    def_subtype(T0,T1),
    def_subtype(T1,T0).

% ---------------------------------------------------------------------------
% defined types  "widening" starts here
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- export(def_type_approx_as_defined/2). % TODO: different than typeslib:approx_as_defined/2, why?
def_type_approx_as_defined(Type,ApproxType):-
    get_canonical_type(Type,CT),
    ( CT == term ; def_subtype_basic(CT,_) ),% def_subtype_basic(_,CT) ),
    !,
    ApproxType = Type.
def_type_approx_as_defined(Type,ApproxType):-
    is_type_param_symbol(Type),
    param_matching_mode(on),!,
    ApproxType = Type.
def_type_approx_as_defined(Type,ParType):-
    def_match_one_rule_as_parametric(Type,ParType),!.
def_type_approx_as_defined(Type,ApproxType):-
    get_canonical_type('basic_props:term',MinSoFar),
    find_min_in_lattice(Type,MinSoFar,ApproxType),!.

find_min_in_lattice(Type,MinSoFar,Min) :-
    def_subtype_basic(New,MinSoFar),
    dz_type_included(Type,New),!,
    find_min_in_lattice(Type,New,Min).
find_min_in_lattice(_,Min,Min).

def_match_one_rule_as_parametric(Type, NewType):-
    param_type_symbol_renaming(_,Type),
    !,
    NewType = Type.
def_match_one_rule_as_parametric(Type, NtypSymbol1):-
    get_type_definition(Type,Def),
    TypeDef = typedef(Type,Def),
    paramtypedef(Head,Body), 
    ParRule = paramtypedef(Head,Body), 
    copy_term(ParRule, Rule),
    TypeDef = typedef(NTypeSymbol, NDefin), non_par_rule_type_symbol(NTypeSymbol), % TODO: non_par_rule_type_symbol/1 check needed?
    Rule = paramtypedef(PTypeSymbol, PDefin), par_rule_type_symbol(PTypeSymbol), % TODO: par_rule_type_symbol/1 check needed?
%        order_type_defin(PDefin, OrPDefin), !, 
    def_match_defin(NDefin, PDefin, PDefin), 
    ground(PTypeSymbol),
    assert_param_type_rule_instance(PTypeSymbol, Cand),
    dz_type_included(NTypeSymbol, Cand),
    !,
    assert_and_propagate_type_equivalence(NTypeSymbol, Cand),
    check_max_depth(Cand,3,NtypSymbol1).

def_match_defin([], RestPDefin, PDefin) :-
    RestPDefin \= PDefin, % some parts of the parametric rule have
                          % been matched
    varset(RestPDefin,FreeParams),
    bind_to_bot(FreeParams).
def_match_defin([NType|NDefin], PDefin, OrigPDefin):-
    def_match_with_some_type(PDefin, NType, RestPDefin),
    def_match_defin(NDefin, RestPDefin, OrigPDefin).

def_match_with_some_type([PType|PDefin], NType, PDefin):-
    def_type_match(NType, PType), !.
def_match_with_some_type([PType|PDefin], NType, [PType|RestPDefin]):-
    def_match_with_some_type(PDefin, NType, RestPDefin).

def_type_match(NType, PType):-
    var(PType),
    def_type_approx_as_defined(NType,DefType),
    !,
    PType = DefType.
def_type_match(NType, PType):- 
    NType == PType,
    !.
def_type_match(NType, PType):-
    compound_pure_type_term(NType, NComp, Name, Arity),
    compound_pure_type_term(PType, PComp, Name, Arity), % PType is not a variable.
    !,
    def_compound_type_match(Arity, NComp, PComp).
def_type_match(_NType, PType):-
    % non_par_rule_type_symbol(NType),
    par_rule_type_symbol(PType), !.
def_type_match(NType, PType):-
    non_par_rule_type_symbol(NType),
    non_par_rule_type_symbol(PType).

% TODO: share with compound_type_match/3
def_compound_type_match(0, _NComp, _PComp):-!.
def_compound_type_match(ArgNum, NComp, PComp):-
    ArgNum > 0, 
    arg(ArgNum, NComp, NArg),
    arg(ArgNum, PComp, PArg),
    def_type_match(NArg, PArg),
    NArgNum is ArgNum - 1,
    def_compound_type_match(NArgNum, NComp, PComp).

% % ---------------------------------------------------------------------------
% % a facility to output the type lattice in the DOT format
% 
% :- use_module(engine(stream_basic)).
% :- use_module(library(format), [format/3]).
% 
% :- export(gen_graph/0). % TODO: disable (debugging)
% gen_graph :-
%     open('type_graph.dot',write,Out),
%     gen_gr(Out).
% 
% gen_gr(Out) :-
%     format(Out,"digraph G {\nordering = out;\n",[]),
%     def_subtype_basic(A,B),
%     format(Out,"\"~w\" -> \"~w\"\n ",[B,A]),
%     fail.
% gen_gr(Out) :-
%     format(Out,"}\n",[]),
%     close(Out).

