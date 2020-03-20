% (included from typeslib.pl)
% TODO: document, merge into other file?

% Begin equal to non-failure analysis.

%% Operations on type assignments.

% TODO: make it a special case of dz_equivalent_types/2?
% A type is equivalent to top, either if it is top, or is defined as top.  
equivalent_to_top_type(Type):- 
    is_type_param_symbol(Type),!,
    fail.
equivalent_to_top_type(Type):- 
    top_type(Type),
    !.
equivalent_to_top_type(Type):-
    non_par_rule_type_symbol(Type),
    get_NO_par_type_definition(Type, [Type1]),
    top_type(Type1).

 %% equivalent_to_top_type(Type):- 
 %%     set_top_type(TopType),
 %%     dz_type_included(Type, TopType).

% End equal to non-failure analysis.

% Begin Not equal to non-failure analysis.


%% get_compatible_types(+F/+A, +Type, -Type1, -RestTypes).
%% F/A: functor/arity of the subtype searched.
%% Type: Type in which the subtype is searched.
%% Type1: subtype of Type with functor/arity F/A.
%% RestTypes: rest of types in the definition of Type. It's a list.
%% Preconditions:
%% TermAri > 0
%% Comments: Type1 and the types in RestTypes are a partition of Type
%%           (this means that they are disjoint). Fails if there is
%%           no subtype which is a compound pure type term in Type,
%%           in particular, if type is top, bottom, or a base type symbol.
%%          
%%  IMPORTANT: It is possible to write an specialized version assuming
%%  that the rules are unfolded (or simplified without bottom, and
%%  top). This version which does not expand the user defined type symbolS.

get_compatible_types(TermFun/TermAri, Type, _Seen, CompType):-
    compound_pure_type_term(Type, _Term, Name, Arity),
    !,
    Name = TermFun, 
    Arity = TermAri,
    CompType = [Type].
get_compatible_types(TermFun/TermAri, Type, Seen, CompTypes):-
    non_par_rule_type_symbol(Type),
    !,
    get_compatible_types_from_type_symbol(TermFun/TermAri, Type, Seen, CompTypes).
get_compatible_types(TermFun/TermAri, Type, _Seen, [CompType]):-
    ground_type(Type),
    !,
    create_compound_with_ground_args(TermAri, TermFun, CompType).
get_compatible_types(TermFun/TermAri, Type, _Seen, [CompType]):-
    struct_type(Type),
    !,
    create_compound_with_top_args(TermAri, TermFun, CompType).
get_compatible_types(TermFun/TermAri, Type, _Seen, [CompType]):-
    var_type(Type), % TODO:[new-resources] support for etermsvar
    !,
    create_compound_with_var_args(TermAri, TermFun, CompType).

create_compound_with_top_args(TermAri, TermFun, CompType):-
    create_top_sequence(TermAri, TopArgs),
    Compound =.. [TermFun|TopArgs],
    construct_compound_pure_type_term(Compound, CompType).

create_compound_with_ground_args(TermAri, TermFun, CompType):-
    create_ground_sequence(TermAri, GndArgs),
    Compound =.. [TermFun|GndArgs],
    construct_compound_pure_type_term(Compound, CompType).

% TODO:[new-resources] support for etermsvar
create_compound_with_var_args(TermAri, TermFun, CompType):-
    create_var_sequence(TermAri, VarArgs),
    Compound =.. [TermFun|VarArgs],
    construct_compound_pure_type_term(Compound, CompType).

get_compatible_types_from_type_symbol(_, Type, Seen, _CompTypes):-
    member_0(Type, Seen),
    !,
    fail.     
get_compatible_types_from_type_symbol(TermFun/TermAri, Type, Seen, CompTypes):-
    get_NO_par_type_definition(Type, Defin),
    get_compatible_types_from_union(Defin, TermFun/TermAri, [Type|Seen], CompTypes).

get_compatible_types_from_union([], _, _Seen, []):-!.
get_compatible_types_from_union([Type|TypUnion], TermFun/TermAri, Seen, CompTypes):-
    ( get_compatible_types(TermFun/TermAri, Type, Seen, CTypes) ->
        append(CTypes, RestCompTypes, CompTypes)
    ; CompTypes = RestCompTypes
    ),
    get_compatible_types_from_union(TypUnion, TermFun/TermAri, Seen, RestCompTypes).

%%

type_intersection_2(Type1, Type2, Intersect):-
    dz_type_included(Type1, Type2),
    !,
    Intersect = Type1.
type_intersection_2(Type1, Type2, Intersect):-
    dz_type_included(Type2, Type1),
    !,
    Intersect = Type2.
type_intersection_2(Type1, Type2, Intersect):-
    debug_message("Performing full intersection of ~q and ~q.", [Type1, Type2]), % TODO: remove
    pp_type_intersection(Type1, Type2, Intersect),
    debug_message("Intersection of ~q and ~q is ~q.", [Type1, Type2, Intersect]). % TODO: remove
 %% type_intersection_2(Type1, Type2, Intersect):-
 %%     Intersect = Type2,
 %%     warning_message("No inclusion relationship between types ~q and ~q.",[Type1, Type2]),
 %%     warning_message("Assumed that the intersection is ~q. This can be improved by performing full intersection.", [Intersect]).
   

pp_type_intersection(Typ1, Typ2, Inter):-
    typeslib:type_intersection(Typ1, Typ2, Intersec), 
    !, 
    ( is_empty_type(Intersec) -> 
        clean_after_empty_pp_type_intersection,
        set_bottom_type(Inter)
    ; simplify_types_after_pp_type_intersection,
      replace_one_equiv_type(Intersec, Inter)
    ).

type_escape_term_list([Arg|LitArgs], [EscArg|RArgs]):- !,
     escaped_type(Arg, EscArg),
     type_escape_term_list(LitArgs, RArgs).
type_escape_term_list([], []).

%% perform_one_type_unification(Unification, Subst, OutSubst):-
%%       get_data_from_substitution(Subst, Var_List, Type_List, Term_List, _TypeAss),
%%       arg(1, Unification, A1),
%%       arg(2, Unification, A2),
%%       % perform_unification(A1, A2),
%%       (A1 = A2 ->
%%             generate_a_type_assignment(Type_List, Term_List, TypeAss1),
%%             rewrite_terms_as_pure_type_terms(Term_List, TypeAss1, PTypeList),
%%             rewrite_as_type_symbols(PTypeList, TypeSymbol_List),
%%             create_a_type_substitution(Var_List, TypeSymbol_List, Term_List, TypeAss1, OutSubst)
%%             ;
%%             set_bottom_substitution(Var_List, OutSubst)).
%% 
%% rewrite_terms_as_pure_type_terms([], _TypeAss, []):-!.
%% rewrite_terms_as_pure_type_terms([Term|TermList], TypeAss, [PureTypeTerm|PTypeList]):-
%%     rewrite_one_term_as_a_pure_type_term(Term, TypeAss, PureTypeTerm),
%%     rewrite_terms_as_pure_type_terms(TermList, TypeAss, PTypeList).
%% 
%% :- pred rewrite_one_term_as_a_pure_type_term(+Term, +TypeAss, -PureTypeTerm)
%% 
%% # "Creates the Pure Type Term @var{PureTypeTerm} by rewriting
%%  @var{Term} as a type term (possibly with variables) and replacing each
%%  variable in this type term by its type in @var{TypeAss}.".
%% 
%% rewrite_one_term_as_a_pure_type_term(Term, TypeAss, PureTypeTerm):-
%%     escaped_type(Term, TypeTerm),
%%     replace_vars_by_types(TypeAss, TypeTerm, PureTypeTerm).
%% 
%% get_data_from_substitution(Substitution, Var_List, Type_List, Term_List, TypeAss):-
%%      Substitution = typesubs(Var_List, Type_List, Term_List, TypeAss).
%% 
%% set_bottom_substitution(Var_List, Substitution):-
%%      Substitution = typesubs(Var_List, '$bottom', '$bottom', '$bottom').
%% 
%% bottom_substitution(Substitution):-
%%      Substitution = typesubs(_Var_List, Type_List, _Term_List, _TypeAss),
%%      Type_List == '$bottom'.
%% 
%% create_a_type_substitution(Var_List, Type_List, Term_List, TypeAss, Substitution):-
%%      Substitution = typesubs(Var_List, Type_List, Term_List, TypeAss).
%% 
%% 
%% :- pred one_term_2_pure_type_term(Term, Var_List, Type_List, PureTypeTerm)
%% 
%% # "Create a pure type term (i.e. with no variables) by replacing the
%%    variables in @var{Term} by their types. @var{Var_List} is a list
%%    with all the variables of the clause, and @var{Type_List} is the list of
%%    their corresponding types".
%% 
%% one_term_2_pure_type_term(Term, Var_List, Type_List, PureTypeTerm):-
%%         two_lists_to_type_ass(Var_List, Type_List, TypeAss),
%%         rewrite_one_term_as_a_pure_type_term(Term, TypeAss, PureTypeTerm).
%% 
%% two_lists_to_type_ass([], [], []):-!.
%% two_lists_to_type_ass([Var|Vars], [Type|Types], [Var:Type|TypeAss]):-
%%      two_lists_to_type_ass(Vars, Types, TypeAss).

% End not equal to non-failure analysis.
