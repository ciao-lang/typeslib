% (included from typeslib.pl)
% TODO: document, merge into other file?

:- use_module(library(assertions/assrt_lib), [
    prop_apply/3,prop_unapply/3,prop_argvar/2]).

%% :- module(regtype_rules,
%%      [ % type symbols
%%          internally_defined_type_symbol/2,
%%          legal_user_type_pred/1,
%%          new_type_symbol/1,
%%          new_param_type_symbol/1,
%%          rule_type_symbol/1,
%%          par_rule_type_symbol/1,
%%          non_par_rule_type_symbol/1,
%%          type_symbol/1
%% 
%% 
%%      ],
%%      [ assertions, basicmodes, regtypes ] ).
%% 
%% 
%% :- doc(module,"This module contains the operations required for a 
%%      lattice of regular types formed with the native types plus
%%      types defined by regular rules. Rules can also be parametric.").

% ========================================================================

:- regtype legal_user_type_pred(Prop)
   # "@var{Prop} is a @tt{(possibly parametric) type} that can be defined
      by the user. @var{Prop} is the head of the predicate definition.".

legal_user_type_pred(Prop):-
    prop_unapply(Prop, Type, _),
    rule_type_symbol(Type).

% (exported)
% Decompose a prop literal Prop into a type Type and its variable argument Arg
prop_to_type(Prop, Type, Arg) :-
    nonvar(Prop),
    ( functor(Prop, F, 1) ->
        % (old comment from is_a_type_declaration/3:)
        %   WARNING!: any declaration of arity 1 is considered a type.
        %   Perhaps we should escape type symbols instead of functors.
        Type = F,
        arg(1, Prop, Arg)
    ; % If Prop is a parametric type, use its equivalent non-parametric type symbol
      prop_unapply(Prop, ParTypeSymbol, Arg0),
      param_type_symbol_renaming(ParTypeSymbol, Type),
      Arg = Arg0
    ).

:- regtype rule_type_symbol(Type)
   # "@var{Type} is a @tt{(possibly parametric) type symbol}  
      that should be defined by a (possibly parametric) type rule.".

rule_type_symbol(Type):-
    ( non_par_rule_type_symbol(Type)
    ; par_rule_type_symbol(Type)
    ).

% ========================================================================
% TYPE SYMBOL COUNTER OPERATIONS

% TODO: better documentation for type_param vs param_type    

:- data typ_sym_counter/1.
:- data lib_typ_sym_counter/1. %% For libraries.

:- data param_typ_sym_counter/1.
:- data lib_param_typ_sym_counter/1. %% For libraries.

:- data typ_param_sym_counter/1.
:- data lib_typ_param_sym_counter/1. %% For libraries.

:- pred new_type_symbol(-NewTyp)
   # "Creates a new (non-parametric) type symbol (using the value of the
      type symbol counter) and instantiates @var{NewTyp} to it. The type
      symbol counter is incremented by 1.".

new_type_symbol(NewTyp):-
    new_counter_value(typ_sym, N),
    name(N, NName),
    append("rt", NName, TypName),
    name(NewTyp, TypName).

internally_defined_type_symbol(F,1):- % TODO: weak?
    atom(F),
    atom_concat(rt,N,F),
    atom_number(N,_),
    !.
internally_defined_type_symbol(F,1):-
    is_type_param_symbol(F).

:- pred new_param_type_symbol(-NewTyp)
   # "Creates a new (parametric) type symbol (using the value of the type
      symbol counter) and instantiates @var{NewTyp} to it. The type symbol
      counter is incremented by 1.".

new_param_type_symbol(NewTyp):-
    new_counter_value(param_typ_sym, N),
    name(N, NName),
    append("pt", NName, TypName),
    name(NewTyp, TypName).

is_param_type_symbol(F):- % TODO: weak?
    atom(F),
    atom_concat(pt,N,F),
    atom_number(N,_),
    !.

% TODO: document, this is introduced in code like
%   :- entry p(X,Y) : ta(X,T).
% but those param types are never reversed in the output.
:- pred new_type_param_symbol(-NewTyp)
   # "Creates a new (@em{hidden}) type parameter symbol.".

new_type_param_symbol(Type):-
    new_counter_value(typ_param_sym, N),
    name(N, NName),
    append("tp", NName, TypeName),
    name(Type, TypeName).

is_type_param_symbol(Type) :- % TODO: weak?
    atom(Type),
    atom_concat(tp, N, Type),
    atom_number(N, _),
    !.

% ---------------------------------------------------------------------------

% TODO: see accept_type/1, add type props
is_user_defined_type_symbol(T) :- typeslib_is_user_type(T).

%----------------------------------------------
% END OF TYPE SYMBOL COUNTER OPERATIONS

% CREATION OF TYPES.

%% % This gives the "analyzable" pred definitions of the basic types
%% % (whose intended definitions are in basictypes)
%% % Does not work!!!! (because of magic transformation)
%% basic_types_pred_defs(fdtypes,[]).
%% %% basic_types_pred_defs(fdtypes,
%% %%   [ (clause(term(_),true),clid),
%% %%     (clause(gnd(X),ground(X)),clid),
%% %%     (clause(num(X),number(X)),clid),
%% %%     (clause(atm(X),atom(X)),clid),
%% %%     (clause(flt(X),float(X)),clid),
%% %%     (clause(struct(X),compound(X)),clid),
%% %%   %??  (clause(var(X),var(X)),clid),
%% %%   % These four do belong in fdtypes
%% %%   % (clause(rat(X),??),clid),
%% %%   % (clause(int(X),??),clid),
%% %%   % (clause(nnegint(X),??),clid),
%% %%   % (clause(anyfd(X),??),clid),
%% %%     (clause(regtype(_,_),true),clid)
%% %%   ]).
%% 
%% basic_types_pred_defs(regtypes,
%%      [ (clause(term(_),true),clid),
%%        (clause(gnd(X),ground(X)),clid),
%%        (clause(num(X),number(X)),clid),
%%        (clause(atm(X),atom(X)),clid),
%%        (clause(flt(X),float(X)),clid),
%% %      (clause(struct(X),compound(X)),clid),  compund not a builtin
%%        (clause(struct(X),term(X)),clid),
%%        (clause(rat(X/Y),(integer(X),integer(Y))),clid),
%%        (clause(int(X),integer(X)),clid),
%%        (clause(nnegint(X),(integer(X),X>=0)),clid),
%%        (clause(anyfd(_),true),clid),
%%      % A VERY UGLY HACK, I KNOW (PBC)
%%        (clause('SYSCALL'(_),true),clid)
%%      ]).
%% 
%% basic_types_pred_defs(regtypes,
%%      [ (clause(term(_),true),clid),
%%        (clause(gnd(_),true),clid),
%%        (clause(num(_),true),clid),
%%        (clause(atm(_),true),clid),
%%        (clause(flt(_),true),clid),
%%        (clause(struct(_),true),clid),
%%        (clause(rat(X/Y),(integer(X),integer(Y))),clid),
%%        (clause(int(X),integer(X)),clid),
%%        (clause(nnegint(X),(integer(X),X>=0)),clid),
%%        (clause(anyfd(X),true),clid),
%%      % A VERY UGLY HACK, I KNOW (PBC)
%%        (clause('SYSCALL'(_),true),clid)
%%      ]).


% TYPE RULE REPRESENTATION AND RELATED PROCEDURES  

% TODO: same?
% Change this? 
get_rule_type_predicate(typedef(TypSymbol, _Defin), TypSymbol).

get_rule_type_symbol(typedef(TypSymbol, _Defin), TypSymbol).

%% %
%% %delete?
%% :- pred defined_type_symbol(+Type, -Defin)
%% 
%% # "If @var{Type} is a rule type symbol that is defined by an
%%    (asserted) type rule, then @var{Defin} is its definition. Otherwise
%%    @var{Defin} is bound to the atom @tt{nodef}. It always succeeds".
%% 
%% defined_type_symbol(Type, Defin):-
%%     (rule_type_symbol(Type) -> 
%%       (find_type_defin(Type, Defin1) -> 
%%                  Defin = Defin1; 
%%                  Defin = nodef)
%%      ; Defin = nodef).
%% 
%% :- pred get_NP_typedef_default_bot(+Type, -Defin)
%% 
%% # "If @var{Type} is a rule type symbol that is defined by an
%%    (asserted) type rule, then @var{Defin} is its definition. Otherwise
%%    find the definition of a type equivalent to @var{Type}. If there is
%%    not definition for none of the equivalent types, then a warning
%%    message is issued and the definition @var{Defin} is unified with
%%    the bottom type [bot].  It always succeeds".
%% 
%% get_NP_typedef_default_bot(Type, Defin):-
%%    (typedef(Type, Defin1) 
%%        -> Defin = Defin1
%%        ; (equiv_type(Type,Type1) % it might be equivalent to another! (PBC)
%%             -> get_NP_typedef_default_bot(Type1, Defin)
%%             ;  definition_not_found_default_bot(Type, Defin))).
%% 
%% definition_not_found_default_bot(Type, Defin):-
%%      Defin = [T],
%%      set_bottom_type(T),
%% %     warning_message("Type ~q not defined, assumed ~q", [Type, T]).
%%      Type=Type.
%% 
%% :- pred pp_find_type_defin(+Type, -Defin)
%% 
%% # "Finds the definition @var{Defin} of @var{Type} in the asserted type
%%    rules.  If there is no type rule defining @var{Type}, then gives a warning
%%    message and returns top type.".
%% 
%% pp_find_type_defin(TypeSymbol, Def):- 
%%    (typedef(TypeSymbol, Def)
%%      -> true
%%       ; definition_not_found(TypeSymbol, Def)).

 %% get_NO_par_type_definition(Type, Defin):-
 %%    (typedef(Type, Defin1) 
 %%        -> Defin = Defin1
 %%        ; (equiv_type(Type,Type1) % it might be equivalent to another! (PBC)
 %%             -> get_NO_par_type_definition(Type1, Defin)
 %%             ; compiler_error(type_undefined(Type)),
 %% %             give any (PBC):
 %% %              Defin = nodef).
 %%           Defin = [G],
 %%           set_top_type(T),
 %%           functor(G,T,1),
 %%           arg(1,Type,X),
 %%           arg(1,T,X) )).

% exist_one_non_par_type_rule(TypeSymbol, Def):-
%      typedef(TypeSymbol, Def). 

% Like typedef/2 but makes sure that rule_type_symbol(Type) holds
% TODO: why is this needed?
get_typedef(Type, Defin):-
    rule_type_symbol(Type),
    typedef(Type, Defin). 

:- pred insert_rule(+TypeSymbol, +TypeDef)
   => non_par_rule_type_symbol * type_disjunction
   # "Asserta a type rule defining @var{TypeSymbol} with the definition 
      @var{TypeDef}.".

insert_rule(TypeSymbol, TypeList):-
    % OLD 21-Dec-98 asserta(typedef(TypeSymbol, TypeList)).
    ( typedef(TypeSymbol,_) ->
        true
    ; assertz_fact(pgm_typedef(TypeSymbol, TypeList))
    ).

remove_rule(TypeSymbol) :-
    retract_fact(pgm_typedef(TypeSymbol, _)).

% (exported)
insert_user_type_pred_def(Prop, Clauses):-
    prop_unapply(Prop, Type, _),
    insert_user_type_rule(Type, Clauses).

insert_user_type_rule(Type, Clauses):-
    pred2par_non_par_rule(Type, Clauses, TypeRule),
    assertz_typedef_or_paramtypedef(TypeRule),
    assertz_fact(pgm_user_type(Type)).

assertz_typedef_or_paramtypedef(typedef(TypeSymbol,TypeList)):-
    \+ typedef(TypeSymbol,_),
    assertz_fact(pgm_typedef(TypeSymbol,TypeList)), !.
assertz_typedef_or_paramtypedef(paramtypedef(TypeSymbol,TypeList)):-
    \+ paramtypedef(TypeSymbol,_),
    asserta_fact(pgm_paramtypedef(TypeSymbol,TypeList)).


:- data pgm_user_type/1. %% For user programs.
:- data lib_user_type/1. %% For libraries.

%% user_type(A):-
%%      pgm_user_type(A).
%% user_type(A):-
%%      lib_user_type(A).

insert_new_type_rule(TypeSymbol,  TypeList):-
    insert_rule(TypeSymbol, TypeList),
    asserta_fact(no_simplified_type(TypeSymbol)).

%% create_type_rule(TypeSymbol, TypeList, TypeRule):-
%%    TypeRule = typedef(TypeSymbol, TypeList).
%% 
%% get_symbol_defin_from_type_rule(TypeRule, TypeSymbol, Defin):-
%%    TypeRule = typedef(TypeSymbol, Defin).

%---------------------------------
% RETRACTION OF TYPE RULES 
%---------------------------------

:- pred retract_rule(+TypeSymbol)
   => non_par_rule_type_symbol
   # "Retracts the type rule defining @var{TypeSymbol}.".

retract_rule(TypSymbol):-
    retract_fact(pgm_typedef(TypSymbol, _)),
    !.
retract_rule(_TypSymbol). % PLG Dec-6-2003
                      % If there is no type rule for TypSymbol, 
                      % then succeeds as before, but
                      % do not raise any error message.
 %% On Dec-6-2003 was:
 %% retract_rule(TypSymbol):-
 %%    error_message("In retract_rule/1: There is no type rule defining ~q. Failing.", 
 %%                  [TypSymbol]).

%
retract_rules([]).
retract_rules([TypSymbol|List]):-
    retract_rule(TypSymbol),
    retract_rules(List).
%
:- pred selective_retract_rules(+Rules)
   => type_rule_list
   # "Retract the type rules defining the type symbols in @var{Rules}.".

selective_retract_rules([typedef(TypSymbol, _Defin)|Types]):-
    retract_rule(TypSymbol),
    selective_retract_rules(Types).
selective_retract_rules([]).

%---------------------------------
% MODIFICATION OF TYPE RULES 
% --------------------------------

assert_unfolded_rules([]).
assert_unfolded_rules([typedef(TypeSymbol, Def)|Rest]):-
    retractall_fact(pgm_typedef(TypeSymbol, _)),
    assertz_fact(pgm_typedef(TypeSymbol, Def)), % assertz or asserta?
    assert_unfolded_rules(Rest).

actualize_rules(RuleList):-
    retract_all_type_rules,
    asserta_type_rule_list(RuleList).

retract_all_type_rules:-
    retractall_fact(pgm_typedef(_, _)). 

%-----------------------------------
% ASSERTION OF TYPE RULES 
% ----------------------------------

:- pred asserta_type_rule_list(+Rules)
   # "Asserta the type rules in @var{Rules}.".

asserta_type_rule_list([typedef(Type, Def)|Types]):-
%       assertz_fact(pgm_typedef(Type, Def)),
    insert_rule(Type, Def),
    asserta_type_rule_list(Types).
asserta_type_rule_list([]).

assert_rules_if_not_exist([typedef(Type, Def)|Types]):-
    ( (typedef(Type, _) ; is_type_param_symbol(Type)) ->
        true
    ; assertz_fact(pgm_typedef(Type, Def))
    ),
    assert_rules_if_not_exist(Types).
assert_rules_if_not_exist([]).

%---------------------------------
% CONSULT OF TYPE RULES 
%---------------------------------

:- pred get_type_definition(+Type, -Defin)
   # "If @var{Type} is a rule type symbol that is defined by an
      (asserted) type rule, then @var{Defin} is its definition. Otherwise
      find the definition of a type equivalent to @var{Type}. If there is
      not definition for none of the equivalent types, then a warning
      message is issued and the definition @var{Defin} is unified with
      the bottom type [bot].  It always succeeds".

%pp:
get_type_definition(Type, Defin):-
    is_type_param_symbol(Type),!,
    ( param_matching_mode(off) ->
        typedef(Type, Defin)
    ; Defin = [Type]
    ).
get_type_definition(Type, Defin):-
    non_par_rule_type_symbol(Type),
    !,
    get_NO_par_type_definition(Type, Defin).
get_type_definition(Type, Defin):-
    par_rule_type_symbol(Type),
    get_par_type_definition(Type, Defin),!.

get_NO_par_type_definition(Type, Defin):-
    ( typedef(Type, Defin1) ->
        Defin = Defin1
    ; equiv_type(Type,Type1) -> 
        % it might be equivalent to another! (PBC)
        % This shouldn't be necessary if all type symbols
        % were replaced by their representants in the 
        % correspondig equivalence class. PLG
        get_type_definition(Type1, Defin)
    ; definition_not_found(Type, Defin)
    ).

get_par_type_definition(Type, Defin):-
    findall(paramtypedef(Type, Defin2), paramtypedef(Type, Defin2), Rules),  
    % TODO: errors here should be runtime checks (bugs)
    ( Rules = [] ->
        compiler_error(param_type_undefined(Type)),
        Defin = nodef
    ; Rules = [Rule1|Rest],
      ( Rest = [] ->
          true 
      ; compiler_error(multiple_type_defin(Type))
      ),
      Rule1 = paramtypedef(Type, Defin)
    ).

definition_not_found(Type, Defin):-
    Defin = [T],
    % set_top_type(T), %% PLG Dec-6-2003
    set_bottom_type(T), %% Now, a type symbol with no defining type rule is considered empty
                     %% (bottom).
%    warning_message("Type ~q not defined, assumed ~q", [Type, T]).
    Type = Type.
%

get_analysis_types(TypeRuleList):-
    findall(typedef(TypSymbol, Def), (
        typedef(TypSymbol, Def), 
        ( internally_defined_type_symbol(TypSymbol,1)
        ; is_type_param_symbol(TypSymbol)
          % ; param_type_symbol_renaming(_,TypSymbol)
        )
    ), TypeRuleList).

%% get_no_simplified_rules(Count, TypeRules):-
%%    Count =:= -1, % None type rule is simplified.
%%    !,
%%    get_analysis_types(TypeRules).
%% get_no_simplified_rules(Count, TypeRules):-
%%    current_type_symbol_counter_value(TypeSymbCount),
%%    TypeSymbCount =:= Count, % No type rule was created since last simplification.
%%    !,
%%    TypeRules = [].
%% get_no_simplified_rules(Count, TypeRules):-
%%     findall(typedef(TypSymbol, Def),
%%            (typedef(TypSymbol, Def), no_simplified_rule(TypSymbol, Count)),
%%             TypeRules).
%% 
%% no_simplified_rule(TypeSymbol, Count):-
%%    atom_concat(rt, N, TypeSymbol),
%%    atom_codes(N, S), 
%%    number_codes(Num, S), 
%%    !,
%%    Num >= Count.

%---------------------------------
% END OF CONSULT OF TYPE RULES 
%---------------------------------

%% :- pred get_param_type_symbol_renamings/1
%%      # "Gets all equivalences of parametric type instances 
%%            to nonparametric types currently in the database.".
%% 
%% get_param_type_symbol_renamings(PEquivs):-
%%      findall(param_type_symbol_renaming(X, Y),
%%              param_type_symbol_renaming(X, Y),
%%              PEquivs).

get_type_symbols_instances_of_parametric_types(Types):- 
    findall(NPartyp, (
        param_type_symbol_renaming(_ParTyp, NPartyp),
        typedef(NPartyp, _Def)
    ), Types).

% ===========================================================================
% (note: it was in termsd.pl)

% TODO: merge revert_type_internal/3 and revert_types/5? (this is
%   required for asub_to_out/6, asub_to_info/6) (JF)

:- export(revert_type_internal/3).
% Given type T and variable X, obtain internal property representation.
% Use revert_type/5 to obtain the final representation.
revert_type_internal(T,X,Type):-
    type_symbol(T), !,
    functor(Type,T,1),
    arg(1,Type,X).
%       Type=..[T,X].
revert_type_internal(T,X,(X=T)).      

% TODO: document NewInternalPred
:- export(revert_types/5).
:- meta_predicate revert_types(?,?,pred(3),?,?).
% Obtain property literal representation of internal types literals
% (as obtained from revert_type_internal/3)
revert_types([Type0|OutputUser],[NType|NOutputUser],NewInternalPred,Symbols,Rest):-
    non_par_equiv_type(Type0,Type), % TODO: inserted here from asub_to_native (JFMC)
    ( Type = (_X = T) ->
        symbols_of(T,Symbols,Rest1),
        NType = Type
    ; functor(Type,S,AS),
      prop_argvar(Type,X), % TODO: see revert_type_internal/3 and non_par_equiv_type/2, can arity be != 1?
      ( param_type_symbol_renaming(PT,S) ->
          % parametric are not created: so not required
          % Symbols = [PT|Rest1],
          %pp% Symbols = Rest1,
          PT=..[_|Args],
          append(Args,Rest1,Symbols),
          prop_apply(PT,X,NType)
      ; internally_defined_type_symbol(S,AS) ->
          Symbols = [S|Rest1],
          call(NewInternalPred,S,AS,NewS),
          Type=..[S|Args],
          NType=..[NewS|Args]
      ; Symbols = Rest1,
        NType=Type
      )
    ),
    revert_types(OutputUser,NOutputUser,NewInternalPred,Rest1,Rest).
revert_types([],[],_NewInternalPred,S,S).

symbols_of(T,Symbols,Rest):-
    compound_pure_type_term(T,Term,_Name,Arity),!,
    symbols_of0(Arity,Term,Symbols,Rest).
symbols_of(T,[T|Rest],Rest).

symbols_of0(0,_Term,S,S).
symbols_of0(N,Term,Symbols,Rest):-
    arg(N,Term,T),
    symbols_of(T,Symbols,Rest1),
    N1 is N - 1,
    symbols_of0(N1,Term,Rest1,Rest).

