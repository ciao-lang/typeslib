% (included from typeslib.pl)
%! # Basic Type Operations (for size-extended types)

% \author Alejandro Serrano
%
% \module This module implements an extended version of the Dart-Zobel
% inclusion algorithm which takes into account the size descriptions
% used in the argsize abstract domain.  The code is based on the one
% in @lib{basic_type_operations} and @lib{regtype_basic_lattice}.
% 
% In order to solve size relations, it requires a definition for the
% multifile edz_postprocess_relations/4.

:- use_module(library(terms_check), [unifiable/3]).

% ---------------------------------------------------------------------------
% (hook for edz_type_included/5)    
% TODO: document
% Note: output PostRel is expected to be sorted
:- multifile edz_postprocess_relations/4.
% ---------------------------------------------------------------------------

% (exported)
:- pred edz_type_included(+Type1, +Size1, +Type2, +Size2, -Relations)
   # "Like @pred{dz_type_included/2} but using @pred{edz_subset/5}".
edz_type_included(Type1, Size1, Type2, Size2, Relations):-
    retractall_fact(epgm_dz_pair(_, _)),
    % retractall_fact(epgm_dz_pair(_, _, _, _, _)), % unused (JFMC)
    edz_subset(Type1, Size1, Type2, Size2, Relations).

% TODO: reuse dz_pair/2
:- pred edz_pair(?TypSymb, ?TypSet).
edz_pair(TypSymb, TypSet):-
    epgm_dz_pair(TypSymb, TypSet).
edz_pair(TypSymb, TypSet):-
    elib_dz_pair(TypSymb, TypSet).

:- data(epgm_dz_pair/2). %% For user programs.
:- data(elib_dz_pair/2). %% For libraries.

:- pred edz_subset(+Type1,+Size1,+Type2,+Size2,-Relations)
   # "Checks whether @var{Type1} is a subset of @var{Type2}.  If so,
   it also generates the @var{Relations} between @var{Size1} and
   @var{Size2} (based on @pred{generate_size_relations/3} hook).".

edz_subset(Type1, Size1, Type2, Size2, Relations) :-
    % same type
    Type1 == Type2, !,
    unifiable(Size1, Size2, RawRelations),
    edz_postprocess_relations(RawRelations, Size1, Size2, Relations).
edz_subset(Type1, _Size1, _Type2, _Size2, []) :-
    % _|_ <= everything
    bot_type(Type1), !. 
edz_subset(_Type1, _Size1, Type2, _Size2, []) :-
    bot_type(Type2), !,
    % never something <= _|_ (but for _|_)
    fail. 
edz_subset(_Type1, _Size1, Type2, _Size2, []) :-
    % everything <= top
    equivalent_to_top_type(Type2), !.  
edz_subset(Type1, _Size1, _Type2, _Size2, []) :-
    % never top <= something (but for top)
    top_type(Type1), !,
    fail.
% Added by PLG May-18-2003 to fix the bug:
% list(num) was not included in gnd.
edz_subset(Type1, _Size1, Type2, _Size2, []) :-
    % Check inclusion in the 'ground' type
    % There are no relations for this type
    ground_type(Type2), 
    !,
    is_ground_type(Type1).
% End added
edz_subset(Type1, Size1, Type2, Size2, Relations):- 
    compound_pure_type_term(Type1, _Term1, _Name1, _Arity1),
    !,
    compound_pure_type_term_edz_subset(Type1, Size1, Type2, Size2, RawRelations),
    edz_postprocess_relations(RawRelations, Size1, Size2, Relations).
%% Added by PLG. Oct, 20, 2004
edz_subset(Type1, Size1, Type2, Size2, Relations):- 
    compound_pure_type_term(Type2, _Term2, _Name2, _Arity2),
    !,
    rule_type_symbol(Type1), 
    edz_subset_v([Type1], [Size1], [[Type2]], [[Size2]], RawRelations),
    edz_postprocess_relations(RawRelations, Size1, Size2, Relations).
%% End Added by PLG.
edz_subset(Type1, Size1, Type2, Size2, Relations):- 
    basic_lattice_type_symbol(Type1), 
    basic_lattice_type_symbol(Type2),
    !,
    edz_subset_lattice(Type1, Size1, Type2, Size2, Relations).
%% End Paco
edz_subset(_Type1, Size1, Type2, Size2, [C=A,D=B]):-
    % TODO: add hook? use get_size_definition/5? (JFMC)
    dz_type_included(Type2,num),
    Size1 = num((A,B)),
    !,
    Size2 = num((C,D)).
edz_subset(Type1, Size1, Type2, Size2, Relations) :-
    edz_subset_v([Type1], [Size1], [[Type2]], [[Size2]], RawRelations),
    edz_postprocess_relations(RawRelations, Size1, Size2, Relations).

compound_pure_type_term_edz_subset(_Type1, _Size1, Type2, _Size2, []):- 
    struct_type(Type2), !.
compound_pure_type_term_edz_subset(Type1, _Size1, Type2, _Size2, []):-  
    ground_struct_type(Type2), !,
    is_ground_type(Type1).
compound_pure_type_term_edz_subset(Type1, Size1, Type2, Size2, Relations):-
    compound_pure_type_term(Type2, _Term2, _Name2, _Arity2),
    edz_subset_v([Type1], [Size1], [[Type2]], [[Size2]], Relations).
compound_pure_type_term_edz_subset(Type1, Size1, Type2, Size2, Relations):- 
    rule_type_symbol(Type2),
    edz_subset_v([Type1], [Size1], [[Type2]], [[Size2]], Relations).

:- pred edz_subset_v(+Seq, +SizeSeq, +SeqSet, +SizeSeqSet, -Relations)
   # "Like @pred{dz_subset_v/2} but using @pred{generate_size_relations/3} for
   size relations".
edz_subset_v(_Seq, _Sizes, [], _, _) :-
    % We are not a subset :(
    !, fail.   
edz_subset_v([bot|Seq], [_|Sizes], SeqSet, SizeSeqSet, Relations):-
    !,
    edz_tails(SeqSet, SizeSeqSet, Tails, SizeTails),
    edz_subset_v(Seq, Sizes, Tails, SizeTails, Relations).            
edz_subset_v([], [], _, _, []) :- !.
edz_subset_v([Type|Seq], [_Size|SizeSeq], SeqSet, SizeSeqSet, Relations):-
    rule_type_symbol(Type), % old 
    % type_symbol(Type), 
    findall(TypeSet, edz_pair(Type, TypeSet), SetTypeSet, [[Type]]), % claudio
    % findall(TypeSet, dz_pair(Type, TypeSet), SetTypeSet),
    dz_heads(SeqSet, Heads), % TODO: was edz_heads/4 but size was unused
    set_ty_subset(SetTypeSet, Heads), !,
    edz_tails(SeqSet, SizeSeqSet, Tails, SizeTails),
    edz_subset_v(Seq, SizeSeq, Tails, SizeTails, Relations).
edz_subset_v([Type|Seq], [Size|SizeSeq], SeqSet, SizeSeqSet, Relations):-
    rule_type_symbol(Type), !,
    edz_expand([Type|Seq], [Size|SizeSeq], SetofSeq, SetofSizeSeq),
    dz_heads(SeqSet, Heads), % TODO: was edz_heads/4 but size was unused
    asserta_fact(epgm_dz_pair(Type, Heads)), 
    all_edz_subset_v(SetofSeq, SetofSizeSeq, SeqSet, SizeSeqSet, Relations).   
edz_subset_v([Type|Seq], [Size|SizeSeq], SeqSet, SizeSeqSet, Relations):-
    edz_open(Type, [Type|Seq], [Size|SizeSeq], OpenSeq, OpenSizeSeq),
    edz_expands(SeqSet, SizeSeqSet, ExpSeqSet, ExpSizeSeqSet),
    edz_selects(ExpSeqSet, ExpSizeSeqSet, Type, SelExpSeqSet, SelExpSizeSeqSet),
    % Generate size relations
    generate_size_relations(Size, SelExpSizeSeqSet, ThisRelations),
    % Continue Dart-Zobel algorithm
    edz_opens(SelExpSeqSet, SelExpSizeSeqSet, Type, OpenSelExpSeqSet, OpenSelExpSizeSeqSet),
    edz_subset_v(OpenSeq, OpenSizeSeq, OpenSelExpSeqSet, OpenSelExpSizeSeqSet, RestRelations),
    append(ThisRelations, RestRelations, Relations).

% TODO: add hooks? (JFMC)
generate_size_relations(_, [], []) :- !.
generate_size_relations(Size, [[S|_]|R], Relations) :- !,
    generate_size_relations(Size, R, RRelations),
    ( Size = s(Size1,Extra1)
    ; Size1 = Size, Extra1 = none
    ),
    ( S = s(Size2,Extra2)
    ; Size2 = S, Extra2 = none
    ),
    ( Extra1 = (A1,B1), Extra2 = (A2,B2)
    -> ExtraRel = [A1=A2,B1=B2|RRelations]
     ; ExtraRel = RRelations
    ),
    ( unifiable_different_sides(Size1, Size2, SizeRel)
    -> append(SizeRel, ExtraRel, Relations)
     ; Relations = ExtraRel
    ).

% Assume A and B have disjoint set of variables
unifiable_different_sides(A, B, Unif) :-
    unifiable(A, B, PreUnif),
    check_unifications(PreUnif, PreUnif, A, B, Unif).

check_unifications([], _, _, _, []).
check_unifications([X=Y|R], PreUnif, A, B, Unif) :-
    % Recursive part
    check_unifications(R, PreUnif, A, B, RUnif),
    % Check each part is from a place
    varset(A, AVars),
    varset(B, BVars),
    ( ( varmember(X, AVars), varmember(Y, AVars)
      ; varmember(X, BVars), varmember(Y, BVars) )
    -> find_related_unifications(PreUnif, X, Y, UnifsX),
       find_related_unifications(PreUnif, Y, X, UnifsY),
       ord_union(UnifsX, UnifsY, UnifsXY),
       ord_union(UnifsXY, RUnif, Unif)
     ; insert(RUnif,X=Y,Unif)
    ).

find_related_unifications([], _, _, []).
find_related_unifications([A=B|R], X, Y, [Rel|RelR]) :-
    A == X, B \== Y, !,
    join_as_equiv(Y,B,Rel),
    find_related_unifications(R, X, Y, RelR).
find_related_unifications([B=A|R], X, Y, [Rel|RelR]) :-
    A == X, B \== Y, !,
    join_as_equiv(Y,B,Rel),
    find_related_unifications(R, X, Y, RelR).
find_related_unifications([_|R], X, Y, RelR) :-
    !, find_related_unifications(R, X, Y, RelR).

join_as_equiv(A,B,C=D) :-
    sort([A,B],[C,D]).

varmember(X,[Y|_]) :- X == Y.
varmember(X,[_|R]) :- varmember(X,R).

% ---------------------------------------------------------------------------

edz_tails([], [], [], []).
edz_tails([[_|Seq]|SeqSet], [[_|SizeSeq]|SizeSeqSet], [Seq|Rest], [SizeSeq|SizeRest]):-
    edz_tails(SeqSet, SizeSeqSet, Rest, SizeRest).

:- pred edz_expand(+Seq, +SizeSeq, -Expansion, -SizeExpansion)
   # "Like @pred{dz_expand/2} but using @pred{get_size_definition/5}".
edz_expand([], [], [], []):-!.
edz_expand([TypSymbol|Seq], [Size|SizeSeq], Expansion, SizeExpansion):-
    rule_type_symbol(TypSymbol), !, 
    get_type_definition(TypSymbol, Defin1),
    sort(Defin1, Defin), % assume the type is defined.
    get_size_definition(TypSymbol, Defin, Size, ParentSize, SizeDefin),
    edz_expand_type_symbol(ParentSize, Defin, SizeDefin, Seq, SizeSeq, Expansion, SizeExpansion).
edz_expand(Seq, SizeSeq, [Seq], [SizeSeq]).

edz_expand_type_symbol(_Parent, [], [], _Seq, _SizeSeq, [], []) :- !.
edz_expand_type_symbol(Parent, [Type|Defin], [Size|SizeDefin], Seq, SizeSeq, [[Type|Seq]|Expansion], [[ESize|SizeSeq]|SizeExpansion]):-
    ( Parent = none
    -> ESize = Size
     ; ESize = s(Size, Parent)
    ),
    edz_expand_type_symbol(Parent, Defin, SizeDefin, Seq, SizeSeq, Expansion, SizeExpansion).

% In fact we should perform the real union by removing duplicated items. 
% PLG Nov 6 98
edz_expands([], [], [], []) :- !. 
edz_expands([Seq|Rest], [Size|SRest], OutExp, OutSExp):-
    edz_expand(Seq, Size, Expan1, SExpan1),
    edz_expands(Rest, SRest, Expansion, SExpansion),
    append(Expan1, Expansion, OutExp),
    append(SExpan1, SExpansion, OutSExp).
   
all_edz_subset_v([], [], _, _, []) :- !.
all_edz_subset_v([Seq|SetofSeq], [SizeSeq|SetofSizeSeq], SeqSet, SizeSeqSet, Relations):-
    edz_subset_v(Seq, SizeSeq, SeqSet, SizeSeqSet, SeqRelations),
    all_edz_subset_v(SetofSeq, SetofSizeSeq, SeqSet, SizeSeqSet, RestRelations),
    append(SeqRelations, RestRelations, Relations).

%% dz_open(+Type, +Seq, -OutSeq)
%% Type: a pure type term.
%% Seq: an expanded selected sequence.
%% OutSeq: a sequence.

edz_open(Type, [T|InSeq], [S|InSize], OuSeq, OuSize) :-
    % If the size had the parent information, forget about it
    S = s(Size, _Parent), !,
    edz_open_(Type, [T|InSeq], [Size|InSize], OuSeq, OuSize).
edz_open(Type, [T|InSeq], [S|InSize], OuSeq, OuSize) :-
    S \= s(_,_), !,
    edz_open_(Type, [T|InSeq], [S|InSize], OuSeq, OuSize).

edz_open_(Type, [_|InSeq], [_|InSize], InSeq, InSize):-
%  (top_type(Type); 
%   base_type_symbol(Type);
%   struct_type(Type); % Added by PLG 24-5-99
%   ground_type(Type); 
%   is_type_param_symbol(Type); % Added by PBC 01-12-03
%   constant_symbol(Type, _)), !.
% replaced by PBC 01-12-03, by:
    basic_lattice_type_symbol(Type), !.
edz_open_(Type, [Type1|InSeq], [_Size1|InSize], OuSeq, OuSize):-
    compound_pure_type_term(Type, _Comp, _Name, Arity),
    top_type(Type1), !,
    create_top_sequence(Arity, TopSeq),
    append(TopSeq, InSeq, OuSeq),
    append(TopSeq, InSize, OuSize).
edz_open_(Type, [Type1|InSeq], [_Size1|InSize], OuSeq, OuSize):-
    compound_pure_type_term(Type, _Comp, _Name, Arity),
    ground_type(Type1), !,
    create_ground_sequence(Arity, GroundSeq),
    append(GroundSeq, InSeq, OuSeq),
    append(GroundSeq, InSize, OuSize).
edz_open_(Type, [Type1|InSeq], [_Size1|InSize], OuSeq, OuSize):- % Uncommented -PLG (11 Jul 05)
    compound_pure_type_term(Type, _Comp, _Name, Arity),
    struct_type(Type1), !,
    create_top_sequence(Arity, TopSeq),
    append(TopSeq, InSeq, OuSeq),
    append(TopSeq, InSize, OuSize).
edz_open_(Type, [Type1|InSeq], [_Size1|InSize], OuSeq, OuSize):- % Added -ASM (5 Sep 12)
    compound_pure_type_term(Type, _Comp, _Name, Arity),
    var_type(Type1), !,
    create_var_sequence(Arity, TopSeq),
    append(TopSeq, InSeq, OuSeq),
    append(TopSeq, InSize, OuSize).
edz_open_(Type, [Type1|InSeq], [Size1|InSize], OuSeq, OuSize):-
    compound_pure_type_term(Type, _Comp, Name, Arity), 
    compound_pure_type_term(Type1, Comp1, Name, Arity),
    compound_pure_type_term(Size1, SizeComp1, Name, Arity),
    Comp1 =.. [_|ArgSeq],
    SizeComp1 =.. [_|ArgSize],
    append(ArgSeq, InSeq, OuSeq),
    append(ArgSize, InSize, OuSize).

%% dz_opens(+Seq, +Type, -OutSeq)
%% Seq: a set of expanded selected sequences.
%% Type: a pure type term.
%% OutSeq: a set of sequences.

edz_opens([], [], _, [], []):-!.
edz_opens([Seq|Rest], [Size|SRest], Type, [OuSeq|OuRest], [OuSize|OuSRest]):-
    edz_open(Type, Seq, Size, OuSeq, OuSize),
    edz_opens(Rest, SRest, Type, OuRest, OuSRest).

%% dz_selects(+Seqs, +Type, -Sel)
%% Type: a type term.
%% Seqs: an expanded set of sequences.
%% Sel: a set of sequences.

edz_selects([[Type1|Seq]|Rest], [[Size1|SizeSeq]|SizeRest], Type, Sel, SizeSel):-
    ( dz_type_selects(Type, Type1) % TODO: edz_type_selects/2 was like dz_type_selects/2
    -> Sel = [[Type1|Seq]|SRest], SizeSel = [[Size1|SizeSeq]|SizeSRest]
     ; Sel = SRest, SizeSel = SizeSRest
    ),
    edz_selects(Rest, SizeRest, Type, SRest, SizeSRest).
edz_selects([], [], _Type, [], []).   

% ---------------------------------------------------------------------------
% Code based on regtype_basic_lattice.pl

edz_subset_lattice(Type1, Size1, Type2, Size2, [A=C,B=D]) :-
    % We only have relations for numeric types
    numeric_type(Type2), % TODO: add hook? (JFMC)
    !,
    type_included_in_numeric(Type1),
    Size1 =.. [_|[(A,B)]],
    Size2 =.. [_|[(C,D)]].
edz_subset_lattice(Type1, _Size1, Type2, _Size2, []) :-
    % For the rest check usual inclusion
    dz_subset_lattice(Type1, Type2).

% ---------------------------------------------------------------------------
%! # Default size definitions

% TODO: add hook? (JFMC)

% HACK: Special case for numbers and gnd
get_size_definition(_, [num], num((A,B)), (A,B), [num((A,B))]) :- !.
%get_size_definition(_, [gnd], gnd((A,B)), (A,B), [gnd((A,B))]) :- !.
get_size_definition(Typ, Defn, Size, ParentSize, SizeDefn) :-
    get_size_definition_(Typ, Defn, Size, ParentSize, SizeDefn).

% ASM - New predicates for sizes
get_size_definition_(_TypSymbol, [], _Size, _ParentSize, []) :- !.
get_size_definition_(TypSymbol, [Rule|Rest], Size, ParentSize, [RuleSize|RestSizes]) :-
    ( Size =.. [_,(A,B)|Args]
    -> ParentSize = (A,B)
     ; Size =.. [_|Args],
       ParentSize = none
    ),
    find_size_for_rule(TypSymbol, Size, Rule, Args, RuleSize),
    get_size_definition_(TypSymbol, Rest, Size, ParentSize, RestSizes).

% Special cases for lists
find_size_for_rule(Typ, ParentSize, [], Rs, RuleSize) :-
    !,
    find_size_for_rule(Typ, ParentSize, ^([]), Rs, RuleSize).
find_size_for_rule(Typ, ParentSize, [A|B], Rs, RuleSize) :-
    !,
    find_size_for_rule(Typ, ParentSize, ^(.(A,B)), Rs, RuleSize).
% Check we have the size
find_size_for_rule(Typ, ParentSize, Rule, [R|_], ^(RuleSize)) :-
    % We have functors
    Rule = ^(InnerRule),
    functor(InnerRule, F, _),
    R = ^(InnerSize),
    functor(InnerSize, F, _),
    !, % We found the size
    InnerRule =.. [F|RuleArgs],
    InnerSize =.. [F|SizeArgs],
    generate_new_size_for_rule(Typ, ParentSize, RuleArgs, SizeArgs, RuleSizeArgs),
    RuleSize =.. [F|RuleSizeArgs].
find_size_for_rule(_Typ, _ParentSize, Rule, [R|_], RuleSize) :-
    Rule \= ^(_), % We have another type
    functor(Rule, F, _),
    functor(R, F, _),
    !, RuleSize = R. % We just take the size
find_size_for_rule(Typ, ParentSize, Rule, [_|Args], RuleSize) :-
    find_size_for_rule(Typ, ParentSize, Rule, Args, RuleSize).

generate_new_size_for_rule(_, _, [], _, []).
generate_new_size_for_rule(Typ, ParentSize, [Typ|Rest], SizeSeq, [NewSize|SizeRest]) :-
    !, % Recursive case
    ( ParentSize =.. [F,(A,B)|Args] % This should always be the case
    -> NewSize =.. [F,(A-1,B-1)|Args]
     ; NewSize = ParentSize
    ),
    generate_new_size_for_rule(Typ, ParentSize, Rest, SizeSeq, SizeRest).
generate_new_size_for_rule(Typ, ParentSize, [Other|Rest], [Size|SizeSeq], [Size|SizeRest]) :-
    Other \= Typ,
    generate_new_size_for_rule(Typ, ParentSize, Rest, SizeSeq, SizeRest).
% ASM - End of new predicates

