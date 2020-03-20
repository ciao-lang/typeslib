:- module(rnd_type_value, [], []).

% TODO: document; this is an incomplete prototype of a random type value generator
%   See rnd_basic_type_value/3

:- use_module(library(random)).
:- use_module(library(lists), [length/2]).
:- use_module(library(hiordlib), [maplist/3]).
:- use_module(typeslib(typeslib), [equiv_type/2]).
:- use_module(typeslib(typeslib), [ % (internal?)
    typedef/2,
    paramtypedef/2,
    param_type_symbol_renaming/2
]).

:- export(rnd_type_value/2).
rnd_type_value(Type, Value) :-
    rnd_type_value_(Type, params(0.05, 10), Value),
    !.

rnd_type_value_(Type, ExtraParams, Value) :-
    rnd_basic_type_value(Type, ExtraParams, Value),
    !.
rnd_type_value_(^(Pattern), params(P, K), Value) :-
    pattern_value(Pattern, P, K, Value).
rnd_type_value_([Type|Other], ExtraParams, [Value|Values]) :-
    rnd_type_value_(Type,  ExtraParams, Value),
    rnd_type_value_(Other, ExtraParams, Values).
rnd_type_value_(Type, ExtraParams, Value) :-
%       display([Type,Value]),nl,
    ( paramtypedef(Type, TypeDef) -> true
    ; ( param_type_symbol_renaming(Type, RenType) -> true % TODO: needed? get typedef in a better way
      ; Type = RenType
      ),
      ( typedef(RenType, TypeDef) -> true
      ; equiv_type(RenType, EqType),
        typedef(EqType, TypeDef)
      )
    ),
    length(TypeDef, N),
    TypeDef = [First|_],
    random(X),
    params(P, _K) = ExtraParams,
    (
        (N == 1 ; X < P) ->
        rnd_type_value_(First, ExtraParams, Value)
    ;
        random(2, N, I),
        A =.. [p|TypeDef],
        arg(I, A, Possible),
        rnd_type_value_(Possible, ExtraParams, Value)
    ).

pattern_value(Pattern, P1, K, Value) :-
    P2 is (K * P1) / (1 + (K - 1) * P1),
    ( typedef(Pattern, _) ->
        rnd_type_value_(Pattern, params(P2, K), Value)
    ; % TODO: cut?
        Pattern =.. [Functor|Types],
        maplist(pattern_value(P2, K), Types, Values),
        Value =.. [Functor|Values]
    ;
        Pattern = Value
    ).

% ---------------------------------------------------------------------------

:- multifile rnd_basic_type_value/3.

% rnd_basic_type_value('basic_props:character_code', _ExtraParams, Value) :-
%       random(0'a,0'z,Value0),
%       random(0'A,0'Z,Value1),
%       random(0'0,0'9,Value2),
%       random(1,3,X),
%       (
%           X == 1 -> Value = Value0
%       ;   X == 2 -> Value = Value1
%       ;   X == 3 -> Value = Value2
%       ).

rnd_basic_type_value(num, ExtraParams, Value) :-
    random(P),
    ( P > 0.5
    -> rnd_basic_type_value(flt, ExtraParams, Value)
    ; rnd_basic_type_value(int, ExtraParams, Value)
    ).
rnd_basic_type_value(int, _ExtraParams, Value) :-
    random(-32768, 32767, Value).
rnd_basic_type_value(flt, _ExtraParams, Value) :-
    uniform(-100.0, 100.0, Value).
rnd_basic_type_value('basic_props:nnegint', _ExtraParams, Value) :-
    random(0, 32767, Value).
rnd_basic_type_value('basic_props:character_code', _ExtraParams, Value) :-
    random(1, 255, Value).
rnd_basic_type_value(var,               _ExtraParams, _Value).
rnd_basic_type_value('term_typing:var', _ExtraParams, _Value).
rnd_basic_type_value(atm,               _ExtraParams, Value) :-
%% these params avoid the overload of the atom table
    rnd_type_value_('basic_props:string', params(1.0/3.0, 10), Value0),
    atom_codes(Value, Value0).
rnd_basic_type_value('term_typing:ground', ExtraParams, Value) :-
    rnd_basic_type_value(gnd, ExtraParams, Value).
rnd_basic_type_value(gnd, ExtraParams, Value) :-
    random(2, 5, X),
    params(P1, K) = ExtraParams,
    ( X == 2 ->
        rnd_basic_type_value(num, ExtraParams, Value)
    ; X == 3 ->
        rnd_basic_type_value(atm, ExtraParams, Value)
    ; P2 is (K * P1) / (1 + (K - 1) * P1),
      rnd_type_value_('basic_props:list'('basic_props:gnd'), params(P2, K), Args),
      ( X == 4 ->
          Value = Args
      ; rnd_basic_type_value(atm, ExtraParams, Functor),
        Value =.. [Functor|Args]
      )
    ).
rnd_basic_type_value(term, ExtraParams, Value) :-
    random(1, 5, X),
    params(P1, K) = ExtraParams,
    ( X == 1 ->
        Value = _
    ; X == 2 ->
        rnd_basic_type_value(num, ExtraParams, Value)
    ; X == 3 ->
        rnd_basic_type_value(atm, ExtraParams, Value)
    ; P2 is (K * P1) / (1 + (K - 1) * P1),
      rnd_type_value_('basic_props:list', params(P2, K), Args),
      ( X == 4 ->
          Value = Args
      ; rnd_basic_type_value(atm, ExtraParams, Functor),
        Value =.. [Functor|Args]
      )
    ).
rnd_basic_type_value([],    _, []).
rnd_basic_type_value(Const, _, Const) :- number(Const).

uniform(A, B, D) :-
    random(R),
    D is A + (B - A) * R.

