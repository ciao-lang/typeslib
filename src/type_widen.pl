% (included file)
%! # Widenings

% ---------------------------------------------------------------------------
%! ## Naive widening based on defined types

% TODO: very inefficient! linear search on types
% (exported)
terms_naive_ewiden_el(T,T2):-
    get_module_types(List),
    contain_this_type(List,T,Ret),
    minimaltype(Ret,T2),!.

% ---------------------------------------------------------------------------
%! ## Shortening
% Used in `termsd.pl`. It needs a `Depthk` parameter.

% (exported)
shortening_el(T,ST,Depthk):- 
    find_path(T,Anc,N,[],1,Depthk,Flag),!,
    ( Flag == included ->
        Node = Anc
    ; type_union_NoDB(Anc,N,Node,[])
    ),
    get_typedef(Node, Defin),
    new_type_symbol(NewNode),
    replace_def(Defin,NewDefin,N,Anc,NewNode,[]),
    unfold_type_union(NewNode,NewDefin,NewDefin_u),    
    sort(NewDefin_u,NewDefin_u_s),
    insert_rule(NewNode,NewDefin_u_s),
    replace(T,Anc,Anc,NewNode,NT,[]),
    shortening_el(NT,ST,Depthk).
shortening_el(T,T,_).

replace(T,T1,_,NewNode,NewNode,_):- T == T1,!.
replace(T,_,T1,NewNode,NewNode,_):- T == T1,!.
replace(T,T1,T2,NewNode,NT,Seen):-
    get_typedef(T,Def),!,
    ( member(T,Seen) ->
        NT = T
    ; replace_def(Def,NewDef,T1,T2,NewNode,[T|Seen]),
      ( Def == NewDef ->
          NT = T
      ; new_type_symbol(NT),            
        replace_def(NewDef,NewDef2,T,T,NT,Seen),  %  Seen
        unfold_type_union(NT,NewDef2,NewDef2_u), 
        sort(NewDef2_u,NewDef2_u_s),
        insert_rule(NT,NewDef2_u_s)
      )
    ).
% replace(T,T1,T2,NewNode,NT,Seen):-
%       get_typedef(T,Def),!,
%       (
%           member((T,NT),Seen) -> true
%       ;
%           new_type_symbol(NT),
%           replace_def(Def,NewDef,T1,T2,NewNode,[(T,NT)|Seen]),
%           unfold_type_union(NT,NewDef,NewDef_u), % test test test test
%           insert_rule(NT,NewDef_u)
%       ).
replace(T,T1,T2,NewNode,NT,Seen):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    replace_arg(A,Term,NewTerm,T1,T2,NewNode,Seen),
    construct_compound_pure_type_term(NewTerm,NT).
replace(T,_,_,_,T,_).

replace_def([],[],_,_,_,_).
replace_def([T|Def],[NT|NewDef],T1,T2,NewNode,Seen):-
    replace(T,T1,T2,NewNode,NT,Seen),
    replace_def(Def,NewDef,T1,T2,NewNode,Seen).

replace_arg(0,_,_,_,_,_,_) :- !.
replace_arg(A,Term,NewTerm,T1,T2,NewNode,Seen):-
    arg(A,Term,Arg),
    replace(Arg,T1,T2,NewNode,NewArg,Seen),
    arg(A,NewTerm,NewArg),
    A1 is A - 1,
    replace_arg(A1,Term,NewTerm,T1,T2,NewNode,Seen).

find_path(T,Anc,N,Seen,Depth,Depthk,Flag):-
    get_typedef(T,Def),!,
    prlb(T,Lab),
    ( ( member((Lab,Anc),Seen),
        ( Depthk =\= 0, Depth >= Depthk
        ; dz_type_included(T,Anc)
        )
      ) ->
        ( T == Anc -> fail
        ; N = T,
          ( Depthk =\= 0, Depth >= Depthk ->
              Flag = notincluded
          ; Flag = included
          )
        )
    ; NewDepth is Depth + 1,
      find_path_def(Def,Anc,N,[(Lab,T)|Seen],NewDepth,Depthk,Flag)
    ).
find_path(T,Anc,N,Seen,Depth,Depthk,Flag):-
    compound_pure_type_term(T,Term,_F,A),!,
    NewDepth is Depth + 1,  
    find_path_arg(A,Term,Anc,N,Seen,NewDepth,Depthk,Flag).

find_path_def([T|_Def],Anc,N,Seen,Depth,Depthk,Flag):-
    find_path(T,Anc,N,Seen,Depth,Depthk,Flag),!.
find_path_def([_T|Def],Anc,N,Seen,Depth,Depthk,Flag):-
    find_path_def(Def,Anc,N,Seen,Depth,Depthk,Flag).

find_path_arg(0,_,_,_,_,_,_,_):- !,fail.
find_path_arg(A,Term,Anc,N,Seen,Depth,Depthk,Flag):-
    arg(A,Term,Arg),
    find_path(Arg,Anc,N,Seen,Depth,Depthk,Flag),!.
find_path_arg(A,Term,Anc,N,Seen,Depth,Depthk,Flag):-
    A1 is A - 1,
    find_path_arg(A1,Term,Anc,N,Seen,Depth,Depthk,Flag).

% ---------------------------------------------------------------------------
%% %! ## Type Jungle

%% A @em{Type Jungle} is a type graph with at most one node for each
%% function symbol. It can be used as a finite subdomain of type
%% graphs. This predicate converts a type graph into the finite domain of
%% type jungles.
%% The main component is the predicate @tt{build_type_jungle}. 

%% jungle_el(T,T):-
%%      top_type(T),!.
%% jungle_el(T,T):-
%%      base_type_symbol(T),!.
%% jungle_el(T,JT):-
%%      prlb(T,Lab),
%%      build_type_jungle(Lab,JT,[],T,Rules,[]),
%%      insert_rules(Rules).
%% 
%% insert_rules([]).
%% insert_rules([(S,Def)|Rules]):-
%%      unfold_type_union(S,Def,Def_u), % test test test test      
%%      sort(Def_u,Def_u_s),
%%      insert_rule(S,Def_u_s),
%%      insert_rules(Rules).
%% 
%% :- pred build_type_jungle(+Lab,-JT,+Nodes,+Type,+Rules,+TailRules): list * pure_type_term * list * pure_type_term * list * list #
%% "
%% It takes a set @var{Lab} of funtion symbols and will return a node
%% (type term @var{JT}) that is an upper bound of all funtor nodes in the type
%% graph labeled with one of the function symbols in @var{Lab}. If there
%% is already a node for this set of functors then it is looked up in
%% @var{Nodes} and returned directly. Otherwise there are three cases:
%% @begin{itemize}
%% @item if @var{Lab} is a singleton @{JT@} and JT is not a functor/arity element, return Jt.
%% @item if @var{Lab} is a singleton @{F/A@} return a new compound pure
%% type term that should be an upper bound of all nodes in the type graph
%% with label F. It is done by the predicate @tt{build_args} by calling
%% recursively @tt{build_type_jungle} for each argument.
%% @item if on the other hand @var{Lab} is not a singleton, it return a
%% new type symbol and create a new type rule which definition is built
%% by the predicate @tt{build_def} by calling recursively
%% @tt{build_type_jungle} for each element in @var{Lab}.
%% @end{itemize}
%% ".
%% 
%% 
%% build_type_jungle(Lab,JT,Nodes,_Type,Rules,Rules):-
%%      member((Lab,JT),Nodes),!.
%% build_type_jungle([F/A],JT,Nodes,Type,Rules,TailRules):-
%%      functor(NewTerm,F,A),
%%      construct_compound_pure_type_term(NewTerm,JT),
%%      build_args(A,NewTerm,F,A,Type,[([F/A],JT)|Nodes],Rules,TailRules).
%% build_type_jungle([JT],JT,_Nodes,_Type,Rules,Rules).
%% build_type_jungle(Lab,JT,Nodes,Type,[(JT,Def)|Rules],TailRules):-
%%      new_type_symbol(JT),
%%         build_def(Lab,Def,[(Lab,JT)|Nodes],Type,Rules,TailRules).
%% %    insert_rule(JT,Def).
%% 
%% build_args(0,_,_,_,_,_,R,R).
%% build_args(N,Term,F,A,Type,Nodes,Rules,TailRules):-
%%      labels_of_functor(Type,F,A,N,Lab),
%%      arg(N,Term,JT),
%%      build_type_jungle(Lab,JT,Nodes,Type,Rules,Rules1),
%%      N1 is N - 1,
%%      build_args(N1,Term,F,A,Type,Nodes,Rules1,TailRules).
%% 
%% build_def([],[],_,_,R,R).
%% build_def([L|Lab],[D|Def],Nodes,Type,Rules,TailRules):-
%%      build_type_jungle([L],D,Nodes,Type,Rules,Rules1),
%%      build_def(Lab,Def,Nodes,Type,Rules1,TailRules).
%% 
%% 
%% :- pred labels_of_functor(+Type,+Functor,+Arity,+I,-Lab): pure_type_term * atom * int * 
%% int * list #
%% "
%% It obtains a list of functor/arity terms or basic type terms which are
%% the principal function symbols or basic type terms of the @var{I}th
%% argument of any compound type term with @var{Functor}/@var{Arity}
%% function symbol in the type graph @var{Type}. 
%% There are three cases:
%% @begin{itemize}
%% @item if @var{Type} is a type symbol and it is alredy in the set @var{Seen} it returns the empty set. Otherwise it returns the set of labels of each type term in the definition.
%% @item if @var{Type} is a compound type term with @var{Functor}/@var{Arity}
%% function symbol it obtains the @var{I}th argument and returns the principal labels of it.
%% @item Otherwise it returns the empty set.
%% @end{itemize}
%% ".
%% 
%% labels_of_functor(Type,Functor,Arity,I,Lab):-
%%      labels_of_functor0(Type,Functor,Arity,I,L,[],[]),
%%      sort(L,Lab).
%% 
%% labels_of_functor0(T,F,A,I,Lab,L,Seen):-
%%      get_typedef(T,Def),!,
%%      ( 
%%          member(T,Seen) ->
%%          Lab = L
%%      ;
%%          labels_of_functorlist(Def,F,A,I,Lab,L,[T|Seen])
%%      ).      
%% 
%% labels_of_functor0(T,F,A,I,Lab,L,_Seen):-
%%      compound_pure_type_term(T,Term,F,A),!,
%%      arg(I,Term,Arg),
%%      prlb0(Arg,Lab,L1,[]),
%%      labels_of_functor0(Arg,F,A,I,L1,L,_Seen).
%% 
%% labels_of_functor0(_T,_F,_A,_I,L,L,_Seen).
%% 
%% labels_of_functorlist([],_F,_A,_I,L,L,_Seen).
%% labels_of_functorlist([T|Rest],F,A,I,Lab,L,Seen):-
%%      labels_of_functor0(T,F,A,I,Lab,L1,Seen),
%%      labels_of_functorlist(Rest,F,A,I,L1,L,Seen).

% ---------------------------------------------------------------------------
%! ## Topological clash widening operator
% Used in `ptypes.pl`

% (exported)
:- export(hentenwid/3).
hentenwid(T1,T2,T) :-
    hentenwid_(T1,T2,T,[],[],no).

samepf([],[]).
samepf([T|Def],[T2|Def2]):-
    samefunctor(T,T2),!,
    samepf(Def,Def2).

samefunctor(T,T).
samefunctor(T,T2):-
    compound_pure_type_term(T,_Term,F,A),!,
    compound_pure_type_term(T2,_Term2,F,A).
    
hentenancestor(T2,Seen,NT):-
    member((T,NT),Seen),
    dz_type_included(T2,T).
  
hentendef([],[],[],_,_,_).
hentendef([T1|Def1],[T2|Def],[T|NewDef],Seen,Prev,Flag):-
    hentenwid_(T1,T2,T,Seen,Prev,Flag),
    hentendef(Def1,Def,NewDef,Seen,Prev,Flag).

hentenwid_arg(0,_Term1,_Term2,_NewTerm,_Seen,_Prev,_Flag) :- !.
hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag):-
    arg(A,Term2,Arg2),
    arg(A,Term1,Arg1),
    hentenwid_(Arg1,Arg2,NewArg,Seen,Prev,Flag),     
    arg(A,NewTerm,NewArg),
    A1 is A - 1,
    hentenwid_arg(A1,Term1,Term2,NewTerm,Seen,Prev,Flag).

hentenwid_(T1,T2,T,Seen,Prev,Flag):-
    get_typedef(T2,Def),!,
    (
        member((T2,T),Seen) -> true
    ;
        (
            (
                get_typedef(T1,Def1) ->
                NewPrev = [T1|Prev],
                (
                    (Flag == yes;member(T1,Prev)) ->
                     NewFlag = yes
                ;
                    NewFlag = Flag
                )
            ;
                NewPrev = Prev,
                Def1 = [T1],
                NewFlag = Flag
            ),
            (
                (samepf(Def,Def1),NewFlag = no) ->
                 new_type_symbol(NT),
                 hentendef(Def1,Def,NewDef,[(T2,NT)|Seen],NewPrev,NewFlag),
                 (
                     Def == NewDef ->
                     T = T2
                 ;
                     T = NT,
                     unfold_type_union(T,NewDef,NewDef_u),
                     sort(NewDef_u,NewDef_u_s),
                     insert_rule(T,NewDef_u_s)
                 )
            ;
                (
                    hentenancestor(T2,Seen,T) ->
                    true
                ;
                    T = T2
                )
            )
        )
    ).
hentenwid_(T1,T2,T,Seen,Prev,Flag):-
    compound_pure_type_term(T2,Term2,F,A),!,
    compound_pure_type_term(T1,Term1,F,A),
    functor(NewTerm,F,A),
    hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag),
    construct_compound_pure_type_term(NewTerm,T).
hentenwid_(_T1,T2,T2,_Seen,_Prev,_Flag). 

%% % TODO: ??? Alternative to hentenwid/3 (it was in termsd.pl, next to hentenwid/3)
%%
%% widen_el(T1,T2,T):-
%%      get_typedef(T1,Def),!,
%%      sort(Def,Def_s),
%%      new_replace(T2,T1,Def_s,T2,T,[]).
%% 
%% %widen_el(_,T,T).
%% widen_el(T1,T2,T):-
%%      new_replace(T2,_,[T1],T2,T,[]).
%% 
%% new_replace(T,TPrime,_,NewNode,NewNode,_):- T==TPrime,!.
%% new_replace(T,TPrime,DefPrime,NewNode,NT,Seen):-
%%      get_typedef(T,Def),!,
%%      sort(Def,Def_s),
%%      ( 
%%          ord_subset_diff(DefPrime,Def_s,DiffDef) -> 
%%          insert(DiffDef,NewNode,NewDef),
%%          new_type_symbol(NewT), 
%%          unfold_type_union(NewT,NewDef,NewDef_u),           
%%          sort(NewDef_u,NewDef_u_s),
%% % do we also have to replace in NewDef?
%% %        ( 
%% %            member(T,Seen) -> NT = T
%% %        ;
%% %            new_replace_def(NewDef_u_s1,NewDef_u_s,TPrime,DefPrime,NewNode,[T|Seen]),
%% % do we also have to replace in NewDef?                  
%%              
%%             (
%%              NewDef_u_s == Def_s -> 
%%              ( 
%%                  member(T,Seen) -> NT = T
%%              ;
%%              new_replace_def(DiffDef,DiffDef2,TPrime,DefPrime,NewNode,[T|Seen]),
%%              append(DefPrime,DiffDef2,Ddef),
%%              NT = NewT,
%%              replace_def(Ddef,Ddef2,T,TPrime,NT,Seen), %Seen
%%              unfold_type_union(NT,Ddef2,Ddef_u),
%%              sort(Ddef_u,Ddef_u_s),
%%              insert_rule(NT,Ddef_u_s)
%%              )
%%              
%%          ;
%%              NT = NewT,
%%              replace_def(NewDef_u_s,NDef,T,T,NT,Seen), % Seen
%%              unfold_type_union(NT,NDef,NDef_u), 
%%              sort(NDef_u,NDef_u_s),    
%%              insert_rule(NT,NDef_u_s) % do we also have to replace in NewDef?
%%          )
%% % ) % do we also have to replace in NewDef?              
%%      ;
%%          ( 
%%              member(T,Seen) -> NT = T
%%          ;
%%              new_replace_def(Def_s,NewDef,TPrime,DefPrime,NewNode,[T|Seen]),
%%              (
%%                  Def_s == NewDef -> 
%%                  NT = T
%%              ;
%%                  new_type_symbol(NT),
%%                  replace_def(NewDef,NewDef2,T,T,NT,Seen), % Seen
%%                  unfold_type_union(NT,NewDef2,NewDef2_u),
%%                  sort(NewDef2_u,NewDef2_u_s),
%%                  insert_rule(NT,NewDef2_u_s)
%%              )
%%          )
%%      ).
%% new_replace(T,TPrime,DefPrime,NewNode,NT,Seen):-
%%              compound_pure_type_term(T,Term,F,A),!,
%%      functor(NewTerm,F,A),
%%      new_replace_arg(A,Term,NewTerm,TPrime,DefPrime,NewNode,Seen),
%%      construct_compound_pure_type_term(NewTerm,NT).
%% new_replace(T,_,[T],New,New,_):- !.    
%% new_replace(T,_,_,_,T,_).      
%% 
%% new_replace_def([],[],_,_,_,_).
%% new_replace_def([T|Def],[NT|NewDef],TPrime,DefPrime,NewNode,Seen):-
%%      new_replace(T,TPrime,DefPrime,NewNode,NT,Seen),
%%      new_replace_def(Def,NewDef,TPrime,DefPrime,NewNode,Seen).
%% 
%% new_replace_arg(0,_,_,_,_,_,_) :- !.
%% new_replace_arg(A,Term,NewTerm,TPrime,DefPrime,NewNode,Seen):-
%%      arg(A,Term,Arg),
%%      new_replace(Arg,TPrime,DefPrime,NewNode,NewArg,Seen),
%%      arg(A,NewTerm,NewArg),
%%      A1 is A - 1,
%%      new_replace_arg(A1,Term,NewTerm,TPrime,DefPrime,NewNode,Seen).

% ---------------------------------------------------------------------------
%! # Eterms widening operator
% TODO: document

:- use_module(library(lists), [dlist/3]).
:- use_module(library(sets), [insert/3, ord_delete/3]).

:- export(lnewiden_el/4).
lnewiden_el(T1,T2,_TEval,T1):- T1 == T2,!.
lnewiden_el(_,(N,T),_TEval,(N,T)):- top_type(T),!.
lnewiden_el((_N1,T1),(N2_e,T2),TEval,(N2,W)):-
    get_canonical_name(N2_e,N2),
    retract_type_name(N2,LWs,Count),        % equival_names
    laddcycles(LWs,LWss),
    lfilternames(LWss,N2,LWSS),
    ( LWSS == [] ->
        % TODO: ewiden_el can call shortening_el/3 here (which may be good)
        W=T2,
        insert_type_name(N2,LWs,Count) % TODO: count is not modified?
    ;
        insert_type_name(N2,LWs,Count),
        ( TEval=yes, member((['$is'],_N),LWs) -> %% OJO REVISAR % TODO: ???
            get_less_numeric_type(T2,W)
        ;
            new_type_symbol(W),
            maybe_get_type_definition(T2,Def),
%               display(user,'start'),nl(user),
            lnewiden_def(Def,NewDef,T1,T2,W,[(N2,W)],[],LWSS,[],I,[],ListofnewW,[W]), 
            sort(NewDef,NewDef_s),
            insert_rule(W,NewDef_s),
%               display(user,'end'),nl(user),
            sort(ListofnewW,ListofnewW_s),
            normalize_wide_rules_listOfnew(ListofnewW_s,I),
            resetunion,
            make_determ_wide_rules(I)
%               display(user,'endnor'),nl(user)
        )
    ).

lnewiden_def([],[],_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN):- !.
lnewiden_def([T|Def],[NT|NewDef],T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LNt):-
    lnewiden_elem(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,I1,LN,LN1),
    lnewiden_def(Def,NewDef,T1,T2,W,N2,Sel,LW,Seen,I1,Tail,LN1,LNt).

lnewiden_args(0,_F,_Term,_NewTerm,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN):- !.
lnewiden_args(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LNt):-
    arg(A,Term,Arg),
    lnsimplify_LW([F/A|Sel],LW,LW1),
    sort(LW1,LW1_s),
    lnewiden_elem_arg(Arg,NewArg,T1,T2,W,N2,[F/A|Sel],LW1_s,Seen,I,I1,LN,LN1),
    arg(A,NewTerm,NewArg),
    A1 is A - 1,
    lnewiden_args(A1,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I1,Tail,LN1,LNt).

lnewiden_elem(T,T,_T1,_T2,_W,_N2,_Sel,[],_Seen,I,I,LN,LN) :- !.
lnewiden_elem(T,T,_T1,_T2,_W,_N2,Sel,LW,_Seen,I,I,LN,LN):-
    compound_pure_type_term(T,_Term,F,_A),
    \+ lselismember([F/_|Sel],LW), !. % TODO: factorize
lnewiden_elem(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    lnewiden_args(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1),
    construct_compound_pure_type_term(NewTerm,NT).
lnewiden_elem(T,T,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN).

lnewiden_elem_arg(T,NT,_T1,T2,W,_N2,_Sel,_LW,Seen,I,I,LN,LN):- 
    get_typedef(T,_Def),
    ( T== T2 ->
        NT = W 
    ; member((T,NT),Seen)
    ),
    !.
lnewiden_elem_arg(T,T,_T1,_T2,_W,_N2,_Sel,[],_Seen,I,I,LN,LN) :- !.
lnewiden_elem_arg(T,NT,T1,T2,RW,N,Sel,LW,Seen,I,Tail,LN,LNt):-
    ( member((_,Sel,_,_),LW) ; member((Sel,_,_,_),LW) ),
    new_type_symbol(NT),
    findall((ONO,NT),member((Sel,_,ONO,_),LW),NewN,N),
    ( member((_,Sel,ON,_),LW) ->  
        findall(W,(member((_,Sel,ON,_),LW),member((ON,W),N)),WWW,[]), I1 = [NT|Tail], 
        dlist(WWW,LN1,LNt), % LN1 = [W|LNt], 
        Add = true
    ; I1 = Tail, LN1 = LNt, Add = false
    ),
    maybe_get_type_definition(T,DefT),
    ( get_typedef(T, Defin) -> 
        DefT = Defin,
        NewSeen = [(T,NT)|Seen]
    ; DefT = [T],
      NewSeen = Seen
    ),
    lnewiden_def(DefT,DefU,T1,T2,RW,NewN,Sel,LW,NewSeen,I,I1,LN,LN1),
    % display(user,'WWWWWWWWWWWWWW'),nl(user),
    sort(DefU,Def_s),   
    ( Add == true ->  
        sort(WWW,WWWs),
        merge(WWWs,Def_s,Def)
        % merge([W],Def_s,Def) 
    ; Def = Def_s
    ),
    insert_rule(NT,Def), !. % TODO: move this cut
%
lnewiden_elem_arg(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
    get_typedef(T,Def),!,
    ( member((T,NT),Seen) ->
        I = Tail,LN = LN1
    ; new_type_symbol(NT),
      lnewiden_def(Def,NewDef,T1,T2,W,N2,Sel,LW,[(T,NT)|Seen],I,Tail,LN,LN1),
      sort(NewDef,NewDef_s),
      insert_rule(NT,NewDef_s)
    ).
lnewiden_elem_arg(T,T,_T1,_T2,_W,_N2,Sel,LW,_Seen,I,I,LN,LN):-
    compound_pure_type_term(T,_Term,F,_A),
    \+ lselismember([F/_|Sel],LW), !. % TODO: factorize
lnewiden_elem_arg(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    lnewiden_args(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1),
    construct_compound_pure_type_term(NewTerm,NT).
lnewiden_elem_arg(T,T,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN).

:- export(make_determ_wide_rules/1). % TODO: only for evalterms.pl
make_determ_wide_rules([]).
make_determ_wide_rules([T|Rules]):-
    get_typedef(T, Def),
    % resetunion,
    make_deterministic(Def,NewDef), 
    SDef = NewDef,  %       simplify_def(NewDef,SDef,T),
    sort(SDef,SDef_s),
    retract_rule(T),
    insert_rule(T,SDef_s),
    make_determ_wide_rules(Rules).

% ---------------------------------------------------------------------------
%! # Etermsvar widening operator
% TODO: exactly like eterms version, but calls resetunion_VR/0, make_deterministic_VR/2

:- export(lnewiden_el_VR/4).
lnewiden_el_VR(T1,T2,_TEval,T1):- T1 == T2,!.
lnewiden_el_VR(_,(N,T),_TEval,(N,T)):- top_type(T),!.
lnewiden_el_VR((_N1,T1),(N2_e,T2),TEval,(N2,W)):-
    get_canonical_name(N2_e,N2),
    retract_type_name(N2,LWs,Count),        % equival_names
    laddcycles(LWs,LWss),
    lfilternames(LWss,N2,LWSS),
    ( LWSS == [] ->
        W=T2,
        insert_type_name(N2,LWs,Count)
    ;
        insert_type_name(N2,LWs,Count),
        ( TEval=yes, member((['$is'],_N),LWs) -> %% OJO REVISAR % TODO: ???
            get_less_numeric_type(T2,W)
        ;
            new_type_symbol(W),
            maybe_get_type_definition(T2,Def),
%               display(user,'start'),nl(user),
            lnewiden_def_VR(Def,NewDef,T1,T2,W,[(N2,W)],[],LWSS,[],I,[],ListofnewW,[W]), 
            sort(NewDef,NewDef_s),
            insert_rule(W,NewDef_s),
%               display(user,'end'),nl(user),
            sort(ListofnewW,ListofnewW_s),
            normalize_wide_rules_listOfnew(ListofnewW_s,I),
            resetunion_VR,
            make_determ_wide_rules_VR(I)
%               display(user,'endnor'),nl(user)
        )
    ).

lnewiden_def_VR([],[],_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN):- !.
lnewiden_def_VR([T|Def],[NT|NewDef],T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LNt):-
    lnewiden_elem_VR(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,I1,LN,LN1),
    lnewiden_def_VR(Def,NewDef,T1,T2,W,N2,Sel,LW,Seen,I1,Tail,LN1,LNt).

lnewiden_args_VR(0,_F,_Term,_NewTerm,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN):- !.
lnewiden_args_VR(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LNt):-
    arg(A,Term,Arg),
    lnsimplify_LW([F/A|Sel],LW,LW1),
    sort(LW1,LW1_s),
    lnewiden_elem_arg_VR(Arg,NewArg,T1,T2,W,N2,[F/A|Sel],LW1_s,Seen,I,I1,LN,LN1),
    arg(A,NewTerm,NewArg),
    A1 is A - 1,
    lnewiden_args_VR(A1,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I1,Tail,LN1,LNt).

lnewiden_elem_VR(T,T,_T1,_T2,_W,_N2,_Sel,[],_Seen,I,I,LN,LN) :- !.
lnewiden_elem_VR(T,T,_T1,_T2,_W,_N2,Sel,LW,_Seen,I,I,LN,LN):-
    compound_pure_type_term(T,_Term,F,_A),
    \+ lselismember([F/_|Sel],LW), !. % TODO: factorize
lnewiden_elem_VR(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    lnewiden_args_VR(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1),
    construct_compound_pure_type_term(NewTerm,NT).
lnewiden_elem_VR(T,T,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN).

lnewiden_elem_arg_VR(T,NT,_T1,T2,W,_N2,_Sel,_LW,Seen,I,I,LN,LN):- 
    get_typedef(T,_Def),
    ( T== T2 ->
        NT = W 
    ; member((T,NT),Seen)
    ),
    !.
lnewiden_elem_arg_VR(T,T,_T1,_T2,_W,_N2,_Sel,[],_Seen,I,I,LN,LN) :- !.
lnewiden_elem_arg_VR(T,NT,T1,T2,RW,N,Sel,LW,Seen,I,Tail,LN,LNt):-
    ( member((_,Sel,_,_),LW) ; member((Sel,_,_,_),LW) ),
    new_type_symbol(NT),
    findall((ONO,NT),member((Sel,_,ONO,_),LW),NewN,N),
    ( member((_,Sel,ON,_),LW) ->  
        findall(W,(member((_,Sel,ON,_),LW),member((ON,W),N)),WWW,[]), I1 = [NT|Tail], 
        dlist(WWW,LN1,LNt), % LN1 = [W|LNt], 
        Add = true
    ; I1 = Tail, LN1 = LNt, Add = false
    ),
    maybe_get_type_definition(T,DefT),
    ( get_typedef(T, Defin) -> 
        DefT = Defin,
        NewSeen = [(T,NT)|Seen]
    ; DefT = [T],
      NewSeen = Seen
    ),
    lnewiden_def_VR(DefT,DefU,T1,T2,RW,NewN,Sel,LW,NewSeen,I,I1,LN,LN1),
    % display(user,'WWWWWWWWWWWWWW'),nl(user),
    sort(DefU,Def_s),   
    ( Add == true ->  
        sort(WWW,WWWs),
        merge(WWWs,Def_s,Def)
        % merge([W],Def_s,Def) 
    ; Def = Def_s
    ),
    insert_rule(NT,Def), !. % TODO: move this cut
%
lnewiden_elem_arg_VR(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
    get_typedef(T,Def),!,
    ( member((T,NT),Seen) ->
        I = Tail,LN = LN1
    ; new_type_symbol(NT),
      lnewiden_def_VR(Def,NewDef,T1,T2,W,N2,Sel,LW,[(T,NT)|Seen],I,Tail,LN,LN1),
      sort(NewDef,NewDef_s),
      insert_rule(NT,NewDef_s)
    ).
lnewiden_elem_arg_VR(T,T,_T1,_T2,_W,_N2,Sel,LW,_Seen,I,I,LN,LN):-
    compound_pure_type_term(T,_Term,F,_A),
    \+ lselismember([F/_|Sel],LW), !. % TODO: factorize
lnewiden_elem_arg_VR(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    lnewiden_args_VR(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1),
    construct_compound_pure_type_term(NewTerm,NT).
lnewiden_elem_arg_VR(T,T,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN).

make_determ_wide_rules_VR([]).
make_determ_wide_rules_VR([T|Rules]):-
    get_typedef(T, Def),
    % resetunion_VR,
    make_deterministic_VR(Def,NewDef), 
    SDef = NewDef,  %       simplify_def(NewDef,SDef,T),
    sort(SDef,SDef_s),
    retract_rule(T),
    insert_rule(T,SDef_s),
    make_determ_wide_rules_VR(Rules).

% ---------------------------------------------------------------------------
% (common for lnewiden_el/4 and lnewiden_el_VR/4)

lselismember(Sel,[(_,S,_N,_C)|_LW]):-
    dlist(_,S,Sel), !. % TODO: move cut?
lselismember(Sel,[_|LW]):-
    lselismember(Sel,LW).

laddcycles([],[]).
laddcycles([(S,N)|LWs],[(S,N,[(S,N)])|LWss]):-
    laddcycles(LWs,LWss).

lnsimplify_LW(_,[],[]) :- !.
lnsimplify_LW(Sel,[(PS,S,N,C)|LW],[(PS,S,N,C)|LW1]):-
    dlist(_,S,Sel),!,
    lnsimplify_LW(Sel,LW,LW1).
lnsimplify_LW(Sel,[_|LW],LW1):-
    lnsimplify_LW(Sel,LW,LW1).

lfilternames([],_N2,[]) :- !.
lfilternames([(S,Nw,C)|LWs],Nw,[([],S,Nw,C)|LWW]):- !,
    lfilternames(LWs,Nw,LWW).
lfilternames([(S,N,C)|LWs],Nw,LWW1):-
    get_type_name(N,L),
    insert(C,(S,N),NC),
    lexpandandfilternames(L,S,NC,Nw,LWW1,LWW),
    lfilternames(LWs,Nw,LWW).

lexpandandfilternames([],_S,_C,_Nw,L,L) :- !.
lexpandandfilternames([(NS,NL)|L],S,C,Nw,[(PS,TS,NL,C)|LWP],LW1):-
    member((PS,NL),C),!,
    dlist(NS,TS,S),
    lexpandandfilternames(L,S,C,Nw,LWP,LW1).
lexpandandfilternames([(SL,Nw)|L],S,C,Nw,[([],NSL,Nw,C)|LWP],LW1):- !,
    dlist(SL,NSL,S),        
    lexpandandfilternames(L,S,C,Nw,LWP,LW1).
lexpandandfilternames([(SL,NL)|L],S,C,Nw,LWP,LW1):-
    dlist(SL,NSL,S),        
    get_type_name(NL,LL),   
    insert(C,(NSL,NL),NC),
    lexpandandfilternames(LL,NSL,NC,Nw,LWP,LWP1),
    lexpandandfilternames(L,S,C,Nw,LWP1,LW1).

normalize_wide_rules_listOfnew([],_).
normalize_wide_rules_listOfnew([W|ListofnewW],I):-
    normalize_wide_rules_ow(I,W),   
    normalize_wide_rules_listOfnew(ListofnewW,I).

normalize_wide_rules_ow([],_).
normalize_wide_rules_ow([T|Rules],W):-
    get_typedef(T, Def),
    member(W,Def),!,
    ord_delete(Def,W,U),
    get_typedef(W,DefW),
    merge(DefW,U,NewDef),
    retract_rule(T),
    insert_rule(T,NewDef), 
    normalize_wide_rules_ow(Rules,W).
normalize_wide_rules_ow([_|Rules],W):-
    normalize_wide_rules_ow(Rules,W).

% ---------------------------------------------------------------------------
%! # evalterms (old?) widening operator
% ``Type Graph Jungle Widening''

% TODO: see evalterms.pl for details

:- export(ewiden_el/5).
ewiden_el(T1,T2,T1,_TEval,_Depthk):- T1 == T2,!.
ewiden_el(_,(N,T),(N,T),_TEval,_Depthk):- top_type(T),!.
ewiden_el((_N1,T1),(N2,T2),(N2,W),TEval,Depthk):-
    % get_canonical_name(N2_e,N2), % TODO: new in lnewiden_el
    retract_type_name(N2,LWs,Count),
    %       obtain_all_names_selectors_EV(LWs,N2,[],[],LW1,[]),
    % in order to manage the case when there is not relation between the new approximation and the older
    % % %   obtain_all_names_selectors_EV(LWs,N2,[],[],LW1,[],[N2|L]),
    obtain_all_names_selectors_EV(LWs,N2,[],[],LW1,[],[N2]),
    % in order to manage the case when there is not relation between the new approximation and the older
    sort(LW1,LW),
    % findall((S,N2),member((S,N2),LWs),LW,[]), % here, the clausure
    ( LW == [] ->
        ( Count < 5 ->
            W = T2,
            Count1 is Count + 1,
            insert_type_name(N2,LWs,Count1)
        ; shortening_el(T2,W,Depthk),
          insert_type_name(N2,LWs,0)           
        )
    ; insert_type_name(N2,LWs,0),
      ( TEval=yes, member((['$is'],_N),LW) ->
          get_less_numeric_type(T2,W)
      ; new_type_symbol(W),
        maybe_get_type_definition(T2,Def),
        ewiden_def(Def,NewDef,T1,T2,W,[],LW,[],I,[]), 
        sort(NewDef,NewDef_s),
        insert_rule(W,NewDef_s),
        normalize_wide_rules_EV(I,W),
        % resetunion, % TODO: lnewiden_el/4 does resetunion here, why?
        make_determ_wide_rules(I)
      )
    ).

%    [...]
%    restrict_labels(LWs,W,NLW),   % here, is  not necesary
%    update_labels(NLW,NewLW,N2),   
%    sort(NewLW,NewLW_s),
%    insert_type_name(N2,NewLW_s).
%
% restrict_labels([],_W,[]).
% restrict_labels([(S,N)|LW],W,[(S,N)|NLW]):-
%       get_sub_term(S,W,_Subterm),!,
%       restrict_labels(LW,W,NLW).
% restrict_labels([_|LW],W,NLW):-
%       restrict_labels(LW,W,NLW).
%
% update_labels(LW,NewLW,N2):-
%       findall((S,N2),member((S,N2),LW),List,[]),
%       update_labels0(LW,NewLW,N2,List).
%
% update_labels0([],[],_N2,_List).
% update_labels0([(S,T)|LW],New,N2,List):-
% %     (
% %         T == N2 -> New = [(S,T)|NewLW]     % cambio
% %         T == N2 -> New = NewLW
% %     ;
%           (
%               ancestor(S,List) -> 
%                       New = NewLW 
%           ;
%               New = [(S,T)|NewLW]
%           ),
% %     ),
%       update_labels0(LW,NewLW,N2,List).
%
% ancestor(_S,[]):- !,fail.
% ancestor(S,[(WS,_)|_List]):-
%       dlist([_|_],WS,S),!.
% ancestor(S,[_|List]):-
%       ancestor(S,List).

ewiden_def([],[],_T1,_T2,_W,_Sel,_LW,_Seen,I,I).
ewiden_def([T|Def],[NT|NewDef],T1,T2,W,Sel,LW,Seen,I,Tail):-
    ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,I1),
    ewiden_def(Def,NewDef,T1,T2,W,Sel,LW,Seen,I1,Tail).

ewiden_args(0,_F,_Term,_NewTerm,_T1,_T2,_W,_Sel,_LW,_Seen,I,I) :- !.
ewiden_args(A,F,Term,NewTerm,T1,T2,W,Sel,LW,Seen,I,Tail):-
    arg(A,Term,Arg),
    simplify_LW([F/A|Sel],LW,LW1),
    ewiden_elem(Arg,NewArg,T1,T2,W,[F/A|Sel],LW1,Seen,I,I1),
    arg(A,NewTerm,NewArg),
    A1 is A - 1,
    ewiden_args(A1,F,Term,NewTerm,T1,T2,W,Sel,LW,Seen,I1,Tail).

simplify_LW(_,[],[]).
simplify_LW(Sel,[(S,N)|LW],[(S,N)|LW1]):-
    dlist(_,S,Sel),!,
    simplify_LW(Sel,LW,LW1).
simplify_LW(Sel,[_|LW],LW1):-
    simplify_LW(Sel,LW,LW1).

ewiden_elem(T,W,_T1,T2,W,_Sel,_LW,_Seen,I,I):- 
    get_typedef(T,_Def),T== T2,!.
ewiden_elem(T,NT,_T1,_T2,_W,_Sel,[],Seen,I,I):-
    replace_EV(T,NT,Seen,[]).
ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,Tail):-
    member((Sel,N),LW),!,
    ( ( T == T1; dz_type_included(T,T2)) ->
        NT = W,I=Tail
    ; new_type_symbol(NT),
      % ( get_typedef(T1,_Def) ->
      %     replace_EV(T,T1,T1,W,U,[])  % acaaaa
      % ; U = T
      % ),
      % maybe_get_type_definition(U,DefU),
      ord_delete(LW,(Sel,N),LW1),
      %
      maybe_get_type_definition(T,DefT),
      ( get_typedef(T, Defin) -> 
          DefT = Defin,
          NewSeen = [(T,NT)|Seen]
      ; DefT = [T],
        NewSeen = Seen
      ),
      ewiden_def(DefT,DefU,T1,T2,W,Sel,LW1,NewSeen,I,I1),
      %
      merge([W],DefU,Def),
      insert_rule(NT,Def),
      I1 = [NT|Tail]
    ).
ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,Tail):-
    get_typedef(T,Def),!,
    ( member((T,NT),Seen) ->
        I = Tail
    ; new_type_symbol(NT),
      ewiden_def(Def,NewDef,T1,T2,W,Sel,LW,[(T,NT)|Seen],I,Tail),
      sort(NewDef,NewDef_s),
      insert_rule(NT,NewDef_s)
    ).
ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,Tail):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    ewiden_args(A,F,Term,NewTerm,T1,T2,W,Sel,LW,Seen,I,Tail),
    construct_compound_pure_type_term(NewTerm,NT).
ewiden_elem(T,T,_T1,_T2,_W,_Sel,_LW,_Seen,I,I).

% TODO: older version for evalterms, see newer replace/6
replace_EV(T,NT,P,Seen):-
    get_typedef(T,Def),!,
    ( member((T,NT),P) ->
        true
    ; member(T,Seen) ->
        NT = T
    ; replace_def_EV(Def,NewDef,P,[T|Seen]),
      ( Def == NewDef ->
          NT = T
      ; new_type_symbol(NT),                
        sort(NewDef,NewDef_s),
        insert_rule(NT,NewDef_s)
      )
    ).
replace_EV(T,NT,P,Seen):-
    compound_pure_type_term(T,Term,F,A),!,
    functor(NewTerm,F,A),
    replace_arg_EV(A,Term,NewTerm,P,Seen),
    construct_compound_pure_type_term(NewTerm,NT).
replace_EV(T,T,_,_).
            
replace_def_EV([],[],_P,_Seen).
replace_def_EV([T|Def],[NT|NewDef],P,Seen):-
    replace_EV(T,NT,P,Seen),
    replace_def_EV(Def,NewDef,P,Seen). 

replace_arg_EV(0,_,_,_,_) :- !.
replace_arg_EV(A,Term,NewTerm,P,Seen):-
    arg(A,Term,Arg),
    replace_EV(Arg,NArg,P,Seen),
    arg(A,NewTerm,NArg),
    A1 is A - 1,
    replace_arg_EV(A1,Term,NewTerm,P,Seen).

normalize_wide_rules_EV([],_).
normalize_wide_rules_EV([T|Rules],W):-
    get_typedef(T, Def),
    ord_delete(Def,W,U),
    get_typedef(W,DefW),
    merge(DefW,U,NewDef),
    retract_rule(T),
    insert_rule(T,NewDef), 
    normalize_wide_rules_EV(Rules,W).
    
obtain_all_names_selectors_EV([],_N2,_,_,L,L,_).
obtain_all_names_selectors_EV([(S,N)|LWs],N2,Sel,Seen,NL,Tail,Syn):-
    % in order to manage the case when there is not relation between the new approximation and the older
    member(N,Syn) ,!,
    % in order to manage the case when there is not relation between the new approximation and the older

    % N == N2,!,
    append(S,Sel,S1),
    ( S1 = [] -> NL = LW ;  NL = [(S1,N2)|LW]),
    obtain_all_names_selectors_EV(LWs,N2,Sel,Seen,LW,Tail,Syn).
obtain_all_names_selectors_EV([(_S,N)|LWs],N2,Sel,Seen,LW,Tail,Syn):-
    member(N,Seen),!,
    obtain_all_names_selectors_EV(LWs,N2,Sel,Seen,LW,Tail,Syn).
obtain_all_names_selectors_EV([(S,N)|LWs],N2,Sel,Seen,LW,Tail,Syn):-
    get_type_name(N,L),
    append(S,Sel,S1),
    obtain_all_names_selectors_EV(L,N2,S1,[N|Seen],LW,LW1,Syn),
    obtain_all_names_selectors_EV(LWs,N2,Sel,Seen,LW1,Tail,Syn).

% ===========================================================================
% (common)

:- export(get_less_numeric_type/2).
:- pred get_less_numeric_type(+T,-T2)
   # "Approximate @var{T} to the closest predefined numeric type
   (int,flt, or num). Assumes that @var{T} is numeric.".
% TODO: rename predicate? type_approx_numeric?
get_less_numeric_type(T,T2) :- dz_type_included(T,int), !, T2 = int.
get_less_numeric_type(T,T2) :- dz_type_included(T,flt), !, T2 = flt.
get_less_numeric_type(_T,num).

% ---------------------------------------------------------------------------

:- export(get_canonical_name/2). % (internal?)
% TODO: rename? document
get_canonical_name(N,Canonical):-
    get_equiv_name(N,Canonical),!.
get_canonical_name(N,N):- !.

