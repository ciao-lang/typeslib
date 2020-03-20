% (included from typeslib.pl)
% TODO: document, merge into other file?

type_intersection_2_VR(Type1, Type2, Intersect):-
    dz_type_included(Type1, Type2),
    !,
    Intersect = Type1.
type_intersection_2_VR(Type1, Type2, Intersect):-
    dz_type_included(Type2, Type1),
    !,
    Intersect = Type2.
type_intersection_2_VR(Type1, Type2, Intersect):-
    debug_message("Performing full intersection of ~q and ~q.", [Type1, Type2]), % TODO: remove
    pp_type_intersection_VR(Type1, Type2, Intersect),
    debug_message("Intersection of ~q and ~q is ~q.", [Type1, Type2, Intersect]). % TODO: remove
 %% type_intersection_2(Type1, Type2, Intersect):-
 %%     Intersect = Type2,
 %%     warning_message("No inclusion relationship between types ~q and ~q.",[Type1, Type2]),
 %%     warning_message("Assumed that the intersection is ~q. This can be improved by performing full intersection.", [Intersect]).
   

pp_type_intersection_VR(Typ1, Typ2, Inter):-
     % Calls the special intersection which treats var as top
     typeslib:type_intersection_VR(Typ1, Typ2, Intersec),
     !, 
     ( is_empty_type(Intersec) -> 
         clean_after_empty_pp_type_intersection,
         set_bottom_type(Inter)
     ; simplify_types_after_pp_type_intersection,
       replace_one_equiv_type(Intersec, Inter)
     ).

