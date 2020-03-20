# Regular Types Library

This library implements basic routines for storing and manipulating
regular types. These operations are used in CiaoPP domains, analysis,
and program transformations.

The main library module is `typeslib.pl`. See
`typeslib(typeslib_hooks)` and `typeslib_flag/1` for hooks defining
the library parameters. The interface to this library is defined by
the following predicates:

 - Initialization, cleanup, serialization: `post_init_types/0`,
   `cleanup_types/0`, `gen_lib_type_info/1`, `load_lib_type_info/1`,
   `cleanup_lib_type_info/0`, `dump_types/2`, `restore_types/2`.

 - Transform from/to predicate (property) notation:
   `legal_user_type_pred/1`, `insert_user_type_pred_def/2`,
   `pretty_type_lit_rules/4`, `pretty_type_lit_rules_desimp/2`,
   `typedef_to_pred/3`, `revert_type_internal/3`, `revert_types/5`
   (requires `revert_type_internal/3`).

 - Type creation (as an object in the type db):
   `create_new_type_rule/2` (`new_type_symbol/1`+`insert_rule/2`),
   `new_type_symbol/1`, `insert_rule/2`, `normalize_type/2` (ensure
   that it is a type symbol), `type_escape_term_list/2`
   (`escaped_type/2` on a list), `make_prop_type_unary/2`.
  
 - Basic elements of the type lattice: `pure_type_term/1` (prop),
   `native_type_symbol/1`, `set_atom_type/1`, `set_float_type/1`,
   `set_ground_type/1`, `set_int_type/1`, `set_numeric_type/1`,
   `set_numexp_type/1`, `top_type/1`, `set_top_type/1`, `var_type/1`,
   `set_var_type/1`, `bot_type/1`, `set_bottom_type/1`,
   `compound_pure_type_term/4`, `construct_compound_pure_type_term/2`.

 - Inspect type definition: `get_type_definition/2`,
   `maybe_get_type_definition/2`.

 - Type name annotations (for structural widening): `get_type_name/2`,
   `insert_type_name/3` `new_type_name/1`, `retract_type_name/3`,
   `get_canonical_name/2`, `get_equiv_name/2`, `insert_equiv_name/2`,
   `retract_equiv_name/2`, `lab_intersect/2`.

 - Widening operators: `approx_as_defined/2`, `ewiden_el/5`,
   `hentenwid/3`, `lnewiden_el/4`, `lnewiden_el_VR/4`,
   `shortening_el/3`, `terms_naive_ewiden_el/2`,
   `get_less_numeric_type/2`.

 - Union and intersection of types: `type_intersection_0/3`,
   `type_intersection_2/3`, `type_intersection_2_VR/3`,
   `def_type_lub/3`, `resetunion/0`, `resetunion_VR/0`,
   `type_union/3`, `type_union_NoDB/4`, `type_union_VR/3`,
   `def_type_glb/3`.

 - Type inclusion and equivalence: `dz_type_included/2`,
   `edz_type_included/5` (for sized types, depends on multifile
   `edz_postprocess_relations/4`), `dz_equivalent_types/2` (based on
   `dz_type_included/2`) `def_subtype/2`, `def_equivalent_types/2`
   (based on `def_subtype/2`), `set_param_matching_mode/1`,
   `belongs_to_type/2` (`escaped_type/2`+`dz_type_included/2`).

 - Other checks and operations on types: `is_empty_type/1`,
   `is_ground_type/1`, `concrete/4`, `partial_concrete/4`,
   `equivalent_to_top_type/1`, `equivalent_to_numeric/1`,
   `contains_type_param/1`, `get_compatible_types/4`,
   `find_type_functor/5` (see `get_compatible_types/4`),
   `is_infinite_type/1`, `finite_unfold/2`, `not_expandible_type/1`.

 - Garbage collection and simplification of types:
   `assert_required_type/1`, `get_required_types/1` (postprocess in
   `typedef(::=(_,_))` format), `simplify_step2/0`, `equiv_type/2`
   (representative type after simplification),
   `replace_non_par_rule_type_symbol/2` (obtain the corresponding
   parametric type symbol)

 - Debugging: `show_types/0`, `show_types_raw_printer/0`.

Other experimental features:

 - Random sampling (`typeslib(rnd_type_value)`): `rnd_type_value/2`
   (see multifile hooks)
