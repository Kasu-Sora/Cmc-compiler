#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#require "userlib/proof.c"
#include "userlib/array.h"
#require "userlib/array.c"
#include "cmc_abi.h"
#require "cmc_abi.c"
#include "cmc_codegen.h"
#require "cmc_codegen.c"
#include "cmc_rep.h"

PROOF static size_t _cmc_rep_axioms_before = vector_size(get_all_axioms());

PROOF static int _cmc_rep_struct_names = (
    new_const("Tcm_expr", get_struct_name_type()),
    new_const("Tcm_arg", get_struct_name_type()),
    new_const("Tcm_stmt", get_struct_name_type()),
    new_const("Tcm_slot", get_struct_name_type()),
    new_const("Tcm_member", get_struct_name_type()),
    new_const("Tcm_struct", get_struct_name_type()),
    new_const("Tcm_global", get_struct_name_type()),
    new_const("Tcm_string", get_struct_name_type()),
    new_const("Tcm_function", get_struct_name_type()),
    new_const("Tcm_program", get_struct_name_type()),
    new_const("Tcm_output", get_struct_name_type()), 0);

PROOF static int _cmc_rep_field_names = (
    new_const("Fkind", get_field_type()),
    new_const("Fop", get_field_type()),
    new_const("Fty", get_field_type()),
    new_const("Fvalue", get_field_type()),
    new_const("Fa", get_field_type()),
    new_const("Fb", get_field_type()),
    new_const("Fargs", get_field_type()),
    new_const("Fexpr", get_field_type()),
    new_const("Fnext", get_field_type()),
    new_const("Fslot", get_field_type()),
    new_const("Fcount", get_field_type()),
    new_const("Fmembers", get_field_type()),
    new_const("Fhas_init", get_field_type()),
    new_const("Finit", get_field_type()),
    new_const("Fbytes", get_field_type()),
    new_const("Flength", get_field_type()),
    new_const("Fret_ty", get_field_type()),
    new_const("Fparams", get_field_type()),
    new_const("Flocals", get_field_type()),
    new_const("Fbody", get_field_type()),
    new_const("Fstructs", get_field_type()),
    new_const("Fglobals", get_field_type()),
    new_const("Fstrings", get_field_type()),
    new_const("Ffunctions", get_field_type()),
    new_const("Fmain_id", get_field_type()),
    new_const("Fops", get_field_type()),
    new_const("Fimms", get_field_type()),
    new_const("Fdata", get_field_type()),
    new_const("Fcode_capacity", get_field_type()),
    new_const("Fdata_capacity", get_field_type()),
    new_const("Fcode_length", get_field_type()),
    new_const("Fdata_length", get_field_type()),
    new_const("Fentry", get_field_type()), 0);

PROOF thm cm_rep_expr_kind_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(cm_rep_expr_kind (CMConstE (n:int) (ty:cm_type)) = 0i) &&
     (cm_rep_expr_kind (CMStringE (sid:int) (ty:cm_type)) = 1i) &&
     (cm_rep_expr_kind (CMVarE (scope:int) (slot:int) (ty:cm_type)) = 2i) &&
     (!dst src ty. cm_rep_expr_kind
        (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) = 3i) &&
     (!op left right ty. cm_rep_expr_kind
        (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = 4i) &&
     (!op arg ty. cm_rep_expr_kind
        (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) = 5i) &&
     (!base index ty. cm_rep_expr_kind
        (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) = 6i) &&
     (!base mid ty. cm_rep_expr_kind
        (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) = 7i) &&
     (!fid args ty. cm_rep_expr_kind
        (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) = 8i) &&
     (!asked ty. cm_rep_expr_kind
        (CMSizeofE (asked:cm_type) (ty:cm_type)) = 9i) &&
     (!ty. cm_rep_expr_kind (CMGetcE (ty:cm_type)) = 10i) &&
     (!arg ty. cm_rep_expr_kind
        (CMPutcE (arg:cm_expr) (ty:cm_type)) = 11i) &&
     (!arg ty. cm_rep_expr_kind
        (CMPutiE (arg:cm_expr) (ty:cm_type)) = 12i) &&
     (!arg ty. cm_rep_expr_kind
        (CMExitE (arg:cm_expr) (ty:cm_type)) = 13i) &&
     (cm_rep_expr_kinds ([]:(cm_expr)list) = ([]:(int)list)) &&
     (!arg args. cm_rep_expr_kinds
        ((arg:cm_expr)::(args:(cm_expr)list)) =
        cm_rep_expr_kind arg :: cm_rep_expr_kinds args)`);

PROOF static thm prove_cm_expr_shape(
    const term statement, const term kind_fact, size_t target,
    const term_list witnesses, const term shape_fact) {
  gnode root = gnode_new_with_ccl(statement);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`e:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "He");
  for (size_t i = 0; i < 14; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "He");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "He", NULL);
    }
  }
  for (size_t i = 0; i < 14; ++i) {
    if (i == target) continue;
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    int index = labeled_term_list_index(assumptions, "He");
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(assumptions[index].tm), cm_rep_expr_kind_def)),
        assume_rule(kind_fact));
    CONTR_TAC(cases[i], impossible);
  }
  gnode selected = cases[target];
  for (size_t i = 0; i < vector_size(witnesses); ++i) {
    selected = EXISTS_TAC(selected, witnesses[i]);
  }
  ACCEPT_TAC(selected, assume_rule(shape_fact));
  return gnode_prove(root);
}

PROOF thm cm_expr_const_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 0i ==>
     exists n ty. e == CMConstE (n:int) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 0i`, 0,
    TERM_LIST(`a0:int`, `a1:cm_type`),
    `e == CMConstE (a0:int) (a1:cm_type)`);
PROOF thm cm_expr_string_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 1i ==>
     exists sid ty. e == CMStringE (sid:int) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 1i`, 1,
    TERM_LIST(`a0:int`, `a1:cm_type`),
    `e == CMStringE (a0:int) (a1:cm_type)`);
PROOF thm cm_expr_var_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 2i ==>
     exists scope slot ty.
       e == CMVarE (scope:int) (slot:int) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 2i`, 2,
    TERM_LIST(`a0:int`, `a1:int`, `a2:cm_type`),
    `e == CMVarE (a0:int) (a1:int) (a2:cm_type)`);
PROOF thm cm_expr_assign_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 3i ==>
     exists dst src ty.
       e == CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 3i`, 3,
    TERM_LIST(`a0:cm_expr`, `a1:cm_expr`, `a2:cm_type`),
    `e == CMAssignE (a0:cm_expr) (a1:cm_expr) (a2:cm_type)`);
PROOF thm cm_expr_binary_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 4i ==>
     exists op left right ty.
       e == CMBinaryE (op:int) (left:cm_expr)
              (right:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 4i`, 4,
    TERM_LIST(`a0:int`, `a1:cm_expr`, `a2:cm_expr`,
              `a3:cm_type`),
    `e == CMBinaryE (a0:int) (a1:cm_expr)
            (a2:cm_expr) (a3:cm_type)`);
PROOF thm cm_expr_unary_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 5i ==>
     exists op arg ty.
       e == CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 5i`, 5,
    TERM_LIST(`a0:int`, `a1:cm_expr`, `a2:cm_type`),
    `e == CMUnaryE (a0:int) (a1:cm_expr) (a2:cm_type)`);
PROOF thm cm_expr_index_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 6i ==>
     exists base index ty.
       e == CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 6i`, 6,
    TERM_LIST(`a0:cm_expr`, `a1:cm_expr`, `a2:cm_type`),
    `e == CMIndexE (a0:cm_expr) (a1:cm_expr) (a2:cm_type)`);
PROOF thm cm_expr_member_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 7i ==>
     exists base mid ty.
       e == CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 7i`, 7,
    TERM_LIST(`a0:cm_expr`, `a1:int`, `a2:cm_type`),
    `e == CMMemberE (a0:cm_expr) (a1:int) (a2:cm_type)`);
PROOF thm cm_expr_call_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 8i ==>
     exists fid args ty.
       e == CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 8i`, 8,
    TERM_LIST(`a0:int`, `a1:(cm_expr)list`, `a2:cm_type`),
    `e == CMCallE (a0:int) (a1:(cm_expr)list) (a2:cm_type)`);
PROOF thm cm_expr_sizeof_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 9i ==>
     exists asked ty.
       e == CMSizeofE (asked:cm_type) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 9i`, 9,
    TERM_LIST(`a0:cm_type`, `a1:cm_type`),
    `e == CMSizeofE (a0:cm_type) (a1:cm_type)`);
PROOF thm cm_expr_getc_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 10i ==>
     exists ty. e == CMGetcE (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 10i`, 10,
    TERM_LIST(`a:cm_type`), `e == CMGetcE (a:cm_type)`);
PROOF thm cm_expr_putc_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 11i ==>
     exists arg ty. e == CMPutcE (arg:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 11i`, 11,
    TERM_LIST(`a0:cm_expr`, `a1:cm_type`),
    `e == CMPutcE (a0:cm_expr) (a1:cm_type)`);
PROOF thm cm_expr_puti_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 12i ==>
     exists arg ty. e == CMPutiE (arg:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 12i`, 12,
    TERM_LIST(`a0:cm_expr`, `a1:cm_type`),
    `e == CMPutiE (a0:cm_expr) (a1:cm_type)`);
PROOF thm cm_expr_exit_shape = prove_cm_expr_shape(
    `!e. cm_rep_expr_kind (e:cm_expr) == 13i ==>
     exists arg ty. e == CMExitE (arg:cm_expr) (ty:cm_type)`,
    `cm_rep_expr_kind (e:cm_expr) == 13i`, 13,
    TERM_LIST(`a0:cm_expr`, `a1:cm_type`),
    `e == CMExitE (a0:cm_expr) (a1:cm_type)`);

PROOF thm mk_cm_rep_expr_kind_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!e. 0i <= cm_rep_expr_kind (e:cm_expr) &&
           cm_rep_expr_kind e <= 13i`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`e:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "He");
  for (size_t i = 0; i < 14; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "He");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "He", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv,
        THM_LIST(cm_rep_expr_kind_def));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_expr_kind_bounds = mk_cm_rep_expr_kind_bounds();

PROOF thm mk_cm_rep_expr_kind_exhaustive(void) {
  thm bounds = spec_rule(`e:cm_expr`, cm_rep_expr_kind_bounds);
  thm impossible = mp_rule(int_arith_rule(
      `(0i <= cm_rep_expr_kind (e:cm_expr) &&
        cm_rep_expr_kind e <= 13i) ==>
       ~(cm_rep_expr_kind e == 0i) ==>
       ~(cm_rep_expr_kind e == 1i) ==>
       ~(cm_rep_expr_kind e == 2i) ==>
       ~(cm_rep_expr_kind e == 3i) ==>
       ~(cm_rep_expr_kind e == 4i) ==>
       ~(cm_rep_expr_kind e == 5i) ==>
       ~(cm_rep_expr_kind e == 6i) ==>
       ~(cm_rep_expr_kind e == 7i) ==>
       ~(cm_rep_expr_kind e == 8i) ==>
       ~(cm_rep_expr_kind e == 9i) ==>
       ~(cm_rep_expr_kind e == 10i) ==>
       ~(cm_rep_expr_kind e == 11i) ==>
       ~(cm_rep_expr_kind e == 12i) ==>
       ~(cm_rep_expr_kind e == 13i) ==> F`),
      bounds);
  return gen_rule(`e:cm_expr`, impossible);
}
PROOF thm cm_rep_expr_kind_exhaustive =
    mk_cm_rep_expr_kind_exhaustive();

PROOF static thm prove_cm_expr_shape_ent(
    const term statement, const thm shape_theorem,
    const term kind_fact, const const_cstr_list names,
    const term_list witnesses, const term shape_fact) {
  gnode root = gnode_new_with_ccl(statement);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm shaped = mp_rule(spec_rule(`e:cm_expr`, shape_theorem),
      assume_rule(kind_fact));
  gnode with_shape = ASSUME_TAC(introduced, shaped, "Hs");
  for (size_t i = 0; i < vector_size(names); ++i) {
    with_shape = ASMP_EXISTS_TAC(with_shape, "Hs", names[i]);
  }
  gnode_list initialized = AUTO_INIT_SLTAC(with_shape);
  gnode selected = initialized[0];
  for (size_t i = 0; i < vector_size(witnesses); ++i) {
    selected = EXISTS_SLTAC(selected, witnesses[i]);
  }
  gnode fact_goal = AUTO_INTRO_FACT_SLTAC(selected);
  gnode_list pure = PURE_SLTAC(fact_goal);
  ACCEPT_TAC(pure[0], assume_rule(shape_fact));
  AUTO_FRAME_SLTAC(pure[1]);
  return gnode_prove(root);
}

PROOF thm cm_expr_const_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 0i ==>
     (emp |-- exists n ty.
       fact(e == CMConstE (n:int) (ty:cm_type)))`,
    cm_expr_const_shape, `cm_rep_expr_kind (e:cm_expr) == 0i`,
    CONST_STRING_LIST("n_", "ty_"),
    TERM_LIST(`n_:int`, `ty_:cm_type`),
    `e == CMConstE (n_:int) (ty_:cm_type)`);
PROOF thm cm_expr_string_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 1i ==>
     (emp |-- exists sid ty.
       fact(e == CMStringE (sid:int) (ty:cm_type)))`,
    cm_expr_string_shape, `cm_rep_expr_kind (e:cm_expr) == 1i`,
    CONST_STRING_LIST("sid_", "ty_"),
    TERM_LIST(`sid_:int`, `ty_:cm_type`),
    `e == CMStringE (sid_:int) (ty_:cm_type)`);
PROOF thm cm_expr_var_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 2i ==>
     (emp |-- exists scope slot ty.
       fact(e == CMVarE (scope:int) (slot:int) (ty:cm_type)))`,
    cm_expr_var_shape, `cm_rep_expr_kind (e:cm_expr) == 2i`,
    CONST_STRING_LIST("scope_", "slot_", "ty_"),
    TERM_LIST(`scope_:int`, `slot_:int`, `ty_:cm_type`),
    `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
PROOF thm cm_expr_assign_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 3i ==>
     (emp |-- exists dst src ty.
       fact(e == CMAssignE (dst:cm_expr)
         (src:cm_expr) (ty:cm_type)))`,
    cm_expr_assign_shape, `cm_rep_expr_kind (e:cm_expr) == 3i`,
    CONST_STRING_LIST("dst_", "src_", "ty_"),
    TERM_LIST(`dst_:cm_expr`, `src_:cm_expr`, `ty_:cm_type`),
    `e == CMAssignE (dst_:cm_expr) (src_:cm_expr) (ty_:cm_type)`);
PROOF thm cm_expr_binary_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 4i ==>
     (emp |-- exists op left right ty.
       fact(e == CMBinaryE (op:int) (left:cm_expr)
         (right:cm_expr) (ty:cm_type)))`,
    cm_expr_binary_shape, `cm_rep_expr_kind (e:cm_expr) == 4i`,
    CONST_STRING_LIST("op_", "left_", "right_", "ty_"),
    TERM_LIST(`op_:int`, `left_:cm_expr`, `right_:cm_expr`,
              `ty_:cm_type`),
    `e == CMBinaryE (op_:int) (left_:cm_expr)
      (right_:cm_expr) (ty_:cm_type)`);
PROOF thm cm_expr_unary_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 5i ==>
     (emp |-- exists op arg ty.
       fact(e == CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)))`,
    cm_expr_unary_shape, `cm_rep_expr_kind (e:cm_expr) == 5i`,
    CONST_STRING_LIST("op_", "arg_", "ty_"),
    TERM_LIST(`op_:int`, `arg_:cm_expr`, `ty_:cm_type`),
    `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
PROOF thm cm_expr_index_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 6i ==>
     (emp |-- exists base index ty.
       fact(e == CMIndexE (base:cm_expr)
         (index:cm_expr) (ty:cm_type)))`,
    cm_expr_index_shape, `cm_rep_expr_kind (e:cm_expr) == 6i`,
    CONST_STRING_LIST("base_", "index_", "ty_"),
    TERM_LIST(`base_:cm_expr`, `index_:cm_expr`, `ty_:cm_type`),
    `e == CMIndexE (base_:cm_expr) (index_:cm_expr) (ty_:cm_type)`);
PROOF thm cm_expr_member_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 7i ==>
     (emp |-- exists base mid ty.
       fact(e == CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)))`,
    cm_expr_member_shape, `cm_rep_expr_kind (e:cm_expr) == 7i`,
    CONST_STRING_LIST("base_", "mid_", "ty_"),
    TERM_LIST(`base_:cm_expr`, `mid_:int`, `ty_:cm_type`),
    `e == CMMemberE (base_:cm_expr) (mid_:int) (ty_:cm_type)`);
PROOF thm cm_expr_call_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 8i ==>
     (emp |-- exists fid args ty.
       fact(e == CMCallE (fid:int)
         (args:(cm_expr)list) (ty:cm_type)))`,
    cm_expr_call_shape, `cm_rep_expr_kind (e:cm_expr) == 8i`,
    CONST_STRING_LIST("fid_", "args_", "ty_"),
    TERM_LIST(`fid_:int`, `args_:(cm_expr)list`, `ty_:cm_type`),
    `e == CMCallE (fid_:int) (args_:(cm_expr)list) (ty_:cm_type)`);
PROOF thm cm_expr_sizeof_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 9i ==>
     (emp |-- exists asked ty.
       fact(e == CMSizeofE (asked:cm_type) (ty:cm_type)))`,
    cm_expr_sizeof_shape, `cm_rep_expr_kind (e:cm_expr) == 9i`,
    CONST_STRING_LIST("asked_", "ty_"),
    TERM_LIST(`asked_:cm_type`, `ty_:cm_type`),
    `e == CMSizeofE (asked_:cm_type) (ty_:cm_type)`);
PROOF thm cm_expr_getc_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 10i ==>
     (emp |-- exists ty. fact(e == CMGetcE (ty:cm_type)))`,
    cm_expr_getc_shape, `cm_rep_expr_kind (e:cm_expr) == 10i`,
    CONST_STRING_LIST("ty_"), TERM_LIST(`ty_:cm_type`),
    `e == CMGetcE (ty_:cm_type)`);
PROOF thm cm_expr_putc_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 11i ==>
     (emp |-- exists arg ty.
       fact(e == CMPutcE (arg:cm_expr) (ty:cm_type)))`,
    cm_expr_putc_shape, `cm_rep_expr_kind (e:cm_expr) == 11i`,
    CONST_STRING_LIST("arg_", "ty_"),
    TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`),
    `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
PROOF thm cm_expr_puti_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 12i ==>
     (emp |-- exists arg ty.
       fact(e == CMPutiE (arg:cm_expr) (ty:cm_type)))`,
    cm_expr_puti_shape, `cm_rep_expr_kind (e:cm_expr) == 12i`,
    CONST_STRING_LIST("arg_", "ty_"),
    TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`),
    `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
PROOF thm cm_expr_exit_shape_ent = prove_cm_expr_shape_ent(
    `!e. cm_rep_expr_kind (e:cm_expr) == 13i ==>
     (emp |-- exists arg ty.
       fact(e == CMExitE (arg:cm_expr) (ty:cm_type)))`,
    cm_expr_exit_shape, `cm_rep_expr_kind (e:cm_expr) == 13i`,
    CONST_STRING_LIST("arg_", "ty_"),
    TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`),
    `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);

PROOF thm cm_rep_expr_op_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(cm_rep_expr_op (CMConstE (n:int) (ty:cm_type)) = 0i) &&
     (cm_rep_expr_op (CMStringE (sid:int) (ty:cm_type)) = 0i) &&
     (cm_rep_expr_op (CMVarE (scope:int) (slot:int) (ty:cm_type)) = scope) &&
     (!dst src ty. cm_rep_expr_op
        (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) = 0i) &&
     (!op left right ty. cm_rep_expr_op
        (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = op) &&
     (!op arg ty. cm_rep_expr_op
        (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) = op) &&
     (!base index ty. cm_rep_expr_op
        (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) = 0i) &&
     (!base mid ty. cm_rep_expr_op
        (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) = 0i) &&
     (!fid args ty. cm_rep_expr_op
        (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) = 0i) &&
     (!asked ty. cm_rep_expr_op
        (CMSizeofE (asked:cm_type) (ty:cm_type)) = 0i) &&
     (!ty. cm_rep_expr_op (CMGetcE (ty:cm_type)) = 0i) &&
     (!arg ty. cm_rep_expr_op
        (CMPutcE (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (!arg ty. cm_rep_expr_op
        (CMPutiE (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (!arg ty. cm_rep_expr_op
        (CMExitE (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (cm_rep_expr_ops ([]:(cm_expr)list) = ([]:(int)list)) &&
     (!arg args. cm_rep_expr_ops
        ((arg:cm_expr)::(args:(cm_expr)list)) =
        cm_rep_expr_op arg :: cm_rep_expr_ops args)`);

PROOF thm cm_rep_expr_value_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(cm_rep_expr_value (CMConstE (n:int) (ty:cm_type)) = n) &&
     (cm_rep_expr_value (CMStringE (sid:int) (ty:cm_type)) = sid) &&
     (cm_rep_expr_value
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) = slot) &&
     (!dst src ty. cm_rep_expr_value
        (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) = 0i) &&
     (!op left right ty. cm_rep_expr_value
        (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = 0i) &&
     (!op arg ty. cm_rep_expr_value
        (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (!base index ty. cm_rep_expr_value
        (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) = 0i) &&
     (!base mid ty. cm_rep_expr_value
        (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) = mid) &&
     (!fid args ty. cm_rep_expr_value
        (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) = fid) &&
     (!asked ty. cm_rep_expr_value
        (CMSizeofE (asked:cm_type) (ty:cm_type)) =
        cm_type_encode asked) &&
     (!ty. cm_rep_expr_value (CMGetcE (ty:cm_type)) = 0i) &&
     (!arg ty. cm_rep_expr_value
        (CMPutcE (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (!arg ty. cm_rep_expr_value
        (CMPutiE (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (!arg ty. cm_rep_expr_value
        (CMExitE (arg:cm_expr) (ty:cm_type)) = 0i) &&
     (cm_rep_expr_values ([]:(cm_expr)list) = ([]:(int)list)) &&
     (!arg args. cm_rep_expr_values
        ((arg:cm_expr)::(args:(cm_expr)list)) =
        cm_rep_expr_value arg :: cm_rep_expr_values args)`);

PROOF thm cm_expr_node_def = new_fun_definition(
    `cm_expr_node (p:int) (e:cm_expr)
       (payload:int->int->int->hprop) : hprop =
       (exists za zb zargs.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_expr Fkind) Tint
            (cm_rep_expr_kind e) **
          data_at (field_addr p Tcm_expr Fop) Tint
            (cm_rep_expr_op e) **
          data_at (field_addr p Tcm_expr Fty) Tint
            (cm_type_encode (cm_expr_type e)) **
          data_at (field_addr p Tcm_expr Fvalue) Tint64
            (cm_rep_expr_value e) **
          data_at (field_addr p Tcm_expr Fa) Tptr za **
          data_at (field_addr p Tcm_expr Fb) Tptr zb **
          data_at (field_addr p Tcm_expr Fargs) Tptr zargs **
          payload za zb zargs)`);

PROOF thm cm_expr_payload_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!za zb zargs n ty. cm_expr_payload
        (CMConstE (n:int) (ty:cm_type)) za zb zargs =
        (fact(za == 0i && zb == 0i && zargs == 0i))) &&
     (!za zb zargs sid ty. cm_expr_payload
        (CMStringE (sid:int) (ty:cm_type)) za zb zargs =
        (fact(za == 0i && zb == 0i && zargs == 0i))) &&
     (!za zb zargs scope slot ty. cm_expr_payload
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) za zb zargs =
        (fact(za == 0i && zb == 0i && zargs == 0i))) &&
     (!za zb zargs dst src ty. cm_expr_payload
        (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type))
          za zb zargs =
        (fact(zargs == 0i) **
         cm_expr_node za dst (cm_expr_payload dst) **
         cm_expr_node zb src (cm_expr_payload src))) &&
     (!za zb zargs op left right ty. cm_expr_payload
        (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) za zb zargs =
        (fact(zargs == 0i) **
         cm_expr_node za left (cm_expr_payload left) **
         cm_expr_node zb right (cm_expr_payload right))) &&
     (!za zb zargs op arg ty. cm_expr_payload
        (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) za zb zargs =
        (fact(~(za == 0i) && zb == 0i && zargs == 0i) **
         cm_expr_node za arg (cm_expr_payload arg))) &&
     (!za zb zargs base index ty. cm_expr_payload
        (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type))
          za zb zargs =
        (fact(zargs == 0i) **
         cm_expr_node za base (cm_expr_payload base) **
         cm_expr_node zb index (cm_expr_payload index))) &&
     (!za zb zargs base mid ty. cm_expr_payload
        (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type))
          za zb zargs =
        (fact(~(za == 0i) && zb == 0i && zargs == 0i) **
         cm_expr_node za base (cm_expr_payload base))) &&
     (!za zb zargs fid args ty. cm_expr_payload
        (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type))
          za zb zargs =
        (fact(za == 0i && zb == 0i) ** cm_arg_tree args zargs)) &&
     (!za zb zargs asked ty. cm_expr_payload
        (CMSizeofE (asked:cm_type) (ty:cm_type)) za zb zargs =
        (fact(za == 0i && zb == 0i && zargs == 0i))) &&
     (!za zb zargs ty. cm_expr_payload
        (CMGetcE (ty:cm_type)) za zb zargs =
        (fact(za == 0i && zb == 0i && zargs == 0i))) &&
     (!za zb zargs arg ty. cm_expr_payload
        (CMPutcE (arg:cm_expr) (ty:cm_type)) za zb zargs =
        (fact(~(za == 0i) && zb == 0i && zargs == 0i) **
         cm_expr_node za arg (cm_expr_payload arg))) &&
     (!za zb zargs arg ty. cm_expr_payload
        (CMPutiE (arg:cm_expr) (ty:cm_type)) za zb zargs =
        (fact(~(za == 0i) && zb == 0i && zargs == 0i) **
         cm_expr_node za arg (cm_expr_payload arg))) &&
     (!za zb zargs arg ty. cm_expr_payload
        (CMExitE (arg:cm_expr) (ty:cm_type)) za zb zargs =
        (fact(~(za == 0i) && zb == 0i && zargs == 0i) **
         cm_expr_node za arg (cm_expr_payload arg))) &&
     (!p. cm_arg_tree ([]:(cm_expr)list) (p:int) = fact(p == 0i)) &&
     (!arg args p. cm_arg_tree
        ((arg:cm_expr)::(args:(cm_expr)list)) (p:int) =
        (exists ze zn.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_arg Fexpr) Tptr ze **
          data_at (field_addr p Tcm_arg Fnext) Tptr zn **
          cm_expr_node ze arg (cm_expr_payload arg) **
          cm_arg_tree args zn))`);

PROOF thm cm_expr_rep_def = new_fun_definition(
    `cm_expr_rep (p:int) (e:cm_expr) : hprop =
       cm_expr_node p e (cm_expr_payload e)`);
PROOF thm cm_arg_list_rep_def = new_fun_definition(
    `cm_arg_list_rep (p:int) (args:(cm_expr)list) : hprop =
       cm_arg_tree args p`);

PROOF thm cm_rep_stmt_kind_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(cm_rep_stmt_kind CMSkipS = 0i) &&
     (!e. cm_rep_stmt_kind (CMExprS (e:cm_expr)) = 1i) &&
     (!slot. cm_rep_stmt_kind (CMDeclS (slot:int)) = 2i) &&
     (!slot e. cm_rep_stmt_kind
        (CMInitS (slot:int) (e:cm_expr)) = 3i) &&
     (!a b. cm_rep_stmt_kind
        (CMSeqS (a:cm_stmt) (b:cm_stmt)) = 4i) &&
     (!a. cm_rep_stmt_kind (CMBlockS (a:cm_stmt)) = 5i) &&
     (!e a b. cm_rep_stmt_kind
        (CMIfS (e:cm_expr) (a:cm_stmt) (b:cm_stmt)) = 6i) &&
     (!e a. cm_rep_stmt_kind
        (CMWhileS (e:cm_expr) (a:cm_stmt)) = 7i) &&
     (cm_rep_stmt_kind CMBreakS = 8i) &&
     (cm_rep_stmt_kind CMContinueS = 9i) &&
     (!e. cm_rep_stmt_kind (CMReturnS (e:cm_expr)) = 10i)`);

PROOF thm cm_rep_stmt_slot_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(cm_rep_stmt_slot CMSkipS = 0i) &&
     (!e. cm_rep_stmt_slot (CMExprS (e:cm_expr)) = 0i) &&
     (!slot. cm_rep_stmt_slot (CMDeclS (slot:int)) = slot) &&
     (!slot e. cm_rep_stmt_slot
        (CMInitS (slot:int) (e:cm_expr)) = slot) &&
     (!a b. cm_rep_stmt_slot
        (CMSeqS (a:cm_stmt) (b:cm_stmt)) = 0i) &&
     (!a. cm_rep_stmt_slot (CMBlockS (a:cm_stmt)) = 0i) &&
     (!e a b. cm_rep_stmt_slot
        (CMIfS (e:cm_expr) (a:cm_stmt) (b:cm_stmt)) = 0i) &&
     (!e a. cm_rep_stmt_slot
        (CMWhileS (e:cm_expr) (a:cm_stmt)) = 0i) &&
     (cm_rep_stmt_slot CMBreakS = 0i) &&
     (cm_rep_stmt_slot CMContinueS = 0i) &&
     (!e. cm_rep_stmt_slot (CMReturnS (e:cm_expr)) = 0i)`);

PROOF thm cm_stmt_node_def = new_fun_definition(
    `cm_stmt_node (p:int) (s:cm_stmt)
       (payload:int->int->int->hprop) : hprop =
       (exists ze za zb.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_stmt Fkind) Tint
            (cm_rep_stmt_kind s) **
          data_at (field_addr p Tcm_stmt Fslot) Tint
            (cm_rep_stmt_slot s) **
          data_at (field_addr p Tcm_stmt Fexpr) Tptr ze **
          data_at (field_addr p Tcm_stmt Fa) Tptr za **
          data_at (field_addr p Tcm_stmt Fb) Tptr zb **
          payload ze za zb)`);

PROOF thm cm_stmt_payload_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!ze za zb. cm_stmt_payload CMSkipS ze za zb =
        fact(ze == 0i && za == 0i && zb == 0i)) &&
     (!ze za zb e. cm_stmt_payload (CMExprS (e:cm_expr)) ze za zb =
        (fact(~(ze == 0i) && za == 0i && zb == 0i) **
         cm_expr_rep ze e)) &&
     (!ze za zb slot. cm_stmt_payload
        (CMDeclS (slot:int)) ze za zb =
        fact(ze == 0i && za == 0i && zb == 0i)) &&
     (!ze za zb slot e. cm_stmt_payload
        (CMInitS (slot:int) (e:cm_expr)) ze za zb =
        (fact(~(ze == 0i) && za == 0i && zb == 0i) **
         cm_expr_rep ze e)) &&
     (!ze za zb a b. cm_stmt_payload
        (CMSeqS (a:cm_stmt) (b:cm_stmt)) ze za zb =
        (fact(ze == 0i) **
         cm_stmt_node za a (cm_stmt_payload a) **
         cm_stmt_node zb b (cm_stmt_payload b))) &&
     (!ze za zb a. cm_stmt_payload
        (CMBlockS (a:cm_stmt)) ze za zb =
        (fact(ze == 0i && ~(za == 0i) && zb == 0i) **
         cm_stmt_node za a (cm_stmt_payload a))) &&
     (!ze za zb e a b. cm_stmt_payload
        (CMIfS (e:cm_expr) (a:cm_stmt) (b:cm_stmt)) ze za zb =
        (cm_expr_rep ze e **
         cm_stmt_node za a (cm_stmt_payload a) **
         cm_stmt_node zb b (cm_stmt_payload b))) &&
     (!ze za zb e a. cm_stmt_payload
        (CMWhileS (e:cm_expr) (a:cm_stmt)) ze za zb =
        (fact(~(ze == 0i) && ~(za == 0i) && zb == 0i) **
         cm_expr_rep ze e **
         cm_stmt_node za a (cm_stmt_payload a))) &&
     (!ze za zb. cm_stmt_payload CMBreakS ze za zb =
        fact(ze == 0i && za == 0i && zb == 0i)) &&
     (!ze za zb. cm_stmt_payload CMContinueS ze za zb =
        fact(ze == 0i && za == 0i && zb == 0i)) &&
     (!ze za zb e. cm_stmt_payload (CMReturnS (e:cm_expr)) ze za zb =
        (fact(~(ze == 0i) && za == 0i && zb == 0i) **
         cm_expr_rep ze e))`);

PROOF thm cm_stmt_rep_def = new_fun_definition(
    `cm_stmt_rep (p:int) (s:cm_stmt) : hprop =
       cm_stmt_node p s (cm_stmt_payload s)`);

PROOF static thm prove_cm_stmt_shape(
    const term statement, const term kind_fact, size_t target,
    const term_list witnesses, const term shape_fact) {
  gnode root = gnode_new_with_ccl(statement);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`s:cm_stmt`, get_cm_stmt_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "Hs");
  for (size_t i = 0; i < 11; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hs");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hs", NULL);
    }
  }
  for (size_t i = 0; i < 11; ++i) {
    if (i == target) continue;
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    int index = labeled_term_list_index(assumptions, "Hs");
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(assumptions[index].tm), cm_rep_stmt_kind_def)),
        assume_rule(kind_fact));
    CONTR_TAC(cases[i], impossible);
  }
  gnode selected = cases[target];
  for (size_t i = 0; i < vector_size(witnesses); ++i) {
    selected = EXISTS_TAC(selected, witnesses[i]);
  }
  ACCEPT_TAC(selected, assume_rule(shape_fact));
  return gnode_prove(root);
}

PROOF thm cm_stmt_skip_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 0i ==> s == CMSkipS`,
    `cm_rep_stmt_kind (s:cm_stmt) == 0i`, 0,
    TERM_LIST(), `s == CMSkipS`);
PROOF thm cm_stmt_expr_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 1i ==>
     exists e. s == CMExprS (e:cm_expr)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 1i`, 1,
    TERM_LIST(`a:cm_expr`), `s == CMExprS (a:cm_expr)`);
PROOF thm cm_stmt_decl_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 2i ==>
     exists slot. s == CMDeclS (slot:int)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 2i`, 2,
    TERM_LIST(`a:int`), `s == CMDeclS (a:int)`);
PROOF thm cm_stmt_init_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 3i ==>
     exists slot e. s == CMInitS (slot:int) (e:cm_expr)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 3i`, 3,
    TERM_LIST(`a0:int`, `a1:cm_expr`),
    `s == CMInitS (a0:int) (a1:cm_expr)`);
PROOF thm cm_stmt_seq_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 4i ==>
     exists a b. s == CMSeqS (a:cm_stmt) (b:cm_stmt)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 4i`, 4,
    TERM_LIST(`a0:cm_stmt`, `a1:cm_stmt`),
    `s == CMSeqS (a0:cm_stmt) (a1:cm_stmt)`);
PROOF thm cm_stmt_block_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 5i ==>
     exists a. s == CMBlockS (a:cm_stmt)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 5i`, 5,
    TERM_LIST(`a:cm_stmt`), `s == CMBlockS (a:cm_stmt)`);
PROOF thm cm_stmt_if_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 6i ==>
     exists e a b.
       s == CMIfS (e:cm_expr) (a:cm_stmt) (b:cm_stmt)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 6i`, 6,
    TERM_LIST(`a0:cm_expr`, `a1:cm_stmt`, `a2:cm_stmt`),
    `s == CMIfS (a0:cm_expr) (a1:cm_stmt) (a2:cm_stmt)`);
PROOF thm cm_stmt_while_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 7i ==>
     exists e a. s == CMWhileS (e:cm_expr) (a:cm_stmt)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 7i`, 7,
    TERM_LIST(`a0:cm_expr`, `a1:cm_stmt`),
    `s == CMWhileS (a0:cm_expr) (a1:cm_stmt)`);
PROOF thm cm_stmt_break_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 8i ==> s == CMBreakS`,
    `cm_rep_stmt_kind (s:cm_stmt) == 8i`, 8,
    TERM_LIST(), `s == CMBreakS`);
PROOF thm cm_stmt_continue_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 9i ==> s == CMContinueS`,
    `cm_rep_stmt_kind (s:cm_stmt) == 9i`, 9,
    TERM_LIST(), `s == CMContinueS`);
PROOF thm cm_stmt_return_shape = prove_cm_stmt_shape(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 10i ==>
     exists e. s == CMReturnS (e:cm_expr)`,
    `cm_rep_stmt_kind (s:cm_stmt) == 10i`, 10,
    TERM_LIST(`a:cm_expr`), `s == CMReturnS (a:cm_expr)`);

PROOF static thm prove_cm_stmt_shape_ent(
    const term statement, const thm shape_theorem,
    const term kind_fact, const const_cstr_list names,
    const term_list witnesses, const term shape_fact) {
  gnode root = gnode_new_with_ccl(statement);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm shaped = mp_rule(spec_rule(`s:cm_stmt`, shape_theorem),
      assume_rule(kind_fact));
  gnode with_shape = ASSUME_TAC(introduced, shaped, "Hshape");
  for (size_t i = 0; i < vector_size(names); ++i) {
    with_shape = ASMP_EXISTS_TAC(with_shape, "Hshape", names[i]);
  }
  gnode_list initialized = AUTO_INIT_SLTAC(with_shape);
  gnode selected = initialized[0];
  for (size_t i = 0; i < vector_size(witnesses); ++i) {
    selected = EXISTS_SLTAC(selected, witnesses[i]);
  }
  gnode fact_goal = AUTO_INTRO_FACT_SLTAC(selected);
  gnode_list pure = PURE_SLTAC(fact_goal);
  ACCEPT_TAC(pure[0], assume_rule(shape_fact));
  AUTO_FRAME_SLTAC(pure[1]);
  return gnode_prove(root);
}

PROOF thm cm_stmt_skip_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 0i ==>
     (emp |-- fact(s == CMSkipS))`,
    cm_stmt_skip_shape, `cm_rep_stmt_kind (s:cm_stmt) == 0i`,
    CONST_STRING_LIST(), TERM_LIST(), `s == CMSkipS`);
PROOF thm cm_stmt_expr_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 1i ==>
     (emp |-- exists e. fact(s == CMExprS (e:cm_expr)))`,
    cm_stmt_expr_shape, `cm_rep_stmt_kind (s:cm_stmt) == 1i`,
    CONST_STRING_LIST("expr_"), TERM_LIST(`expr_:cm_expr`),
    `s == CMExprS (expr_:cm_expr)`);
PROOF thm cm_stmt_decl_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 2i ==>
     (emp |-- exists slot. fact(s == CMDeclS (slot:int)))`,
    cm_stmt_decl_shape, `cm_rep_stmt_kind (s:cm_stmt) == 2i`,
    CONST_STRING_LIST("slot_"), TERM_LIST(`slot_:int`),
    `s == CMDeclS (slot_:int)`);
PROOF thm cm_stmt_init_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 3i ==>
     (emp |-- exists slot e.
       fact(s == CMInitS (slot:int) (e:cm_expr)))`,
    cm_stmt_init_shape, `cm_rep_stmt_kind (s:cm_stmt) == 3i`,
    CONST_STRING_LIST("slot_", "expr_"),
    TERM_LIST(`slot_:int`, `expr_:cm_expr`),
    `s == CMInitS (slot_:int) (expr_:cm_expr)`);
PROOF thm cm_stmt_seq_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 4i ==>
     (emp |-- exists a b.
       fact(s == CMSeqS (a:cm_stmt) (b:cm_stmt)))`,
    cm_stmt_seq_shape, `cm_rep_stmt_kind (s:cm_stmt) == 4i`,
    CONST_STRING_LIST("first_", "second_"),
    TERM_LIST(`first_:cm_stmt`, `second_:cm_stmt`),
    `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
PROOF thm cm_stmt_block_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 5i ==>
     (emp |-- exists a. fact(s == CMBlockS (a:cm_stmt)))`,
    cm_stmt_block_shape, `cm_rep_stmt_kind (s:cm_stmt) == 5i`,
    CONST_STRING_LIST("body_"), TERM_LIST(`body_:cm_stmt`),
    `s == CMBlockS (body_:cm_stmt)`);
PROOF thm cm_stmt_if_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 6i ==>
     (emp |-- exists e a b.
       fact(s == CMIfS (e:cm_expr) (a:cm_stmt) (b:cm_stmt)))`,
    cm_stmt_if_shape, `cm_rep_stmt_kind (s:cm_stmt) == 6i`,
    CONST_STRING_LIST("guard_", "yes_", "no_"),
    TERM_LIST(`guard_:cm_expr`, `yes_:cm_stmt`, `no_:cm_stmt`),
    `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)`);
PROOF thm cm_stmt_while_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 7i ==>
     (emp |-- exists e a.
       fact(s == CMWhileS (e:cm_expr) (a:cm_stmt)))`,
    cm_stmt_while_shape, `cm_rep_stmt_kind (s:cm_stmt) == 7i`,
    CONST_STRING_LIST("guard_", "body_"),
    TERM_LIST(`guard_:cm_expr`, `body_:cm_stmt`),
    `s == CMWhileS (guard_:cm_expr) (body_:cm_stmt)`);
PROOF thm cm_stmt_break_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 8i ==>
     (emp |-- fact(s == CMBreakS))`,
    cm_stmt_break_shape, `cm_rep_stmt_kind (s:cm_stmt) == 8i`,
    CONST_STRING_LIST(), TERM_LIST(), `s == CMBreakS`);
PROOF thm cm_stmt_continue_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 9i ==>
     (emp |-- fact(s == CMContinueS))`,
    cm_stmt_continue_shape, `cm_rep_stmt_kind (s:cm_stmt) == 9i`,
    CONST_STRING_LIST(), TERM_LIST(), `s == CMContinueS`);
PROOF thm cm_stmt_return_shape_ent = prove_cm_stmt_shape_ent(
    `!s. cm_rep_stmt_kind (s:cm_stmt) == 10i ==>
     (emp |-- exists e. fact(s == CMReturnS (e:cm_expr)))`,
    cm_stmt_return_shape, `cm_rep_stmt_kind (s:cm_stmt) == 10i`,
    CONST_STRING_LIST("expr_"), TERM_LIST(`expr_:cm_expr`),
    `s == CMReturnS (expr_:cm_expr)`);

PROOF thm mk_cm_rep_stmt_kind_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!s. 0i <= cm_rep_stmt_kind (s:cm_stmt) &&
           cm_rep_stmt_kind s <= 10i`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`s:cm_stmt`, get_cm_stmt_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "Hs");
  for (size_t i = 0; i < 11; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hs");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hs", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv,
        THM_LIST(cm_rep_stmt_kind_def));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_stmt_kind_bounds = mk_cm_rep_stmt_kind_bounds();
PROOF thm mk_cm_rep_stmt_kind_exhaustive(void) {
  thm bounds = spec_rule(`s:cm_stmt`, cm_rep_stmt_kind_bounds);
  thm impossible = mp_rule(int_arith_rule(
      `(0i <= cm_rep_stmt_kind (s:cm_stmt) &&
        cm_rep_stmt_kind s <= 10i) ==>
       ~(cm_rep_stmt_kind s == 0i) ==>
       ~(cm_rep_stmt_kind s == 1i) ==>
       ~(cm_rep_stmt_kind s == 2i) ==>
       ~(cm_rep_stmt_kind s == 3i) ==>
       ~(cm_rep_stmt_kind s == 4i) ==>
       ~(cm_rep_stmt_kind s == 5i) ==>
       ~(cm_rep_stmt_kind s == 6i) ==>
       ~(cm_rep_stmt_kind s == 7i) ==>
       ~(cm_rep_stmt_kind s == 8i) ==>
       ~(cm_rep_stmt_kind s == 9i) ==>
       ~(cm_rep_stmt_kind s == 10i) ==> F`), bounds);
  return gen_rule(`s:cm_stmt`, impossible);
}
PROOF thm cm_rep_stmt_kind_exhaustive =
    mk_cm_rep_stmt_kind_exhaustive();

PROOF thm cm_slot_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p. cm_slot_list_rep (p:int) ([]:(cm_slot_d)list) = fact(p == 0i)) &&
     (!p slot rest. cm_slot_list_rep (p:int)
        ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) =
        (exists zn.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_slot Fty) Tint
            (cm_type_encode (cm_slot_ty slot)) **
          data_at (field_addr p Tcm_slot Fcount) Tint
            (cm_slot_count slot) **
          data_at (field_addr p Tcm_slot Fnext) Tptr zn **
          cm_slot_list_rep zn rest))`);

PROOF thm cm_member_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p. cm_member_list_rep (p:int) ([]:(cm_slot_d)list) = fact(p == 0i)) &&
     (!p slot rest. cm_member_list_rep (p:int)
        ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) =
        (exists zn.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_member Fty) Tint
            (cm_type_encode (cm_slot_ty slot)) **
          data_at (field_addr p Tcm_member Fcount) Tint
            (cm_slot_count slot) **
          data_at (field_addr p Tcm_member Fnext) Tptr zn **
          cm_member_list_rep zn rest))`);

PROOF thm cm_struct_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p. cm_struct_list_rep (p:int) ([]:(cm_struct_d)list) = fact(p == 0i)) &&
     (!p strct rest. cm_struct_list_rep (p:int)
        ((strct:cm_struct_d) :: (rest:(cm_struct_d)list)) =
        (exists zm zn.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_struct Fmembers) Tptr zm **
          data_at (field_addr p Tcm_struct Fnext) Tptr zn **
          cm_member_list_rep zm (cm_struct_members strct) **
          cm_struct_list_rep zn rest))`);

PROOF thm cm_rep_bool_def = new_fun_definition(
    `cm_rep_bool (b:bool) : int = (if b then 1i else 0i)`);

PROOF thm cm_global_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p. cm_global_list_rep (p:int) ([]:(cm_global_d)list) = fact(p == 0i)) &&
     (!p g rest. cm_global_list_rep (p:int)
        ((g:cm_global_d) :: (rest:(cm_global_d)list)) =
        (exists zn.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_global Fty) Tint
            (cm_type_encode (cm_global_ty g)) **
          data_at (field_addr p Tcm_global Fcount) Tint
            (cm_global_count g) **
          data_at (field_addr p Tcm_global Fhas_init) Tint
            (cm_rep_bool (cm_global_has_init g)) **
          data_at (field_addr p Tcm_global Finit) Tint64
            (cm_global_init g) **
          data_at (field_addr p Tcm_global Fnext) Tptr zn **
          cm_global_list_rep zn rest))`);

PROOF thm cm_uint8_buffer_def = new_fun_definition(
    `cm_uint8_buffer (p:int) (bytes:(int)list) : hprop =
       (if bytes == [] then emp
        else fact(~(p == 0i)) **
             store_uint8_array p (ilength bytes) bytes)`);

PROOF thm cm_rep_string_length_def = new_fun_definition(
    `cm_rep_string_length (string:cm_string_d) : int =
       ilength (cm_string_bytes string)`);
PROOF thm cm_rep_string_size_def = new_fun_definition(
    `cm_rep_string_size (string:cm_string_d) : int =
       cm_rep_string_length string + 1i`);
PROOF thm cm_rep_strings_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_strings_size ([]:(cm_string_d)list) = 0i) &&
     (!string rest.
        cm_rep_strings_size
          ((string:cm_string_d) :: (rest:(cm_string_d)list)) =
        cm_rep_string_size string + cm_rep_strings_size rest)`);
PROOF thm cm_rep_strings_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_strings_prefix ([]:(cm_string_d)list)
        (index:int) = 0i) &&
     (!string rest index.
        cm_rep_strings_prefix
          ((string:cm_string_d) :: (rest:(cm_string_d)list))
          (index:int) =
        (if index == 0i then 0i
         else cm_rep_string_size string +
              cm_rep_strings_prefix rest (index - 1i)))`);
PROOF thm cm_string_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p. cm_string_list_rep (p:int) ([]:(cm_string_d)list) = fact(p == 0i)) &&
     (!p s rest. cm_string_list_rep (p:int)
        ((s:cm_string_d) :: (rest:(cm_string_d)list)) =
        (exists zb zn.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_string Fbytes) Tptr zb **
          data_at (field_addr p Tcm_string Flength) Tint
            (cm_rep_string_length s) **
          data_at (field_addr p Tcm_string Fnext) Tptr zn **
          cm_uint8_buffer zb (cm_string_bytes s) **
          cm_string_list_rep zn rest))`);

PROOF thm cm_function_header_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p bodies. cm_function_header_list_rep (p:int)
        ([]:(cm_function_d)list) (bodies:(int)list) =
        fact(p == 0i && bodies == [])) &&
     (!p fn rest bodies. cm_function_header_list_rep (p:int)
        ((fn:cm_function_d) :: (rest:(cm_function_d)list))
        (bodies:(int)list) =
        (exists zp zl zb zn body_rest.
          fact(~(p == 0i) && bodies == zb :: body_rest) **
          data_at (field_addr p Tcm_function Fret_ty) Tint
            (cm_type_encode (cm_function_ret fn)) **
          data_at (field_addr p Tcm_function Fparams) Tptr zp **
          data_at (field_addr p Tcm_function Flocals) Tptr zl **
          data_at (field_addr p Tcm_function Fbody) Tptr zb **
          data_at (field_addr p Tcm_function Fnext) Tptr zn **
          cm_slot_list_rep zp (cm_function_params fn) **
          cm_slot_list_rep zl (cm_function_locals fn) **
          cm_function_header_list_rep zn rest body_rest))`);

PROOF thm cm_function_body_list_rep_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!bodies. cm_function_body_list_rep (bodies:(int)list)
        ([]:(cm_function_d)list) = fact(bodies == [])) &&
     (!fn rest bodies. cm_function_body_list_rep (bodies:(int)list)
        ((fn:cm_function_d) :: (rest:(cm_function_d)list)) =
        (exists zb body_rest.
          fact(bodies == zb :: body_rest) **
          cm_stmt_rep zb (cm_function_body fn) **
          cm_function_body_list_rep body_rest rest))`);

PROOF thm cm_function_list_rep_def = new_fun_definition(
    `cm_function_list_rep (p:int)
       (functions:(cm_function_d)list) : hprop =
       (exists bodies.
          cm_function_header_list_rep p functions bodies **
          cm_function_body_list_rep bodies functions)`);


PROOF thm cm_rep_slot_type_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_slot_type ([]:(cm_slot_d)list) (index:int) = 0i) &&
     (!slot rest index.
        cm_rep_slot_type
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list))
          (index:int) =
        (if index == 0i
         then cm_type_encode (cm_slot_ty slot)
         else cm_rep_slot_type rest (index - 1i)))`);
PROOF thm cm_rep_is_pointer_code_def = new_fun_definition(
    `cm_rep_is_pointer_code (code:int) : int =
       (if 1024i <= code then 1i else 0i)`);
PROOF thm cm_rep_leaf_size_def = new_fun_definition(
    `cm_rep_leaf_size (code:int) : int =
       (if 1024i <= code then 8i
        else if code == 0i then 8i
        else if code == 1i then 1i
        else 0i)`);
PROOF thm cm_rep_code_slot_size_def = new_fun_definition(
    `cm_rep_code_slot_size (code:int) (count:int) : int =
       (if count == 0i
        then cm_rep_leaf_size code
        else count * cm_rep_leaf_size code)`);
PROOF thm cm_rep_member_size_def = new_fun_definition(
    `cm_rep_member_size (member:cm_slot_d) : int =
       cm_rep_code_slot_size
         (cm_type_encode (cm_slot_ty member)) (cm_slot_count member)`);
PROOF thm cm_rep_members_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_members_size ([]:(cm_slot_d)list) = 0i) &&
     (!member rest.
        cm_rep_members_size
          ((member:cm_slot_d) :: (rest:(cm_slot_d)list)) =
        cm_rep_member_size member + cm_rep_members_size rest)`);
PROOF thm cm_rep_members_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_members_safe ([]:(cm_slot_d)list) = T) &&
     (!member rest.
        (cm_rep_members_safe
          ((member:cm_slot_d) :: (rest:(cm_slot_d)list)) <=>
         0i <= cm_rep_member_size member &&
         0i <= cm_rep_members_size rest &&
         cm_rep_members_size (member :: rest) <= 1048576i &&
         cm_rep_members_safe rest))`);
PROOF thm cm_rep_member_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_member_prefix ([]:(cm_slot_d)list) (index:int) = 0i) &&
     (!member rest index.
        cm_rep_member_prefix
          ((member:cm_slot_d) :: (rest:(cm_slot_d)list)) (index:int) =
        (if index == 0i then 0i
         else cm_rep_member_size member +
              cm_rep_member_prefix rest (index - 1i)))`);
PROOF thm cm_rep_member_array_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_member_array ([]:(cm_slot_d)list) (index:int) = 0i) &&
     (!member rest index.
        cm_rep_member_array
          ((member:cm_slot_d) :: (rest:(cm_slot_d)list)) (index:int) =
        (if index == 0i
         then (if cm_slot_count member == 0i then 0i else 1i)
         else cm_rep_member_array rest (index - 1i)))`);
PROOF thm cm_rep_nonzero_def = new_fun_definition(
    `cm_rep_nonzero (n:int) : int =
       (if n == 0i then 0i else 1i)`);
PROOF thm cm_rep_global_array_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_global_array ([]:(cm_global_d)list) (index:int) = 0i) &&
     (!global rest index.
        cm_rep_global_array
          ((global:cm_global_d) :: (rest:(cm_global_d)list))
          (index:int) =
        (if index == 0i
         then (if cm_global_count global == 0i then 0i else 1i)
         else cm_rep_global_array rest (index - 1i)))`);

PROOF static thm cm_prove_rep_num_of_int_add_one(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int). 0i <= x ==>
         num_of_int (1i + x) == SUC (num_of_int x)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm hx = assume_rule(`0i <= (x:int)`);
  thm h1 = int_arith_rule(`0i <= 1i`);
  thm add = mp_rule(specl_rule(TERM_LIST(`1i`, `x:int`),
      get_theorem_by_name("NUM_OF_INT_ADD")), conj_rule(h1, hx));
  thm reduced_add = pure_rewrite_rule(THM_LIST(
      get_theorem_by_name("NUM_OF_INT_OF_NUM")), add);
  thm commute = specl_rule(TERM_LIST(
      `1`, `num_of_int (x:int)`), get_theorem_by_name("ADD_SYM"));
  thm successor = sym_rule(spec_rule(
      `num_of_int (x:int)`, get_theorem_by_name("ADD1")));
  ACCEPT_TAC(leaf, trans_rule(
      reduced_add, trans_rule(commute, successor)));
  return gnode_prove(root);
}
PROOF thm cm_rep_num_of_int_add_one =
    cm_prove_rep_num_of_int_add_one();

PROOF static thm cm_prove_rep_inth_append_right(void) {
  gnode root = gnode_new_with_ccl(
      `!(prefix:(A)list). !(suffix:(A)list) (i:int).
         0i <= i ==>
         inth (ilength prefix + i) (prefix ++ suffix) ==
         inth i suffix`);
  gnode_list cases = INDUCT_TAC(root, `prefix:(A)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND"))));
    if (IS_NULL(reduced->solved)) {
      thm zero_index = int_arith_rule(`0i + (i:int) == i`);
      ACCEPT_TAC(reduced, beta_norm(ap_term_rule(
          `\index:int. inth index (suffix:(A)list)`, zero_index)));
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm hi = assume_rule(`0i <= (i:int)`);
    thm ih = assume_rule(
        `!(suffix:(A)list) (i:int).
           0i <= i ==>
           inth (ilength (a1:(A)list) + i)
             (a1 ++ suffix) == inth i suffix`);
    thm ih_at = mp_rule(specl_rule(
        TERM_LIST(`suffix:(A)list`, `i:int`), ih), hi);
    thm hlen = spec_rule(`a1:(A)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm hsum = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(hlen), concl(hi)),
        `0i <= ilength (a1:(A)list) + (i:int)`)),
        conj_rule(hlen, hi));
    thm succ = mp_rule(spec_rule(
        `ilength (a1:(A)list) + (i:int)`,
        cm_rep_num_of_int_add_one), hsum);
    thm reassoc = int_arith_rule(
        `(1i + ilength (a1:(A)list)) + (i:int) ==
         1i + (ilength a1 + i)`);
    thm num_reassoc = ap_term_rule(`num_of_int:int->num`, reassoc);
    thm num_succ = trans_rule(num_reassoc, succ);
    thm ih_nth = pure_rewrite_rule(
        THM_LIST(get_theorem_by_name("INTH_DEF")), ih_at);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("INTH_DEF"),
        num_succ, get_theorem_by_name("NTH_DEF"))));
    ACCEPT_TAC(reduced, ih_nth);
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_inth_append_right =
    cm_prove_rep_inth_append_right();

PROOF static thm cm_prove_rep_inth_cons_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(head:A) (tail:(A)list) i.
         1i <= i ==>
         inth i (head :: tail) == inth (i - 1i) tail`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`1i <= (i:int)`);
  thm shifted_lower = mp_rule(int_arith_rule(mk_imp(
      concl(lower), `0i <= (i:int) - 1i`)), lower);
  thm split = mp_rule(ispecl_rule(TERM_LIST(
      `[(head:A)]`, `tail:(A)list`, `(i:int) - 1i`),
      cm_rep_inth_append_right), shifted_lower);
  thm split_reduced = pure_rewrite_rule(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("APPEND")), split);
  thm index_equal = mp_rule(int_arith_rule(mk_imp(
      concl(lower),
      `(1i + 0i) + ((i:int) - 1i) == i`)), lower);
  thm lifted = beta_norm(ap_term_rule(
      `\index:int. inth index
         ((head:A) :: (tail:(A)list))`, index_equal));
  ACCEPT_TAC(leaf, trans_rule(sym_rule(lifted), split_reduced));
  return gnode_prove(root);
}
PROOF thm cm_rep_inth_cons_tail =
    cm_prove_rep_inth_cons_tail();

PROOF static thm cm_prove_rep_member_array_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list) index.
         0i <= index ==>
         index < ilength slots ==>
         cm_rep_member_array slots index ==
           cm_rep_nonzero (cm_slot_count (inth index slots))`);
  gnode_list cases = INDUCT_TAC(root, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(index:int) < ilength ([]:(cm_slot_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "Hindex");
    CONV_WITH_ASMP_TAC(index_cases[0], reduce_rewrite_conv, THM_LIST(
        cm_rep_member_array_def, cm_rep_nonzero_def,
        get_theorem_by_name("INTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        get_theorem_by_name("NTH_DEF")));
    thm nonnegative = assume_rule(`0i <= (index:int)`);
    thm nonzero = assume_rule(`~((index:int) == 0i)`);
    thm lower = mp_rule(int_arith_rule(
        `0i <= (index:int) ==> ~(index == 0i) ==> 1i <= index`),
        nonnegative);
    lower = mp_rule(lower, nonzero);
    thm length_step = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(index:int) <
             ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm tail_bound = mp_rule(int_arith_rule(
        `(index:int) < 1i + ilength (a1:(cm_slot_d)list) ==>
         index - 1i < ilength a1`), length_step);
    thm tail_nonnegative = mp_rule(int_arith_rule(
        `1i <= (index:int) ==> 0i <= index - 1i`), lower);
    thm ih = mp_rule(mp_rule(spec_rule(
        `(index:int) - 1i`, assume_rule(
          `!index.
             0i <= index ==>
             index < ilength (a1:(cm_slot_d)list) ==>
             cm_rep_member_array a1 index ==
               cm_rep_nonzero (cm_slot_count (inth index a1))`)),
        tail_nonnegative), tail_bound);
    thm lookup = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `index:int`),
        cm_rep_inth_cons_tail), lower);
    gnode reduced = CONV_WITH_ASMP_TAC(
        index_cases[1], reduce_rewrite_conv, THM_LIST(
          cm_rep_member_array_def, lookup));
    ACCEPT_TAC(reduced, ih);
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_member_array_at =
    cm_prove_rep_member_array_at();

PROOF static thm cm_prove_rep_global_array_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(globals:(cm_global_d)list) index.
         0i <= index ==>
         index < ilength globals ==>
         cm_rep_global_array globals index ==
           cm_rep_nonzero (cm_global_count (inth index globals))`);
  gnode_list cases = INDUCT_TAC(root, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(index:int) < ilength ([]:(cm_global_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "Hindex");
    CONV_WITH_ASMP_TAC(index_cases[0], reduce_rewrite_conv, THM_LIST(
        cm_rep_global_array_def, cm_rep_nonzero_def,
        get_theorem_by_name("INTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        get_theorem_by_name("NTH_DEF")));
    thm nonnegative = assume_rule(`0i <= (index:int)`);
    thm nonzero = assume_rule(`~((index:int) == 0i)`);
    thm lower = mp_rule(int_arith_rule(
        `0i <= (index:int) ==> ~(index == 0i) ==> 1i <= index`),
        nonnegative);
    lower = mp_rule(lower, nonzero);
    thm length_step = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(index:int) <
             ilength ((a0:cm_global_d) :: (a1:(cm_global_d)list))`));
    thm tail_bound = mp_rule(int_arith_rule(
        `(index:int) < 1i + ilength (a1:(cm_global_d)list) ==>
         index - 1i < ilength a1`), length_step);
    thm tail_nonnegative = mp_rule(int_arith_rule(
        `1i <= (index:int) ==> 0i <= index - 1i`), lower);
    thm ih = mp_rule(mp_rule(spec_rule(
        `(index:int) - 1i`, assume_rule(
          `!index.
             0i <= index ==>
             index < ilength (a1:(cm_global_d)list) ==>
             cm_rep_global_array a1 index ==
               cm_rep_nonzero (cm_global_count (inth index a1))`)),
        tail_nonnegative), tail_bound);
    thm lookup = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_global_d`, `a1:(cm_global_d)list`, `index:int`),
        cm_rep_inth_cons_tail), lower);
    gnode reduced = CONV_WITH_ASMP_TAC(
        index_cases[1], reduce_rewrite_conv, THM_LIST(
          cm_rep_global_array_def, lookup));
    ACCEPT_TAC(reduced, ih);
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_global_array_at =
    cm_prove_rep_global_array_at();
PROOF thm cm_rep_global_size_def = new_fun_definition(
    `cm_rep_global_size (global:cm_global_d) : int =
       cm_rep_code_slot_size
         (cm_type_encode (cm_global_ty global))
         (cm_global_count global)`);
PROOF thm cm_rep_globals_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_globals_size ([]:(cm_global_d)list) = 0i) &&
     (!global rest.
        cm_rep_globals_size
          ((global:cm_global_d) :: (rest:(cm_global_d)list)) =
        cm_rep_global_size global + cm_rep_globals_size rest)`);
PROOF thm cm_rep_globals_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_globals_safe ([]:(cm_global_d)list) = T) &&
     (!global rest.
        (cm_rep_globals_safe
          ((global:cm_global_d) :: (rest:(cm_global_d)list)) <=>
         0i <= cm_rep_global_size global &&
         0i <= cm_rep_globals_size rest &&
         cm_rep_globals_size (global :: rest) <= 1048560i &&
         cm_rep_globals_safe rest))`);
PROOF thm cm_rep_globals_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_globals_prefix ([]:(cm_global_d)list)
        (index:int) = 0i) &&
     (!global rest index.
        cm_rep_globals_prefix
          ((global:cm_global_d) :: (rest:(cm_global_d)list))
          (index:int) =
        (if index == 0i then 0i
         else cm_rep_global_size global +
              cm_rep_globals_prefix rest (index - 1i)))`);
PROOF thm cm_rep_global_address_def = new_fun_definition(
    `cm_rep_global_address (globals:(cm_global_d)list)
       (index:int) : int =
       16i + cm_rep_globals_prefix globals index`);
PROOF thm cm_rep_string_address_def = new_fun_definition(
    `cm_rep_string_address (globals:(cm_global_d)list)
       (strings:(cm_string_d)list) (index:int) : int =
       16i + cm_rep_globals_size globals +
       cm_rep_strings_prefix strings index`);
PROOF thm cm_rep_args_length_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_args_length ([]:(cm_expr)list) = 0i) &&
     (!arg rest.
        cm_rep_args_length
          ((arg:cm_expr) :: (rest:(cm_expr)list)) =
        1i + cm_rep_args_length rest)`);
PROOF thm cm_rep_args_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_args_safe ([]:(cm_expr)list) = T) &&
     (!arg rest.
        (cm_rep_args_safe
          ((arg:cm_expr) :: (rest:(cm_expr)list)) <=>
         0i <= cm_rep_args_length rest &&
         cm_rep_args_length rest < 2147483647i &&
         cm_rep_args_safe rest))`);
PROOF thm cm_rep_tpair_safe_def = new_fun_definition(
    `cm_rep_tpair_safe (pair:cm_tpair) : bool =
       (0i <= cm_tleft pair &&
        cm_tleft pair <= 2147483647i &&
        0i <= cm_tright pair &&
        cm_tright pair <= 2147483647i)`);
PROOF thm cm_rep_apair_safe_def = new_fun_definition(
    `cm_rep_apair_safe (pair:cm_apair) : bool =
       (0i <= cm_acount pair &&
        cm_acount pair <= 2147483647i &&
        0i <= cm_adepth pair &&
        cm_adepth pair <= 2147483647i &&
        cm_acount pair + cm_adepth pair <= 2147483647i)`);
PROOF thm cm_rep_expr_temps_safe_def =
  new_rec_definition(get_cm_expr_recursion(),
    `(cm_rep_expr_temps_safe
        (CMConstE (n:int) (ty:cm_type)) <=>
        cm_rep_tpair_safe (cm_expr_tpair (CMConstE n ty))) &&
     (cm_rep_expr_temps_safe
        (CMStringE (sid:int) (ty:cm_type)) <=>
        cm_rep_tpair_safe (cm_expr_tpair (CMStringE sid ty))) &&
     (cm_rep_expr_temps_safe
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) <=>
        cm_rep_tpair_safe (cm_expr_tpair (CMVarE scope slot ty))) &&
     (!dst src ty.
        (cm_rep_expr_temps_safe
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMAssignE dst src ty)) &&
         cm_tright (cm_expr_tpair src) < 2147483647i &&
         cm_rep_expr_temps_safe dst &&
         cm_rep_expr_temps_safe src)) &&
     (!op left right ty.
        (cm_rep_expr_temps_safe
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) <=>
         cm_rep_tpair_safe
           (cm_expr_tpair (CMBinaryE op left right ty)) &&
         cm_tright (cm_expr_tpair right) < 2147483647i &&
         cm_rep_expr_temps_safe left &&
         cm_rep_expr_temps_safe right)) &&
     (!op arg ty.
        (cm_rep_expr_temps_safe
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMUnaryE op arg ty)) &&
         cm_rep_expr_temps_safe arg)) &&
     (!base index ty.
        (cm_rep_expr_temps_safe
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMIndexE base index ty)) &&
         cm_tright (cm_expr_tpair index) < 2147483647i &&
         cm_rep_expr_temps_safe base &&
         cm_rep_expr_temps_safe index)) &&
     (!base mid ty.
        (cm_rep_expr_temps_safe
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMMemberE base mid ty)) &&
         cm_rep_expr_temps_safe base)) &&
     (!fid args ty.
        (cm_rep_expr_temps_safe
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMCallE fid args ty)) &&
         cm_rep_args_temps_safe args)) &&
     (!asked ty.
        (cm_rep_expr_temps_safe
          (CMSizeofE (asked:cm_type) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMSizeofE asked ty)))) &&
     (!ty.
        (cm_rep_expr_temps_safe (CMGetcE (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMGetcE ty)))) &&
     (!arg ty.
        (cm_rep_expr_temps_safe
          (CMPutcE (arg:cm_expr) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMPutcE arg ty)) &&
         cm_rep_expr_temps_safe arg)) &&
     (!arg ty.
        (cm_rep_expr_temps_safe
          (CMPutiE (arg:cm_expr) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMPutiE arg ty)) &&
         cm_rep_expr_temps_safe arg)) &&
     (!arg ty.
        (cm_rep_expr_temps_safe
          (CMExitE (arg:cm_expr) (ty:cm_type)) <=>
         cm_rep_tpair_safe (cm_expr_tpair (CMExitE arg ty)) &&
         cm_rep_expr_temps_safe arg)) &&
     (cm_rep_args_temps_safe ([]:(cm_expr)list) <=>
        cm_rep_apair_safe (cm_args_apair [])) &&
     (!arg args.
        (cm_rep_args_temps_safe
          ((arg:cm_expr) :: (args:(cm_expr)list)) <=>
         cm_rep_apair_safe (cm_args_apair (arg :: args)) &&
         cm_acount (cm_args_apair args) < 2147483647i &&
         cm_rep_expr_temps_safe arg &&
         cm_rep_args_temps_safe args))`);

PROOF thm mk_cm_rep_expr_temps_safe_pair(void) {
  gnode root = gnode_new_with_ccl(
      `!e. cm_rep_expr_temps_safe (e:cm_expr) ==>
       cm_rep_tpair_safe (cm_expr_tpair e)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`e:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "He");
  for (size_t i = 0; i < 14; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "He");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "He", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    int index = labeled_term_list_index(assumptions, "He");
    thm shape = assume_rule(assumptions[index].tm);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        shape, cm_rep_expr_temps_safe_def)),
        assume_rule(`cm_rep_expr_temps_safe (e:cm_expr)`));
    thm pair = (i == 0 || i == 1 || i == 2 ||
                i == 9 || i == 10)
        ? opened : conjunct1_rule(opened);
    thm generic = conv_rule(rewrite_conv(THM_LIST(sym_rule(shape))), pair);
    ACCEPT_TAC(cases[i], generic);
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_expr_temps_safe_pair =
    mk_cm_rep_expr_temps_safe_pair();

PROOF thm cm_rep_stmt_children_safe_def =
  new_rec_definition(get_cm_stmt_recursion(),
    `(cm_rep_stmt_children_safe CMSkipS <=> T) &&
     (!expr.
        (cm_rep_stmt_children_safe (CMExprS (expr:cm_expr)) <=>
         cm_rep_expr_temps_safe expr)) &&
     (!slot.
        (cm_rep_stmt_children_safe (CMDeclS (slot:int)) <=> T)) &&
     (!slot expr.
        (cm_rep_stmt_children_safe
          (CMInitS (slot:int) (expr:cm_expr)) <=>
         cm_rep_expr_temps_safe expr)) &&
     (!first second.
        (cm_rep_stmt_children_safe
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) <=>
         0i <= cm_stemps first &&
         cm_stemps first <= 2147483647i &&
         cm_rep_stmt_children_safe first &&
         0i <= cm_stemps second &&
         cm_stemps second <= 2147483647i &&
         cm_rep_stmt_children_safe second)) &&
     (!body.
        (cm_rep_stmt_children_safe (CMBlockS (body:cm_stmt)) <=>
         0i <= cm_stemps body &&
         cm_stemps body <= 2147483647i &&
         cm_rep_stmt_children_safe body)) &&
     (!guard yes no.
        (cm_rep_stmt_children_safe
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) <=>
         cm_rep_expr_temps_safe guard &&
         0i <= cm_stemps yes &&
         cm_stemps yes <= 2147483647i &&
         cm_rep_stmt_children_safe yes &&
         0i <= cm_stemps no &&
         cm_stemps no <= 2147483647i &&
         cm_rep_stmt_children_safe no)) &&
     (!guard body.
        (cm_rep_stmt_children_safe
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) <=>
         cm_rep_expr_temps_safe guard &&
         0i <= cm_stemps body &&
         cm_stemps body <= 2147483647i &&
         cm_rep_stmt_children_safe body)) &&
     (cm_rep_stmt_children_safe CMBreakS <=> T) &&
     (cm_rep_stmt_children_safe CMContinueS <=> T) &&
     (!expr.
        (cm_rep_stmt_children_safe (CMReturnS (expr:cm_expr)) <=>
         cm_rep_expr_temps_safe expr))`);
PROOF thm cm_rep_stmt_temps_safe_def = new_fun_definition(
    `cm_rep_stmt_temps_safe (s:cm_stmt) : bool =
       (0i <= cm_stemps s &&
        cm_stemps s <= 2147483647i &&
        cm_rep_stmt_children_safe s)`);

PROOF thm mk_cm_rep_stmt_temps_safe_bounds(void) {
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_rep_stmt_temps_safe_def)),
      assume_rule(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
  thm bounds = conj_rule(conjunct1_rule(opened),
      conjunct1_rule(conjunct2_rule(opened)));
  return gen_rule(`s:cm_stmt`,
      disch_rule(`cm_rep_stmt_temps_safe (s:cm_stmt)`, bounds));
}
PROOF thm cm_rep_stmt_temps_safe_bounds =
    mk_cm_rep_stmt_temps_safe_bounds();
PROOF thm open_cm_stmt_children_safe(term parent) {
  thm safe = assume_rule(mk_comb(
      `cm_rep_stmt_temps_safe`, parent));
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_rep_stmt_temps_safe_def)), safe);
  return conv_rule(rewrite_conv(THM_LIST(
      cm_rep_stmt_children_safe_def)),
      conjunct2_rule(conjunct2_rule(opened)));
}

PROOF thm fold_cm_stmt_temps_safe(
    term child, thm lower, thm upper, thm children) {
  thm parts = conj_rule(lower, conj_rule(upper, children));
  thm def = inst_rule(TERM_PAIR_LIST(
      (term_pair){child, `s:cm_stmt`}),
      cm_rep_stmt_temps_safe_def);
  return eq_mp_rule(sym_rule(def), parts);
}

PROOF thm prove_cm_rep_stmt_expr_child_safe(void) {
  term parent = `CMExprS (expr:cm_expr)`;
  thm child = open_cm_stmt_children_safe(parent);
  return gen_rule(`expr:cm_expr`,
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), child));
}
PROOF thm cm_rep_stmt_expr_child_safe =
    prove_cm_rep_stmt_expr_child_safe();

PROOF thm prove_cm_rep_stmt_init_child_safe(void) {
  term parent = `CMInitS (slot:int) (expr:cm_expr)`;
  thm child = open_cm_stmt_children_safe(parent);
  return genl_rule(TERM_LIST(`slot:int`, `expr:cm_expr`),
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), child));
}
PROOF thm cm_rep_stmt_init_child_safe =
    prove_cm_rep_stmt_init_child_safe();

PROOF thm prove_cm_rep_stmt_seq_children_safe(void) {
  term first = `first:cm_stmt`;
  term second = `second:cm_stmt`;
  term parent = `CMSeqS (first:cm_stmt) (second:cm_stmt)`;
  thm details = open_cm_stmt_children_safe(parent);
  thm rest1 = conjunct2_rule(details);
  thm rest2 = conjunct2_rule(rest1);
  thm rest3 = conjunct2_rule(rest2);
  thm rest4 = conjunct2_rule(rest3);
  thm first_safe = fold_cm_stmt_temps_safe(
      first, conjunct1_rule(details), conjunct1_rule(rest1),
      conjunct1_rule(rest2));
  thm second_safe = fold_cm_stmt_temps_safe(
      second, conjunct1_rule(rest3), conjunct1_rule(rest4),
      conjunct2_rule(rest4));
  thm result = conj_rule(first_safe, second_safe);
  return genl_rule(TERM_LIST(first, second),
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), result));
}
PROOF thm cm_rep_stmt_seq_children_safe =
    prove_cm_rep_stmt_seq_children_safe();

PROOF thm prove_cm_rep_stmt_block_child_safe(void) {
  term body = `body:cm_stmt`;
  term parent = `CMBlockS (body:cm_stmt)`;
  thm details = open_cm_stmt_children_safe(parent);
  thm rest = conjunct2_rule(details);
  thm result = fold_cm_stmt_temps_safe(
      body, conjunct1_rule(details), conjunct1_rule(rest),
      conjunct2_rule(rest));
  return gen_rule(body,
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), result));
}
PROOF thm cm_rep_stmt_block_child_safe =
    prove_cm_rep_stmt_block_child_safe();

PROOF thm prove_cm_rep_stmt_if_children_safe(void) {
  term guard = `guard:cm_expr`;
  term yes = `yes:cm_stmt`;
  term no = `no:cm_stmt`;
  term parent =
      `CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)`;
  thm details = open_cm_stmt_children_safe(parent);
  thm rest1 = conjunct2_rule(details);
  thm rest2 = conjunct2_rule(rest1);
  thm rest3 = conjunct2_rule(rest2);
  thm rest4 = conjunct2_rule(rest3);
  thm rest5 = conjunct2_rule(rest4);
  thm yes_safe = fold_cm_stmt_temps_safe(
      yes, conjunct1_rule(rest1), conjunct1_rule(rest2),
      conjunct1_rule(rest3));
  thm no_safe = fold_cm_stmt_temps_safe(
      no, conjunct1_rule(rest4), conjunct1_rule(rest5),
      conjunct2_rule(rest5));
  thm result = conj_rule(conjunct1_rule(details),
      conj_rule(yes_safe, no_safe));
  return genl_rule(TERM_LIST(guard, yes, no),
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), result));
}
PROOF thm cm_rep_stmt_if_children_safe =
    prove_cm_rep_stmt_if_children_safe();

PROOF thm prove_cm_rep_stmt_while_children_safe(void) {
  term guard = `guard:cm_expr`;
  term body = `body:cm_stmt`;
  term parent = `CMWhileS (guard:cm_expr) (body:cm_stmt)`;
  thm details = open_cm_stmt_children_safe(parent);
  thm rest1 = conjunct2_rule(details);
  thm rest2 = conjunct2_rule(rest1);
  thm result = conj_rule(conjunct1_rule(details),
      fold_cm_stmt_temps_safe(
        body, conjunct1_rule(rest1), conjunct1_rule(rest2),
        conjunct2_rule(rest2)));
  return genl_rule(TERM_LIST(guard, body),
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), result));
}
PROOF thm cm_rep_stmt_while_children_safe =
    prove_cm_rep_stmt_while_children_safe();

PROOF thm prove_cm_rep_stmt_return_child_safe(void) {
  term parent = `CMReturnS (expr:cm_expr)`;
  thm child = open_cm_stmt_children_safe(parent);
  return gen_rule(`expr:cm_expr`,
      disch_rule(mk_comb(`cm_rep_stmt_temps_safe`, parent), child));
}
PROOF thm cm_rep_stmt_return_child_safe =
    prove_cm_rep_stmt_return_child_safe();
PROOF thm cm_rep_binding_array_def = new_fun_definition(
    `cm_rep_binding_array (globals:(cm_global_d)list)
       (locals:(cm_slot_d)list) (scope:int) (slot:int) : int =
       (if scope == 0i then cm_rep_global_array globals slot
        else if scope == 1i then cm_rep_member_array locals slot
        else 0i)`);
PROOF thm cm_rep_struct_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_struct_size ([]:(cm_struct_d)list) (sid:int) = 0i) &&
     (!strct rest sid.
        cm_rep_struct_size
          ((strct:cm_struct_d) :: (rest:(cm_struct_d)list)) (sid:int) =
        (if sid == 0i
         then cm_rep_members_size (cm_struct_members strct)
         else cm_rep_struct_size rest (sid - 1i)))`);
PROOF thm cm_rep_struct_member_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_struct_member_prefix ([]:(cm_struct_d)list)
        (sid:int) (index:int) = 0i) &&
     (!strct rest sid index.
        cm_rep_struct_member_prefix
          ((strct:cm_struct_d) :: (rest:(cm_struct_d)list))
          (sid:int) (index:int) =
        (if sid == 0i
         then cm_rep_member_prefix (cm_struct_members strct) index
         else cm_rep_struct_member_prefix rest (sid - 1i) index))`);
PROOF thm cm_rep_struct_member_array_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_struct_member_array ([]:(cm_struct_d)list)
        (sid:int) (index:int) = 0i) &&
     (!strct rest sid index.
        cm_rep_struct_member_array
          ((strct:cm_struct_d) :: (rest:(cm_struct_d)list))
          (sid:int) (index:int) =
        (if sid == 0i
         then cm_rep_member_array (cm_struct_members strct) index
         else cm_rep_struct_member_array rest (sid - 1i) index))`);
PROOF thm cm_rep_member_array_code_def = new_fun_definition(
    `cm_rep_member_array_code (structs:(cm_struct_d)list)
       (base_ty:int) (mid:int) : int =
       cm_rep_struct_member_array structs
         (((base_ty - 1024i) rem 1024i) - 2i) mid`);

PROOF static thm cm_prove_rep_struct_member_array_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) sid mid.
         0i <= sid ==>
         sid < ilength structs ==>
         0i <= mid ==>
         mid < ilength
           (cm_struct_members (inth sid structs)) ==>
         cm_rep_struct_member_array structs sid mid ==
           cm_rep_nonzero
             (cm_slot_count
               (inth mid (cm_struct_members (inth sid structs))))`);
  gnode_list cases = INDUCT_TAC(root, `structs:(cm_struct_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(sid:int) < ilength ([]:(cm_struct_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (sid:int) ==> sid < 0i ==> F`),
        assume_rule(`0i <= (sid:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list sid_cases =
        BOOL_CASES_TAC(leaf, `(sid:int) == 0i`, "Hsid");
    {
      thm struct_head = by_rewrite(
          `inth (sid:int)
             ((a0:cm_struct_d) :: (a1:(cm_struct_d)list)) == a0`,
          THM_LIST(assume_rule(`(sid:int) == 0i`),
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF")));
      thm member_bound = conv_rule(rewrite_conv(THM_LIST(struct_head)),
          assume_rule(
            `(mid:int) <
             ilength (cm_struct_members
               (inth (sid:int)
                 ((a0:cm_struct_d) :: (a1:(cm_struct_d)list))))`));
      thm member = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `cm_struct_members (a0:cm_struct_d)`, `mid:int`),
          cm_rep_member_array_at),
          assume_rule(`0i <= (mid:int)`)), member_bound);
      gnode reduced = CONV_WITH_ASMP_TAC(
          sid_cases[0], reduce_rewrite_conv, THM_LIST(
            assume_rule(`(sid:int) == 0i`),
            cm_rep_struct_member_array_def, struct_head));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, member);
      }
    }
    {
      thm sid_nonnegative = assume_rule(`0i <= (sid:int)`);
      thm sid_nonzero = assume_rule(`~((sid:int) == 0i)`);
      thm lower = mp_rule(mp_rule(int_arith_rule(
          `0i <= (sid:int) ==> ~(sid == 0i) ==> 1i <= sid`),
          sid_nonnegative), sid_nonzero);
      thm length_step = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), assume_rule(
            `(sid:int) <
             ilength ((a0:cm_struct_d) :: (a1:(cm_struct_d)list))`));
      thm tail_bound = mp_rule(int_arith_rule(
          `(sid:int) < 1i + ilength (a1:(cm_struct_d)list) ==>
           sid - 1i < ilength a1`), length_step);
      thm tail_nonnegative = mp_rule(int_arith_rule(
          `1i <= (sid:int) ==> 0i <= sid - 1i`), lower);
      thm lookup = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_struct_d`, `a1:(cm_struct_d)list`, `sid:int`),
          cm_rep_inth_cons_tail), lower);
      thm member_bound = conv_rule(rewrite_conv(THM_LIST(lookup)),
          assume_rule(
            `(mid:int) <
             ilength (cm_struct_members
               (inth (sid:int)
                 ((a0:cm_struct_d) :: (a1:(cm_struct_d)list))))`));
      thm ih = assume_rule(
          `!sid mid.
             0i <= sid ==>
             sid < ilength (a1:(cm_struct_d)list) ==>
             0i <= mid ==>
             mid < ilength
               (cm_struct_members (inth sid a1)) ==>
             cm_rep_struct_member_array a1 sid mid ==
               cm_rep_nonzero
                 (cm_slot_count
                   (inth mid (cm_struct_members (inth sid a1))))`);
      thm result = specl_rule(
          TERM_LIST(`(sid:int) - 1i`, `mid:int`), ih);
      result = mp_rule(result, tail_nonnegative);
      result = mp_rule(result, tail_bound);
      result = mp_rule(result, assume_rule(`0i <= (mid:int)`));
      result = mp_rule(result, member_bound);
      gnode reduced = CONV_WITH_ASMP_TAC(
          sid_cases[1], reduce_rewrite_conv, THM_LIST(
            cm_rep_struct_member_array_def, lookup));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, result);
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_member_array_at =
    cm_prove_rep_struct_member_array_at();
PROOF thm cm_rep_type_size_def = new_fun_definition(
    `cm_rep_type_size (structs:(cm_struct_d)list)
       (code:int) : int =
       (if 1024i <= code then 8i
        else if code == 0i then 8i
        else if code == 1i then 1i
        else cm_rep_struct_size structs (code - 2i))`);
PROOF thm cm_rep_structs_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_structs_safe ([]:(cm_struct_d)list) = T) &&
     (!strct rest.
        (cm_rep_structs_safe
          ((strct:cm_struct_d) :: (rest:(cm_struct_d)list)) <=>
         cm_rep_members_safe (cm_struct_members strct) &&
         cm_rep_structs_safe rest))`);
PROOF thm cm_rep_strings_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_strings_safe ([]:(cm_string_d)list) = T) &&
     (!string rest.
        (cm_rep_strings_safe
          ((string:cm_string_d) :: (rest:(cm_string_d)list)) <=>
         0i <= cm_rep_string_size string &&
         0i <= cm_rep_strings_size rest &&
         cm_rep_strings_size (string :: rest) <= 1048560i &&
         cm_rep_strings_safe rest))`);
PROOF thm cm_rep_program_valid_def = new_fun_definition(
    `cm_rep_program_valid (program:cm_program) : int =
       (if cm_wf_program program then 1i else 0i)`);
PROOF thm cm_program_heap_rep_def = new_fun_definition(
    `cm_program_heap_rep (p:int) (program:cm_program) : hprop =
       (exists zs zg zstr zf.
          fact(~(p == 0i)) **
          data_at (field_addr p Tcm_program Fstructs) Tptr zs **
          data_at (field_addr p Tcm_program Fglobals) Tptr zg **
          data_at (field_addr p Tcm_program Fstrings) Tptr zstr **
          data_at (field_addr p Tcm_program Ffunctions) Tptr zf **
          data_at (field_addr p Tcm_program Fmain_id) Tint
            (cm_program_main program) **
          cm_struct_list_rep zs (cm_program_structs program) **
          cm_global_list_rep zg (cm_program_globals program) **
          cm_string_list_rep zstr (cm_program_strings program) **
          cm_function_list_rep zf (cm_program_functions program))`);
PROOF thm cm_program_rep_def = new_fun_definition(
    `cm_program_rep (p:int) (program:cm_program) : hprop =
       (fact(cm_rep_program_valid program == 1i) **
        cm_program_heap_rep p program)`);

PROOF thm cm_rep_ops_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_ops ([]:(tvm_inst)list) = ([]:(int)list)) &&
     (!inst rest.
       cm_rep_ops ((inst:tvm_inst) :: (rest:(tvm_inst)list)) =
       tvm_opcode_code (tvm_inst_op inst) :: cm_rep_ops rest)`);
PROOF thm cm_rep_imms_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_rep_imms ([]:(tvm_inst)list) = ([]:(int)list)) &&
     (!inst rest.
       cm_rep_imms ((inst:tvm_inst) :: (rest:(tvm_inst)list)) =
       tvm_inst_imm inst :: cm_rep_imms rest)`);

/*
 * Public-buffer decoding is deterministic.  The validity witness rejects a
 * malformed opcode/immediate pair; the decoded code itself is computed from
 * the buffers, and data bytes become dense patches at addresses 8+i.
 */
PROOF thm cm_decode_pairs_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!imms.
        cm_decode_pairs ([]:(int)list) (imms:(int)list) =
          ([]:(tvm_inst)list)) &&
     (!op rest imms.
        cm_decode_pairs ((op:int) :: (rest:(int)list))
          (imms:(int)list) =
        (if imms == [] then []
         else tvm_decode_pair op (HD imms) ::
              cm_decode_pairs rest (TL imms)))`);
PROOF int _e_cm_decode_pairs =
    cst_add_const_to_header(`cm_decode_pairs`);

PROOF static thm cm_prove_decode_pairs_rep(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list).
         cm_decode_pairs (cm_rep_ops code) (cm_rep_imms code) == code`);
  gnode_list cases = INDUCT_TAC(root, `code:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_decode_pairs_def, cm_rep_ops_def, cm_rep_imms_def,
        get_tvm_decode_pair_def(), get_tvm_opcode_roundtrip(),
        get_tvm_inst_reconstruct(), get_theorem_by_name("HD"),
        get_theorem_by_name("TL"),
        get_theorem_by_name("NOT_CONS_NIL")));
  }
  return gnode_prove(root);
}
PROOF thm cm_decode_pairs_rep = cm_prove_decode_pairs_rep();

PROOF thm cm_output_decodes_def = new_fun_definition(
    `cm_output_decodes (entry:int) (ops:(int)list)
       (imms:(int)list) (data:(int)list) (obj:tvm_object) : bool =
       ((?code.
           tvm_code_shape (code:(tvm_inst)list) &&
           ops == cm_rep_ops code &&
           imms == cm_rep_imms code) &&
        obj == TVMObject entry (cm_decode_pairs ops imms)
          (cm_bytes_patches data 8i))`);
PROOF int _e_cm_output_decodes =
    cst_add_const_to_header(`cm_output_decodes`);

PROOF static thm cm_prove_output_decode_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!entry ops imms data obj1 obj2.
         cm_output_decodes (entry:int) (ops:(int)list)
           (imms:(int)list) (data:(int)list) (obj1:tvm_object) &&
         cm_output_decodes entry ops imms data (obj2:tvm_object) ==>
         obj1 == obj2`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm premises = assume_rule(
      `cm_output_decodes (entry:int) (ops:(int)list)
         (imms:(int)list) (data:(int)list) (obj1:tvm_object) &&
       cm_output_decodes entry ops imms data (obj2:tvm_object)`);
  thm first = conv_rule(rewrite_conv(THM_LIST(cm_output_decodes_def)),
      conjunct1_rule(premises));
  thm second = conv_rule(rewrite_conv(THM_LIST(cm_output_decodes_def)),
      conjunct2_rule(premises));
  ACCEPT_TAC(leaf, trans_rule(
      conjunct2_rule(first), sym_rule(conjunct2_rule(second))));
  return gnode_prove(root);
}
PROOF thm cm_output_decode_unique =
    cm_prove_output_decode_unique();

PROOF thm cm_undef_int_buffer_def = new_fun_definition(
    `cm_undef_int_buffer (p:int) (n:int) : hprop =
       (if n == 0i then emp
        else fact(~(p == 0i)) ** store_undef_int_array p n)`);
PROOF thm cm_undef_int64_buffer_def = new_fun_definition(
    `cm_undef_int64_buffer (p:int) (n:int) : hprop =
       (if n == 0i then emp
        else fact(~(p == 0i)) ** store_undef_int64_array p n)`);
PROOF thm cm_undef_uint8_buffer_def = new_fun_definition(
    `cm_undef_uint8_buffer (p:int) (n:int) : hprop =
       (if n == 0i then emp
        else fact(~(p == 0i)) ** store_undef_uint8_array p n)`);

PROOF thm cm_int_prefix_buffer_def = new_fun_definition(
    `cm_int_prefix_buffer (p:int) (capacity:int)
       (values:(int)list) : hprop =
       (let n = ilength values in
        if n == 0i then cm_undef_int_buffer p capacity
        else fact(~(p == 0i)) **
             store_int_array p n values **
             store_undef_int_array
               (p + n * sizeof Tint) (capacity - n))`);
PROOF thm cm_int64_prefix_buffer_def = new_fun_definition(
    `cm_int64_prefix_buffer (p:int) (capacity:int)
       (values:(int)list) : hprop =
       (let n = ilength values in
        if n == 0i then cm_undef_int64_buffer p capacity
        else fact(~(p == 0i)) **
             store_int64_array p n values **
             store_undef_int64_array
               (p + n * sizeof Tint64) (capacity - n))`);
PROOF thm cm_uint8_prefix_buffer_def = new_fun_definition(
    `cm_uint8_prefix_buffer (p:int) (capacity:int)
       (values:(int)list) : hprop =
       (let n = ilength values in
        if n == 0i then cm_undef_uint8_buffer p capacity
        else fact(~(p == 0i)) **
             store_uint8_array p n values **
             store_undef_uint8_array
               (p + n * sizeof Tuchar) (capacity - n))`);

PROOF thm cm_output_pre_def = new_fun_definition(
    `cm_output_pre (out:int) (code_capacity:int)
       (data_capacity:int) : hprop =
       (exists ops imms data old_code old_data old_entry.
          fact(~(out == 0i)) **
          fact(0i <= code_capacity) ** fact(0i <= data_capacity) **
          data_at (field_addr out Tcm_output Fops) Tptr ops **
          data_at (field_addr out Tcm_output Fimms) Tptr imms **
          data_at (field_addr out Tcm_output Fdata) Tptr data **
          data_at (field_addr out Tcm_output Fcode_capacity) Tint
            code_capacity **
          data_at (field_addr out Tcm_output Fdata_capacity) Tint
            data_capacity **
          data_at (field_addr out Tcm_output Fcode_length) Tint old_code **
          data_at (field_addr out Tcm_output Fdata_length) Tint old_data **
          data_at (field_addr out Tcm_output Fentry) Tint old_entry **
          cm_undef_int_buffer ops code_capacity **
          cm_undef_int64_buffer imms code_capacity **
          cm_undef_uint8_buffer data data_capacity)`);

PROOF thm cm_output_capacity_def = new_fun_definition(
    `cm_output_capacity (out:int) (code_capacity:int)
       (data_capacity:int) (p:cm_program) : hprop =
       (exists ops imms data.
          fact(~(out == 0i)) **
          fact(0i <= code_capacity) ** fact(0i <= data_capacity) **
          fact(cm_model_code_length p > code_capacity ||
               cm_model_data_length p > data_capacity) **
          data_at (field_addr out Tcm_output Fops) Tptr ops **
          data_at (field_addr out Tcm_output Fimms) Tptr imms **
          data_at (field_addr out Tcm_output Fdata) Tptr data **
          data_at (field_addr out Tcm_output Fcode_capacity) Tint
            code_capacity **
          data_at (field_addr out Tcm_output Fdata_capacity) Tint
            data_capacity **
          data_at (field_addr out Tcm_output Fcode_length) Tint
            (cm_model_code_length p) **
          data_at (field_addr out Tcm_output Fdata_length) Tint
            (cm_model_data_length p) **
          data_at (field_addr out Tcm_output Fentry) Tint (--1i) **
          cm_undef_int_buffer ops code_capacity **
          cm_undef_int64_buffer imms code_capacity **
          cm_undef_uint8_buffer data data_capacity)`);

PROOF thm cm_output_ok_def = new_fun_definition(
    `cm_output_ok (out:int) (code_capacity:int)
       (data_capacity:int) (p:cm_program) : hprop =
       (exists ops imms data.
          fact(~(out == 0i)) **
          fact(0i <= cm_model_code_length p) **
          fact(cm_model_code_length p <= code_capacity) **
          fact(0i <= cm_model_data_length p) **
          fact(cm_model_data_length p <= data_capacity) **
          fact(!(obj:tvm_object) (input:(int)list)
                 (trace:(int)list) (status:int).
            (cm_source_terminates p input trace status <=> true) &&
            (cm_output_decodes 0i
              (cm_rep_ops (cm_model_code p))
              (cm_rep_imms (cm_model_code p))
              (cm_model_data_bytes p) obj <=> true) ==>
            (tvm_terminates obj input trace status <=> true)) **
          data_at (field_addr out Tcm_output Fops) Tptr ops **
          data_at (field_addr out Tcm_output Fimms) Tptr imms **
          data_at (field_addr out Tcm_output Fdata) Tptr data **
          data_at (field_addr out Tcm_output Fcode_capacity) Tint
            code_capacity **
          data_at (field_addr out Tcm_output Fdata_capacity) Tint
            data_capacity **
          data_at (field_addr out Tcm_output Fcode_length) Tint
            (cm_model_code_length p) **
          data_at (field_addr out Tcm_output Fdata_length) Tint
            (cm_model_data_length p) **
          data_at (field_addr out Tcm_output Fentry) Tint 0i **
          cm_int_prefix_buffer ops code_capacity
            (cm_rep_ops (cm_model_code p)) **
          cm_int64_prefix_buffer imms code_capacity
            (cm_rep_imms (cm_model_code p)) **
          cm_uint8_prefix_buffer data data_capacity
            (cm_model_data_bytes p))`);

PROOF int _e_cm_rep_ops = cst_add_const_to_header(`cm_rep_ops`);
PROOF int _e_cm_rep_imms = cst_add_const_to_header(`cm_rep_imms`);
PROOF int _e_cm_undef_int_buffer =
    cst_add_const_to_header(`cm_undef_int_buffer`);
PROOF int _e_cm_undef_int64_buffer =
    cst_add_const_to_header(`cm_undef_int64_buffer`);
PROOF int _e_cm_undef_uint8_buffer =
    cst_add_const_to_header(`cm_undef_uint8_buffer`);
PROOF int _e_cm_int_prefix_buffer =
    cst_add_const_to_header(`cm_int_prefix_buffer`);
PROOF int _e_cm_int64_prefix_buffer =
    cst_add_const_to_header(`cm_int64_prefix_buffer`);
PROOF int _e_cm_uint8_prefix_buffer =
    cst_add_const_to_header(`cm_uint8_prefix_buffer`);
PROOF int _e_cm_output_pre = cst_add_const_to_header(`cm_output_pre`);
PROOF int _e_cm_output_capacity =
    cst_add_const_to_header(`cm_output_capacity`);
PROOF int _e_cm_output_ok = cst_add_const_to_header(`cm_output_ok`);

PROOF static thm cm_prove_model_output_decodes(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_output_decodes 0i
           (cm_rep_ops (cm_model_code p))
           (cm_rep_imms (cm_model_code p))
           (cm_model_data_bytes p)
           (cm_compile_model p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm admissible_parts = eq_mp_rule(
      apply_conversion(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(), get_cm_codegen_admissible_def())),
        concl(wf)), wf);
  thm fields = admissible_parts;
  for (size_t i = 0; i < 7; ++i) {
    fields = conjunct2_rule(fields);
  }
  fields = conjunct1_rule(fields);
  thm field_parts = eq_mp_rule(
      apply_conversion(rewrite_conv(THM_LIST(
        get_cm_codegen_fields_representable_def())), concl(fields)),
      fields);
  thm code_shape = conjunct1_rule(field_parts);
  gnode decoded = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_output_decodes_def)));
  gnode_list parts = CONJ_TAC(decoded);
  gnode witnessed = EXISTS_TAC(
      parts[0], `cm_model_code (p:cm_program)`);
  CONV_TAC(witnessed, reduce_rewrite_conv(THM_LIST(code_shape)));
  CONV_TAC(parts[1], reduce_rewrite_conv(THM_LIST(
      cm_decode_pairs_rep, get_cm_compile_model_def(),
      get_cm_model_patches_def())));
  return gnode_prove(root);
}
PROOF thm cm_model_output_decodes =
    cm_prove_model_output_decodes();

PROOF thm mk_cm_slot_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p slots. ~(p == 0i) ==>
       (cm_slot_list_rep (p:int) (slots:(cm_slot_d)list) |--
        exists slot_ rest_ zn_.
          fact(slots == (slot_:cm_slot_d) :: (rest_:(cm_slot_d)list)) **
          data_at (field_addr p Tcm_slot Fty) Tint
            (cm_type_encode (cm_slot_ty slot_)) **
          data_at (field_addr p Tcm_slot Fcount) Tint
            (cm_slot_count slot_) **
          data_at (field_addr p Tcm_slot Fnext) Tptr zn_ **
          cm_slot_list_rep zn_ rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `slots:(cm_slot_d)list`, "Hslots");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_slot_list_rep_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_slot_list_rep_def));
  gnode opened = HANT_EXISTS_SLTAC(cons, "H", "zn_");
  gnode witnessed = LIST_EXISTS_SLTAC(opened,
      TERM_LIST(`a0:cm_slot_d`, `a1:(cm_slot_d)list`, `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_slot_unfold = mk_cm_slot_unfold();

PROOF thm mk_cm_slot_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p slots. p == 0i ==>
       (cm_slot_list_rep (p:int) (slots:(cm_slot_d)list) |--
        fact(slots == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `slots:(cm_slot_d)list`, "Hslots");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_slot_list_rep_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_slot_list_rep_def));
  gnode opened = HANT_EXISTS_SLTAC(cons, "H", "zn_");
  gnode split = HANT_SEP_SLTAC(opened, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");

  return gnode_prove(root);
}
PROOF thm cm_slot_null = mk_cm_slot_null();
PROOF thm mk_cm_slot_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p slot_ rest_ zn_. ~(p == 0i) ==>
       (data_at (field_addr p Tcm_slot Fty) Tint
          (cm_type_encode (cm_slot_ty (slot_:cm_slot_d))) **
        data_at (field_addr p Tcm_slot Fcount) Tint
          (cm_slot_count slot_) **
        data_at (field_addr p Tcm_slot Fnext) Tptr (zn_:int) **
        cm_slot_list_rep zn_ (rest_:(cm_slot_d)list) |--
        cm_slot_list_rep p (slot_ :: rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(cm_slot_list_rep_def)));
  gnode witnessed = EXISTS_SLTAC(converted, `zn_:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_slot_fold = mk_cm_slot_fold();
PROOF thm mk_cm_member_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p members. ~(p == 0i) ==>
       (cm_member_list_rep (p:int) (members:(cm_slot_d)list) |--
        exists member_ rest_ zn_.
          fact(members == (member_:cm_slot_d) ::
            (rest_:(cm_slot_d)list)) **
          data_at (field_addr p Tcm_member Fty) Tint
            (cm_type_encode (cm_slot_ty member_)) **
          data_at (field_addr p Tcm_member Fcount) Tint
            (cm_slot_count member_) **
          data_at (field_addr p Tcm_member Fnext) Tptr zn_ **
          cm_member_list_rep zn_ rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `members:(cm_slot_d)list`, "Hmembers");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_member_list_rep_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_member_list_rep_def));
  gnode opened = HANT_EXISTS_SLTAC(cons, "H", "zn_");
  gnode witnessed = LIST_EXISTS_SLTAC(opened,
      TERM_LIST(`a0:cm_slot_d`, `a1:(cm_slot_d)list`, `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_member_unfold = mk_cm_member_unfold();

PROOF thm mk_cm_member_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p members. p == 0i ==>
       (cm_member_list_rep (p:int) (members:(cm_slot_d)list) |--
        fact(members == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `members:(cm_slot_d)list`, "Hmembers");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_member_list_rep_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_member_list_rep_def));
  gnode opened = HANT_EXISTS_SLTAC(cons, "H", "zn_");
  gnode split = HANT_SEP_SLTAC(opened, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_member_null = mk_cm_member_null();

PROOF thm mk_cm_member_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p member_ rest_ zn_. ~(p == 0i) ==>
       (data_at (field_addr p Tcm_member Fty) Tint
          (cm_type_encode (cm_slot_ty (member_:cm_slot_d))) **
        data_at (field_addr p Tcm_member Fcount) Tint
          (cm_slot_count member_) **
        data_at (field_addr p Tcm_member Fnext) Tptr (zn_:int) **
        cm_member_list_rep zn_ (rest_:(cm_slot_d)list) |--
        cm_member_list_rep p (member_ :: rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(cm_member_list_rep_def)));
  gnode witnessed = EXISTS_SLTAC(converted, `zn_:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_member_fold = mk_cm_member_fold();
PROOF thm mk_cm_global_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p globals. ~(p == 0i) ==>
       (cm_global_list_rep (p:int) (globals:(cm_global_d)list) |--
        exists global_ rest_ zn_.
          fact(globals == (global_:cm_global_d) ::
            (rest_:(cm_global_d)list)) **
          data_at (field_addr p Tcm_global Fty) Tint
            (cm_type_encode (cm_global_ty global_)) **
          data_at (field_addr p Tcm_global Fcount) Tint
            (cm_global_count global_) **
          data_at (field_addr p Tcm_global Fhas_init) Tint
            (cm_rep_bool (cm_global_has_init global_)) **
          data_at (field_addr p Tcm_global Finit) Tint64
            (cm_global_init global_) **
          data_at (field_addr p Tcm_global Fnext) Tptr zn_ **
          cm_global_list_rep zn_ rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `globals:(cm_global_d)list`, "Hglobals");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_global_list_rep_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_global_list_rep_def));
  gnode opened = HANT_EXISTS_SLTAC(cons, "H", "zn_");
  gnode witnessed = LIST_EXISTS_SLTAC(opened,
      TERM_LIST(`a0:cm_global_d`, `a1:(cm_global_d)list`, `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_global_unfold = mk_cm_global_unfold();

PROOF thm mk_cm_global_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p globals. p == 0i ==>
       (cm_global_list_rep (p:int) (globals:(cm_global_d)list) |--
        fact(globals == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `globals:(cm_global_d)list`, "Hglobals");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_global_list_rep_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_global_list_rep_def));
  gnode opened = HANT_EXISTS_SLTAC(cons, "H", "zn_");
  gnode split = HANT_SEP_SLTAC(opened, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_global_null = mk_cm_global_null();

PROOF thm mk_cm_global_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p global_ rest_ zn_. ~(p == 0i) ==>
       (data_at (field_addr p Tcm_global Fty) Tint
          (cm_type_encode (cm_global_ty (global_:cm_global_d))) **
        data_at (field_addr p Tcm_global Fcount) Tint
          (cm_global_count global_) **
        data_at (field_addr p Tcm_global Fhas_init) Tint
          (cm_rep_bool (cm_global_has_init global_)) **
        data_at (field_addr p Tcm_global Finit) Tint64
          (cm_global_init global_) **
        data_at (field_addr p Tcm_global Fnext) Tptr (zn_:int) **
        cm_global_list_rep zn_ (rest_:(cm_global_d)list) |--
        cm_global_list_rep p (global_ :: rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(cm_global_list_rep_def)));
  gnode witnessed = EXISTS_SLTAC(converted, `zn_:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_global_fold = mk_cm_global_fold();


PROOF thm mk_cm_struct_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p structs. ~(p == 0i) ==>
       (cm_struct_list_rep (p:int) (structs:(cm_struct_d)list) |--
        exists strct_ rest_ zm_ zn_.
          fact(structs == (strct_:cm_struct_d) ::
            (rest_:(cm_struct_d)list)) **
          data_at (field_addr p Tcm_struct Fmembers) Tptr zm_ **
          data_at (field_addr p Tcm_struct Fnext) Tptr zn_ **
          cm_member_list_rep zm_ (cm_struct_members strct_) **
          cm_struct_list_rep zn_ rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `structs:(cm_struct_d)list`, "Hstructs");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_struct_list_rep_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_struct_list_rep_def));
  gnode opened_members = HANT_EXISTS_SLTAC(cons, "H", "zm_");
  gnode opened_next = HANT_EXISTS_SLTAC(
      opened_members, "H", "zn_");
  gnode witnessed = LIST_EXISTS_SLTAC(opened_next,
      TERM_LIST(`a0:cm_struct_d`, `a1:(cm_struct_d)list`,
        `zm_:int`, `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_struct_unfold = mk_cm_struct_unfold();

PROOF thm mk_cm_struct_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p structs. p == 0i ==>
       (cm_struct_list_rep (p:int) (structs:(cm_struct_d)list) |--
        fact(structs == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `structs:(cm_struct_d)list`, "Hstructs");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_struct_list_rep_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_struct_list_rep_def));
  gnode opened_members = HANT_EXISTS_SLTAC(cons, "H", "zm_");
  gnode opened_next = HANT_EXISTS_SLTAC(
      opened_members, "H", "zn_");
  gnode split = HANT_SEP_SLTAC(
      opened_next, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_struct_null = mk_cm_struct_null();

PROOF thm mk_cm_struct_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p strct_ rest_ zm_ zn_. ~(p == 0i) ==>
       (data_at (field_addr p Tcm_struct Fmembers) Tptr (zm_:int) **
        data_at (field_addr p Tcm_struct Fnext) Tptr (zn_:int) **
        cm_member_list_rep zm_ (cm_struct_members (strct_:cm_struct_d)) **
        cm_struct_list_rep zn_ (rest_:(cm_struct_d)list) |--
        cm_struct_list_rep p (strct_ :: rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(cm_struct_list_rep_def)));
  gnode members_witness = EXISTS_SLTAC(converted, `zm_:int`);
  gnode next_witness = EXISTS_SLTAC(members_witness, `zn_:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      next_witness, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_struct_fold = mk_cm_struct_fold();

PROOF thm mk_cm_string_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p strings. ~(p == 0i) ==>
       (cm_string_list_rep (p:int) (strings:(cm_string_d)list) |--
        exists string_ rest_ zb_ zn_.
          fact(strings == (string_:cm_string_d) ::
            (rest_:(cm_string_d)list)) **
          data_at (field_addr p Tcm_string Fbytes) Tptr zb_ **
          data_at (field_addr p Tcm_string Flength) Tint
            (cm_rep_string_length string_) **
          data_at (field_addr p Tcm_string Fnext) Tptr zn_ **
          cm_uint8_buffer zb_ (cm_string_bytes string_) **
          cm_string_list_rep zn_ rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `strings:(cm_string_d)list`, "Hstrings");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_string_list_rep_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_string_list_rep_def));
  gnode opened_bytes = HANT_EXISTS_SLTAC(cons, "H", "zb_");
  gnode opened_next = HANT_EXISTS_SLTAC(
      opened_bytes, "H", "zn_");
  gnode witnessed = LIST_EXISTS_SLTAC(opened_next,
      TERM_LIST(`a0:cm_string_d`, `a1:(cm_string_d)list`,
        `zb_:int`, `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_string_unfold = mk_cm_string_unfold();

PROOF thm mk_cm_string_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p strings. p == 0i ==>
       (cm_string_list_rep (p:int) (strings:(cm_string_d)list) |--
        fact(strings == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `strings:(cm_string_d)list`, "Hstrings");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv, THM_LIST(cm_string_list_rep_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv, THM_LIST(cm_string_list_rep_def));
  gnode opened_bytes = HANT_EXISTS_SLTAC(cons, "H", "zb_");
  gnode opened_next = HANT_EXISTS_SLTAC(
      opened_bytes, "H", "zn_");
  gnode split = HANT_SEP_SLTAC(
      opened_next, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_string_null = mk_cm_string_null();

PROOF thm mk_cm_string_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p string_ rest_ zb_ zn_. ~(p == 0i) ==>
       (data_at (field_addr p Tcm_string Fbytes) Tptr (zb_:int) **
        data_at (field_addr p Tcm_string Flength) Tint
          (cm_rep_string_length (string_:cm_string_d)) **
        data_at (field_addr p Tcm_string Fnext) Tptr (zn_:int) **
        cm_uint8_buffer zb_ (cm_string_bytes string_) **
        cm_string_list_rep zn_ (rest_:(cm_string_d)list) |--
        cm_string_list_rep p (string_ :: rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(cm_string_list_rep_def)));
  gnode bytes_witness = EXISTS_SLTAC(converted, `zb_:int`);
  gnode next_witness = EXISTS_SLTAC(bytes_witness, `zn_:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      next_witness, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_string_fold = mk_cm_string_fold();
PROOF thm mk_cm_function_header_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p functions bodies. ~(p == 0i) ==>
       (cm_function_header_list_rep (p:int)
          (functions:(cm_function_d)list) (bodies:(int)list) |--
        exists fn_ rest_ body_ body_rest_ zp_ zl_ zn_.
          fact(functions == (fn_:cm_function_d) ::
            (rest_:(cm_function_d)list) &&
            bodies == (body_:int) :: (body_rest_:(int)list)) **
          data_at (field_addr p Tcm_function Fret_ty) Tint
            (cm_type_encode (cm_function_ret fn_)) **
          data_at (field_addr p Tcm_function Fparams) Tptr zp_ **
          data_at (field_addr p Tcm_function Flocals) Tptr zl_ **
          data_at (field_addr p Tcm_function Fbody) Tptr body_ **
          data_at (field_addr p Tcm_function Fnext) Tptr zn_ **
          cm_slot_list_rep zp_ (cm_function_params fn_) **
          cm_slot_list_rep zl_ (cm_function_locals fn_) **
          cm_function_header_list_rep zn_ rest_ body_rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `functions:(cm_function_d)list`, "Hfunctions");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv,
      THM_LIST(cm_function_header_list_rep_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv,
      THM_LIST(cm_function_header_list_rep_def));
  gnode zp = HANT_EXISTS_SLTAC(cons, "H", "zp_");
  gnode zl = HANT_EXISTS_SLTAC(zp, "H", "zl_");
  gnode body = HANT_EXISTS_SLTAC(zl, "H", "body_");
  gnode next = HANT_EXISTS_SLTAC(body, "H", "zn_");
  gnode body_rest =
      HANT_EXISTS_SLTAC(next, "H", "body_rest_");
  gnode witnessed = LIST_EXISTS_SLTAC(body_rest,
      TERM_LIST(`a0:cm_function_d`,
        `a1:(cm_function_d)list`, `body_:int`,
        `body_rest_:(int)list`, `zp_:int`, `zl_:int`,
        `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_function_header_unfold =
    mk_cm_function_header_unfold();

PROOF thm mk_cm_function_header_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p functions bodies. p == 0i ==>
       (cm_function_header_list_rep (p:int)
          (functions:(cm_function_d)list) (bodies:(int)list) |--
        fact(functions == [] && bodies == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `functions:(cm_function_d)list`, "Hfunctions");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv,
      THM_LIST(cm_function_header_list_rep_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv,
      THM_LIST(cm_function_header_list_rep_def));
  gnode zp = HANT_EXISTS_SLTAC(cons, "H", "zp_");
  gnode zl = HANT_EXISTS_SLTAC(zp, "H", "zl_");
  gnode body = HANT_EXISTS_SLTAC(zl, "H", "body_");
  gnode next = HANT_EXISTS_SLTAC(body, "H", "zn_");
  gnode body_rest =
      HANT_EXISTS_SLTAC(next, "H", "body_rest_");
  gnode split = HANT_SEP_SLTAC(
      body_rest, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_function_header_null =
    mk_cm_function_header_null();

PROOF thm mk_cm_function_header_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p fn_ rest_ body_ body_rest_ zp_ zl_ zn_.
       ~(p == 0i) ==>
       (data_at (field_addr p Tcm_function Fret_ty) Tint
          (cm_type_encode (cm_function_ret (fn_:cm_function_d))) **
        data_at (field_addr p Tcm_function Fparams) Tptr (zp_:int) **
        data_at (field_addr p Tcm_function Flocals) Tptr (zl_:int) **
        data_at (field_addr p Tcm_function Fbody) Tptr (body_:int) **
        data_at (field_addr p Tcm_function Fnext) Tptr (zn_:int) **
        cm_slot_list_rep zp_ (cm_function_params fn_) **
        cm_slot_list_rep zl_ (cm_function_locals fn_) **
        cm_function_header_list_rep zn_
          (rest_:(cm_function_d)list) (body_rest_:(int)list) |--
        cm_function_header_list_rep p (fn_ :: rest_)
          (body_ :: body_rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(
        THM_LIST(cm_function_header_list_rep_def)));
  gnode zp = EXISTS_SLTAC(converted, `zp_:int`);
  gnode zl = EXISTS_SLTAC(zp, `zl_:int`);
  gnode body = EXISTS_SLTAC(zl, `body_:int`);
  gnode next = EXISTS_SLTAC(body, `zn_:int`);
  gnode body_rest = EXISTS_SLTAC(next, `body_rest_:(int)list`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      body_rest, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_function_header_fold =
    mk_cm_function_header_fold();


PROOF thm mk_cm_program_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p program zs zg zstr zf.
       (fact(cm_rep_program_valid (program:cm_program) == 1i) **
        fact(~((p:int) == 0i)) **
        data_at (field_addr p Tcm_program Fstructs) Tptr (zs:int) **
        data_at (field_addr p Tcm_program Fglobals) Tptr (zg:int) **
        data_at (field_addr p Tcm_program Fstrings) Tptr (zstr:int) **
        data_at (field_addr p Tcm_program Ffunctions) Tptr (zf:int) **
        data_at (field_addr p Tcm_program Fmain_id) Tint
          (cm_program_main (program:cm_program)) **
        cm_struct_list_rep zs (cm_program_structs program) **
        cm_global_list_rep zg (cm_program_globals program) **
        cm_string_list_rep zstr (cm_program_strings program) **
        cm_function_list_rep zf (cm_program_functions program) |--
        cm_program_rep p program)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(
        cm_program_rep_def, cm_program_heap_rep_def)));
  gnode pulled = EXISTS_PULL_SLTAC(converted);
  gnode struct_witness = EXISTS_SLTAC(pulled, `zs:int`);
  gnode global_witness = EXISTS_SLTAC(struct_witness, `zg:int`);
  gnode string_witness = EXISTS_SLTAC(global_witness, `zstr:int`);
  gnode function_witness = EXISTS_SLTAC(string_witness, `zf:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      function_witness, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_program_fold = mk_cm_program_fold();

PROOF static thm cm_view_open(
    const term predicate, const thm_list definitions,
    const term_list variables) {
  thm view = apply_conversion(rewrite_conv(definitions), predicate);
  return genl_rule(variables, eq2ent(view));
}

PROOF static thm cm_view_close(
    const term predicate, const thm_list definitions,
    const term_list variables) {
  thm view = apply_conversion(rewrite_conv(definitions), predicate);
  return genl_rule(variables, eq2ent(sym_rule(view)));
}

PROOF thm mk_cm_arg_unfold(void) {
  gnode root = gnode_new_with_ccl(
      `!p args. ~(p == 0i) ==>
       (cm_arg_list_rep (p:int) (args:(cm_expr)list) |--
        exists arg_ rest_ ze_ zn_.
          fact(args == (arg_:cm_expr) ::
            (rest_:(cm_expr)list)) **
          data_at (field_addr p Tcm_arg Fexpr) Tptr ze_ **
          data_at (field_addr p Tcm_arg Fnext) Tptr zn_ **
          cm_expr_rep ze_ arg_ **
          cm_arg_list_rep zn_ rest_)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `args:(cm_expr)list`, "Hargs");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv,
      THM_LIST(cm_arg_list_rep_def, cm_expr_payload_def));
  CONTR_SLTAC(nil, "H");
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv,
      THM_LIST(cm_arg_list_rep_def, cm_expr_rep_def,
        cm_expr_payload_def));
  gnode opened_expr = HANT_EXISTS_SLTAC(cons, "H", "ze_");
  gnode opened_next = HANT_EXISTS_SLTAC(
      opened_expr, "H", "zn_");
  gnode witnessed = LIST_EXISTS_SLTAC(opened_next,
      TERM_LIST(`a0:cm_expr`, `a1:(cm_expr)list`,
        `ze_:int`, `zn_:int`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_arg_unfold = mk_cm_arg_unfold();

PROOF thm mk_cm_arg_null(void) {
  gnode root = gnode_new_with_ccl(
      `!p args. p == 0i ==>
       (cm_arg_list_rep (p:int) (args:(cm_expr)list) |--
        fact(args == []))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode_list cases = CASES_TAC(
      initialized[0], `args:(cm_expr)list`, "Hargs");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv,
      THM_LIST(cm_arg_list_rep_def, cm_expr_payload_def));
  gnode nil_clean = CLEAN_SLTAC(nil);
  AUTO_FRAME_SLTAC(nil_clean);
  gnode cons = CONV_WITH_ASMP_SLTAC(
      cases[1], rewrite_conv,
      THM_LIST(cm_arg_list_rep_def, cm_expr_payload_def));
  gnode opened_expr = HANT_EXISTS_SLTAC(cons, "H", "ze_");
  gnode opened_next = HANT_EXISTS_SLTAC(
      opened_expr, "H", "zn_");
  gnode split = HANT_SEP_SLTAC(
      opened_next, "H", "Hfact", "Hrest");
  CONTR_SLTAC(split, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_arg_null = mk_cm_arg_null();

PROOF thm mk_cm_arg_fold(void) {
  gnode root = gnode_new_with_ccl(
      `!p arg_ rest_ ze_ zn_. ~(p == 0i) ==>
       (data_at (field_addr p Tcm_arg Fexpr) Tptr (ze_:int) **
        data_at (field_addr p Tcm_arg Fnext) Tptr (zn_:int) **
        cm_expr_node ze_ (arg_:cm_expr) (cm_expr_payload arg_) **
        cm_arg_tree (rest_:(cm_expr)list) zn_ |--
        cm_arg_list_rep p (arg_ :: rest_))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(introduced);
  gnode converted = HCON_CONV_SLTAC(
      initialized[0], rewrite_conv(THM_LIST(
        cm_arg_list_rep_def, cm_expr_payload_def)));
  gnode expr_witness = EXISTS_SLTAC(converted, `ze_:int`);
  gnode next_witness = EXISTS_SLTAC(expr_witness, `zn_:int`);
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      next_witness, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_arg_fold = mk_cm_arg_fold();

PROOF thm mk_cm_expr_close_witness(void) {
  term body =
      `fact(~((p:int) == 0i)) **
       data_at (field_addr p Tcm_expr Fkind) Tint
         (cm_rep_expr_kind (e:cm_expr)) **
       data_at (field_addr p Tcm_expr Fop) Tint
         (cm_rep_expr_op e) **
       data_at (field_addr p Tcm_expr Fty) Tint
         (cm_type_encode (cm_expr_type e)) **
       data_at (field_addr p Tcm_expr Fvalue) Tint64
         (cm_rep_expr_value e) **
       data_at (field_addr p Tcm_expr Fa) Tptr (za:int) **
       data_at (field_addr p Tcm_expr Fb) Tptr (zb:int) **
       data_at (field_addr p Tcm_expr Fargs) Tptr (zargs:int) **
       cm_expr_payload e za zb zargs`;
  term args_exists = mk_sl_exists(`zargs:int`, body);
  thm args_intro = exists_slrule(
      args_exists, `zargs:int`, refl_slrule(body));
  term b_exists = mk_sl_exists(`zb:int`, args_exists);
  thm b_intro = exists_slrule(b_exists, `zb:int`, args_intro);
  term all_exists = mk_sl_exists(`za:int`, b_exists);
  thm all_intro = exists_slrule(all_exists, `za:int`, b_intro);
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_expr_rep_def, cm_expr_node_def)),
      `cm_expr_rep (p:int) (e:cm_expr)`);
  thm folded = trans_slrule(all_intro, eq2ent(sym_rule(view)));
  return genl_rule(
      TERM_LIST(`p:int`, `e:cm_expr`, `za:int`, `zb:int`,
        `zargs:int`),
      folded);
}
PROOF thm cm_expr_close_witness = mk_cm_expr_close_witness();

PROOF thm cm_expr_open = cm_view_open(
    `cm_expr_rep (p:int) (e:cm_expr)`,
    THM_LIST(cm_expr_rep_def, cm_expr_node_def),
    TERM_LIST(`p:int`, `e:cm_expr`));
PROOF thm cm_expr_close = cm_view_close(
    `cm_expr_rep (p:int) (e:cm_expr)`,
    THM_LIST(cm_expr_rep_def, cm_expr_node_def),
    TERM_LIST(`p:int`, `e:cm_expr`));
PROOF thm cm_arg_cons_open = cm_view_open(
    `cm_arg_list_rep (p:int)
       ((arg:cm_expr) :: (rest:(cm_expr)list))`,
    THM_LIST(cm_arg_list_rep_def, cm_expr_payload_def),
    TERM_LIST(`p:int`, `arg:cm_expr`, `rest:(cm_expr)list`));
PROOF thm cm_arg_cons_close = cm_view_close(
    `cm_arg_list_rep (p:int)
       ((arg:cm_expr) :: (rest:(cm_expr)list))`,
    THM_LIST(cm_arg_list_rep_def, cm_expr_payload_def),
    TERM_LIST(`p:int`, `arg:cm_expr`, `rest:(cm_expr)list`));

PROOF thm mk_cm_stmt_close_witness(void) {
  term body =
      `fact(~((p:int) == 0i)) **
       data_at (field_addr p Tcm_stmt Fkind) Tint
         (cm_rep_stmt_kind (s:cm_stmt)) **
       data_at (field_addr p Tcm_stmt Fslot) Tint
         (cm_rep_stmt_slot s) **
       data_at (field_addr p Tcm_stmt Fexpr) Tptr (ze:int) **
       data_at (field_addr p Tcm_stmt Fa) Tptr (za:int) **
       data_at (field_addr p Tcm_stmt Fb) Tptr (zb:int) **
       cm_stmt_payload s ze za zb`;
  term b_exists = mk_sl_exists(`zb:int`, body);
  thm b_intro = exists_slrule(
      b_exists, `zb:int`, refl_slrule(body));
  term a_exists = mk_sl_exists(`za:int`, b_exists);
  thm a_intro = exists_slrule(a_exists, `za:int`, b_intro);
  term all_exists = mk_sl_exists(`ze:int`, a_exists);
  thm all_intro = exists_slrule(all_exists, `ze:int`, a_intro);
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_stmt_rep_def, cm_stmt_node_def)),
      `cm_stmt_rep (p:int) (s:cm_stmt)`);
  thm folded = trans_slrule(all_intro, eq2ent(sym_rule(view)));
  return genl_rule(
      TERM_LIST(`p:int`, `s:cm_stmt`, `ze:int`, `za:int`,
        `zb:int`),
      folded);
}
PROOF thm cm_stmt_close_witness = mk_cm_stmt_close_witness();

PROOF thm cm_stmt_open = cm_view_open(
    `cm_stmt_rep (p:int) (s:cm_stmt)`,
    THM_LIST(cm_stmt_rep_def, cm_stmt_node_def),
    TERM_LIST(`p:int`, `s:cm_stmt`));
PROOF thm cm_stmt_close = cm_view_close(
    `cm_stmt_rep (p:int) (s:cm_stmt)`,
    THM_LIST(cm_stmt_rep_def, cm_stmt_node_def),
    TERM_LIST(`p:int`, `s:cm_stmt`));

PROOF thm cm_slot_cons_open = cm_view_open(
    `cm_slot_list_rep (p:int)
       ((slot:cm_slot_d) :: (rest:(cm_slot_d)list))`,
    THM_LIST(cm_slot_list_rep_def),
    TERM_LIST(`p:int`, `slot:cm_slot_d`, `rest:(cm_slot_d)list`));
PROOF thm cm_slot_cons_close = cm_view_close(
    `cm_slot_list_rep (p:int)
       ((slot:cm_slot_d) :: (rest:(cm_slot_d)list))`,
    THM_LIST(cm_slot_list_rep_def),
    TERM_LIST(`p:int`, `slot:cm_slot_d`, `rest:(cm_slot_d)list`));

PROOF thm cm_member_cons_open = cm_view_open(
    `cm_member_list_rep (p:int)
       ((slot:cm_slot_d) :: (rest:(cm_slot_d)list))`,
    THM_LIST(cm_member_list_rep_def),
    TERM_LIST(`p:int`, `slot:cm_slot_d`, `rest:(cm_slot_d)list`));
PROOF thm cm_member_cons_close = cm_view_close(
    `cm_member_list_rep (p:int)
       ((slot:cm_slot_d) :: (rest:(cm_slot_d)list))`,
    THM_LIST(cm_member_list_rep_def),
    TERM_LIST(`p:int`, `slot:cm_slot_d`, `rest:(cm_slot_d)list`));

PROOF thm cm_struct_cons_open = cm_view_open(
    `cm_struct_list_rep (p:int)
       ((strct:cm_struct_d) :: (rest:(cm_struct_d)list))`,
    THM_LIST(cm_struct_list_rep_def),
    TERM_LIST(`p:int`, `strct:cm_struct_d`, `rest:(cm_struct_d)list`));
PROOF thm cm_struct_cons_close = cm_view_close(
    `cm_struct_list_rep (p:int)
       ((strct:cm_struct_d) :: (rest:(cm_struct_d)list))`,
    THM_LIST(cm_struct_list_rep_def),
    TERM_LIST(`p:int`, `strct:cm_struct_d`, `rest:(cm_struct_d)list`));

PROOF thm cm_global_cons_open = cm_view_open(
    `cm_global_list_rep (p:int)
       ((g:cm_global_d) :: (rest:(cm_global_d)list))`,
    THM_LIST(cm_global_list_rep_def),
    TERM_LIST(`p:int`, `g:cm_global_d`, `rest:(cm_global_d)list`));
PROOF thm cm_global_cons_close = cm_view_close(
    `cm_global_list_rep (p:int)
       ((g:cm_global_d) :: (rest:(cm_global_d)list))`,
    THM_LIST(cm_global_list_rep_def),
    TERM_LIST(`p:int`, `g:cm_global_d`, `rest:(cm_global_d)list`));

PROOF thm cm_string_cons_open = cm_view_open(
    `cm_string_list_rep (p:int)
       ((s:cm_string_d) :: (rest:(cm_string_d)list))`,
    THM_LIST(cm_string_list_rep_def),
    TERM_LIST(`p:int`, `s:cm_string_d`, `rest:(cm_string_d)list`));
PROOF thm cm_string_cons_close = cm_view_close(
    `cm_string_list_rep (p:int)
       ((s:cm_string_d) :: (rest:(cm_string_d)list))`,
    THM_LIST(cm_string_list_rep_def),
    TERM_LIST(`p:int`, `s:cm_string_d`, `rest:(cm_string_d)list`));

PROOF thm cm_function_cons_open = cm_view_open(
    `cm_function_list_rep (p:int)
       ((fn:cm_function_d) :: (rest:(cm_function_d)list))`,
    THM_LIST(cm_function_list_rep_def),
    TERM_LIST(`p:int`, `fn:cm_function_d`, `rest:(cm_function_d)list`));
PROOF thm cm_function_cons_close = cm_view_close(
    `cm_function_list_rep (p:int)
       ((fn:cm_function_d) :: (rest:(cm_function_d)list))`,
    THM_LIST(cm_function_list_rep_def),
    TERM_LIST(`p:int`, `fn:cm_function_d`, `rest:(cm_function_d)list`));
PROOF thm cm_function_split_open = cm_view_open(
    `cm_function_list_rep (p:int)
       (functions:(cm_function_d)list)`,
    THM_LIST(cm_function_list_rep_def),
    TERM_LIST(`p:int`, `functions:(cm_function_d)list`));
PROOF thm cm_function_split_close = cm_view_close(
    `cm_function_list_rep (p:int)
       (functions:(cm_function_d)list)`,
    THM_LIST(cm_function_list_rep_def),
    TERM_LIST(`p:int`, `functions:(cm_function_d)list`));
PROOF thm cm_function_header_cons_open = cm_view_open(
    `cm_function_header_list_rep (p:int)
       ((fn:cm_function_d) :: (rest:(cm_function_d)list))
       ((body:int) :: (body_rest:(int)list))`,
    THM_LIST(cm_function_header_list_rep_def),
    TERM_LIST(`p:int`, `fn:cm_function_d`,
      `rest:(cm_function_d)list`, `body:int`, `body_rest:(int)list`));
PROOF thm cm_function_header_cons_close = cm_view_close(
    `cm_function_header_list_rep (p:int)
       ((fn:cm_function_d) :: (rest:(cm_function_d)list))
       ((body:int) :: (body_rest:(int)list))`,
    THM_LIST(cm_function_header_list_rep_def),
    TERM_LIST(`p:int`, `fn:cm_function_d`,
      `rest:(cm_function_d)list`, `body:int`, `body_rest:(int)list`));
PROOF thm cm_function_body_cons_open = cm_view_open(
    `cm_function_body_list_rep
       ((body:int) :: (body_rest:(int)list))
       ((fn:cm_function_d) :: (rest:(cm_function_d)list))`,
    THM_LIST(cm_function_body_list_rep_def),
    TERM_LIST(`body:int`, `body_rest:(int)list`,
      `fn:cm_function_d`, `rest:(cm_function_d)list`));
PROOF thm cm_function_body_cons_close = cm_view_close(
    `cm_function_body_list_rep
       ((body:int) :: (body_rest:(int)list))
       ((fn:cm_function_d) :: (rest:(cm_function_d)list))`,
    THM_LIST(cm_function_body_list_rep_def),
    TERM_LIST(`body:int`, `body_rest:(int)list`,
      `fn:cm_function_d`, `rest:(cm_function_d)list`));

PROOF thm cm_program_open = cm_view_open(
    `cm_program_rep (p:int) (program:cm_program)`,
    THM_LIST(cm_program_rep_def, cm_program_heap_rep_def),
    TERM_LIST(`p:int`, `program:cm_program`));
PROOF thm cm_program_close = cm_view_close(
    `cm_program_rep (p:int) (program:cm_program)`,
    THM_LIST(cm_program_rep_def, cm_program_heap_rep_def),
    TERM_LIST(`p:int`, `program:cm_program`));

PROOF static thm cm_fill_begin_for(
    const term ty, const thm initialized_def, const thm undefined_def) {
  thm raw = specl_rule(
      TERM_LIST(`p:int`, ty, `n:int`), mk_begin_fill());
  thm wrapped = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(initialized_def), gsym_rule(undefined_def))), raw);
  return genl_rule(TERM_LIST(`p:int`, `n:int`), wrapped);
}

PROOF static thm cm_fill_open_for(
    const term ty, const thm undefined_def) {
  thm raw = specl_rule(
      TERM_LIST(`p:int`, ty, `n:int`, `iv:int`),
      mk_open_fill_cell());
  thm wrapped = conv_rule(rewrite_conv(
      THM_LIST(gsym_rule(undefined_def))), raw);
  return genl_rule(
      TERM_LIST(`p:int`, `n:int`, `iv:int`), wrapped);
}

PROOF static thm cm_fill_close_for(
    const term ty, const thm initialized_def) {
  thm raw = specl_rule(
      TERM_LIST(`p:int`, ty, `iv:int`, `pl:(int)list`, `v:int`),
      mk_close_fill_cell());
  thm wrapped = conv_rule(rewrite_conv(
      THM_LIST(gsym_rule(initialized_def))), raw);
  return genl_rule(
      TERM_LIST(`p:int`, `iv:int`, `pl:(int)list`, `v:int`), wrapped);
}

PROOF static thm cm_fill_finish_for(
    const term ty, const thm initialized_def, const thm undefined_def) {
  thm raw = specl_rule(
      TERM_LIST(`p:int`, ty, `n:int`, `iv:int`, `pl:(int)list`),
      mk_finish_fill());
  thm wrapped = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(initialized_def), gsym_rule(undefined_def))), raw);
  return genl_rule(
      TERM_LIST(`p:int`, `n:int`, `iv:int`, `pl:(int)list`), wrapped);
}

PROOF thm cm_begin_int_fill = cm_fill_begin_for(
    `Tint`, get_theorem_by_name("store_int_array_def"),
    get_theorem_by_name("store_undef_int_array_def"));
PROOF thm cm_open_int_fill = cm_fill_open_for(
    `Tint`, get_theorem_by_name("store_undef_int_array_def"));
PROOF thm cm_close_int_fill = cm_fill_close_for(
    `Tint`, get_theorem_by_name("store_int_array_def"));
PROOF thm cm_finish_int_fill = cm_fill_finish_for(
    `Tint`, get_theorem_by_name("store_int_array_def"),
    get_theorem_by_name("store_undef_int_array_def"));

PROOF thm cm_begin_int64_fill = cm_fill_begin_for(
    `Tint64`, get_theorem_by_name("store_int64_array_def"),
    get_theorem_by_name("store_undef_int64_array_def"));
PROOF thm cm_open_int64_fill = cm_fill_open_for(
    `Tint64`, get_theorem_by_name("store_undef_int64_array_def"));
PROOF thm cm_close_int64_fill = cm_fill_close_for(
    `Tint64`, get_theorem_by_name("store_int64_array_def"));
PROOF thm cm_finish_int64_fill = cm_fill_finish_for(
    `Tint64`, get_theorem_by_name("store_int64_array_def"),
    get_theorem_by_name("store_undef_int64_array_def"));

PROOF thm cm_begin_uint8_fill = cm_fill_begin_for(
    `Tuchar`, get_theorem_by_name("store_uint8_array_def"),
    get_theorem_by_name("store_undef_uint8_array_def"));
PROOF thm cm_open_uint8_fill = cm_fill_open_for(
    `Tuchar`, get_theorem_by_name("store_undef_uint8_array_def"));
PROOF thm cm_close_uint8_fill = cm_fill_close_for(
    `Tuchar`, get_theorem_by_name("store_uint8_array_def"));
PROOF thm cm_finish_uint8_fill = cm_fill_finish_for(
    `Tuchar`, get_theorem_by_name("store_uint8_array_def"),
    get_theorem_by_name("store_undef_uint8_array_def"));

PROOF int _e_cm_rep_expr_kind = cst_add_const_to_header(`cm_rep_expr_kind`);
PROOF int _e_cm_rep_expr_op = cst_add_const_to_header(`cm_rep_expr_op`);
PROOF int _e_cm_rep_expr_value = cst_add_const_to_header(`cm_rep_expr_value`);
PROOF int _e_cm_expr_payload = cst_add_const_to_header(`cm_expr_payload`);
PROOF int _e_cm_expr_node = cst_add_const_to_header(`cm_expr_node`);
PROOF int _e_cm_arg_tree = cst_add_const_to_header(`cm_arg_tree`);
PROOF int _e_cm_expr_rep = cst_add_const_to_header(`cm_expr_rep`);
PROOF int _e_cm_arg_list_rep = cst_add_const_to_header(`cm_arg_list_rep`);
PROOF int _e_cm_rep_stmt_kind = cst_add_const_to_header(`cm_rep_stmt_kind`);
PROOF int _e_cm_rep_stmt_slot = cst_add_const_to_header(`cm_rep_stmt_slot`);
PROOF int _e_cm_stmt_payload = cst_add_const_to_header(`cm_stmt_payload`);
PROOF int _e_cm_stmt_node = cst_add_const_to_header(`cm_stmt_node`);
PROOF int _e_cm_stmt_rep = cst_add_const_to_header(`cm_stmt_rep`);
PROOF int _e_cm_slot_list_rep = cst_add_const_to_header(`cm_slot_list_rep`);
PROOF int _e_cm_member_list_rep = cst_add_const_to_header(`cm_member_list_rep`);
PROOF int _e_cm_struct_list_rep = cst_add_const_to_header(`cm_struct_list_rep`);
PROOF int _e_cm_global_list_rep = cst_add_const_to_header(`cm_global_list_rep`);
PROOF int _e_cm_uint8_buffer = cst_add_const_to_header(`cm_uint8_buffer`);
PROOF int _e_cm_string_list_rep = cst_add_const_to_header(`cm_string_list_rep`);
PROOF int _e_cm_function_header_list_rep =
    cst_add_const_to_header(`cm_function_header_list_rep`);
PROOF int _e_cm_function_body_list_rep =
    cst_add_const_to_header(`cm_function_body_list_rep`);
PROOF int _e_cm_function_list_rep = cst_add_const_to_header(`cm_function_list_rep`);
PROOF int _e_cm_rep_bool = cst_add_const_to_header(`cm_rep_bool`);
PROOF int _e_cm_rep_string_length =
    cst_add_const_to_header(`cm_rep_string_length`);
PROOF int _e_cm_rep_string_size =
    cst_add_const_to_header(`cm_rep_string_size`);
PROOF int _e_cm_rep_strings_size =
    cst_add_const_to_header(`cm_rep_strings_size`);
PROOF int _e_cm_rep_strings_prefix =
    cst_add_const_to_header(`cm_rep_strings_prefix`);
PROOF int _e_cm_rep_slot_type =
    cst_add_const_to_header(`cm_rep_slot_type`);
PROOF int _e_cm_rep_is_pointer_code =
    cst_add_const_to_header(`cm_rep_is_pointer_code`);
PROOF int _e_cm_rep_leaf_size =
    cst_add_const_to_header(`cm_rep_leaf_size`);
PROOF int _e_cm_rep_code_slot_size =
    cst_add_const_to_header(`cm_rep_code_slot_size`);
PROOF int _e_cm_rep_member_size =
    cst_add_const_to_header(`cm_rep_member_size`);
PROOF int _e_cm_rep_members_size =
    cst_add_const_to_header(`cm_rep_members_size`);
PROOF int _e_cm_rep_members_safe =
    cst_add_const_to_header(`cm_rep_members_safe`);
PROOF int _e_cm_rep_member_prefix =
    cst_add_const_to_header(`cm_rep_member_prefix`);
PROOF int _e_cm_rep_member_array =
    cst_add_const_to_header(`cm_rep_member_array`);
PROOF int _e_cm_rep_nonzero =
    cst_add_const_to_header(`cm_rep_nonzero`);
PROOF int _e_cm_rep_global_array =
    cst_add_const_to_header(`cm_rep_global_array`);
PROOF int _e_cm_rep_global_size =
    cst_add_const_to_header(`cm_rep_global_size`);
PROOF int _e_cm_rep_globals_size =
    cst_add_const_to_header(`cm_rep_globals_size`);
PROOF int _e_cm_rep_globals_safe =
    cst_add_const_to_header(`cm_rep_globals_safe`);
PROOF int _e_cm_rep_globals_prefix =
    cst_add_const_to_header(`cm_rep_globals_prefix`);
PROOF int _e_cm_rep_global_address =
    cst_add_const_to_header(`cm_rep_global_address`);
PROOF int _e_cm_rep_string_address =
    cst_add_const_to_header(`cm_rep_string_address`);
PROOF int _e_cm_rep_struct_size =
    cst_add_const_to_header(`cm_rep_struct_size`);
PROOF int _e_cm_rep_struct_member_prefix =
    cst_add_const_to_header(`cm_rep_struct_member_prefix`);
PROOF int _e_cm_rep_struct_member_array =
    cst_add_const_to_header(`cm_rep_struct_member_array`);
PROOF int _e_cm_rep_args_length =
    cst_add_const_to_header(`cm_rep_args_length`);
PROOF int _e_cm_rep_args_safe =
    cst_add_const_to_header(`cm_rep_args_safe`);
PROOF int _e_cm_rep_tpair_safe =
    cst_add_const_to_header(`cm_rep_tpair_safe`);
PROOF int _e_cm_rep_apair_safe =
    cst_add_const_to_header(`cm_rep_apair_safe`);
PROOF int _e_cm_rep_expr_temps_safe =
    cst_add_const_to_header(`cm_rep_expr_temps_safe`);
PROOF int _e_cm_rep_stmt_children_safe =
    cst_add_const_to_header(`cm_rep_stmt_children_safe`);
PROOF int _e_cm_rep_stmt_temps_safe =
    cst_add_const_to_header(`cm_rep_stmt_temps_safe`);
PROOF int _e_cm_rep_args_temps_safe =
    cst_add_const_to_header(`cm_rep_args_temps_safe`);
PROOF int _e_cm_rep_binding_array =
    cst_add_const_to_header(`cm_rep_binding_array`);
PROOF int _e_cm_rep_member_array_code =
    cst_add_const_to_header(`cm_rep_member_array_code`);
PROOF int _e_cm_rep_type_size =
    cst_add_const_to_header(`cm_rep_type_size`);
PROOF int _e_cm_rep_structs_safe =
    cst_add_const_to_header(`cm_rep_structs_safe`);
PROOF int _e_cm_rep_strings_safe =
    cst_add_const_to_header(`cm_rep_strings_safe`);
PROOF int _e_cm_rep_program_valid =
    cst_add_const_to_header(`cm_rep_program_valid`);
PROOF int _e_cm_program_rep = cst_add_const_to_header(`cm_program_rep`);

PROOF thm get_cm_rep_bool_def(void) { return cm_rep_bool_def; }
PROOF thm get_cm_rep_string_length_def(void) {
  return cm_rep_string_length_def;
}
PROOF thm get_cm_rep_string_size_def(void) {
  return cm_rep_string_size_def;
}
PROOF thm get_cm_rep_strings_size_def(void) {
  return cm_rep_strings_size_def;
}
PROOF thm get_cm_rep_strings_prefix_def(void) {
  return cm_rep_strings_prefix_def;
}
PROOF thm get_cm_rep_slot_type_def(void) {
  return cm_rep_slot_type_def;
}
PROOF thm get_cm_rep_is_pointer_code_def(void) {
  return cm_rep_is_pointer_code_def;
}
PROOF thm get_cm_rep_leaf_size_def(void) { return cm_rep_leaf_size_def; }
PROOF thm get_cm_rep_code_slot_size_def(void) {
  return cm_rep_code_slot_size_def;
}
PROOF thm get_cm_rep_member_size_def(void) {
  return cm_rep_member_size_def;
}
PROOF thm get_cm_rep_members_size_def(void) {
  return cm_rep_members_size_def;
}
PROOF thm get_cm_rep_members_safe_def(void) {
  return cm_rep_members_safe_def;
}
PROOF thm get_cm_rep_member_prefix_def(void) {
  return cm_rep_member_prefix_def;
}
PROOF thm get_cm_rep_member_array_def(void) {
  return cm_rep_member_array_def;
}
PROOF thm get_cm_rep_nonzero_def(void) {
  return cm_rep_nonzero_def;
}
PROOF thm get_cm_rep_global_array_def(void) {
  return cm_rep_global_array_def;
}
PROOF thm get_cm_rep_inth_cons_tail(void) {
  return cm_rep_inth_cons_tail;
}
PROOF thm get_cm_rep_member_array_at(void) {
  return cm_rep_member_array_at;
}
PROOF thm get_cm_rep_global_array_at(void) {
  return cm_rep_global_array_at;
}
PROOF thm get_cm_rep_global_size_def(void) {
  return cm_rep_global_size_def;
}
PROOF thm get_cm_rep_globals_size_def(void) {
  return cm_rep_globals_size_def;
}
PROOF thm get_cm_rep_globals_safe_def(void) {
  return cm_rep_globals_safe_def;
}
PROOF thm get_cm_rep_globals_prefix_def(void) {
  return cm_rep_globals_prefix_def;
}
PROOF thm get_cm_rep_global_address_def(void) {
  return cm_rep_global_address_def;
}
PROOF thm get_cm_rep_string_address_def(void) {
  return cm_rep_string_address_def;
}
PROOF thm get_cm_rep_struct_size_def(void) {
  return cm_rep_struct_size_def;
}
PROOF thm get_cm_rep_struct_member_prefix_def(void) {
  return cm_rep_struct_member_prefix_def;
}
PROOF thm get_cm_rep_struct_member_array_def(void) {
  return cm_rep_struct_member_array_def;
}
PROOF thm get_cm_rep_args_length_def(void) {
  return cm_rep_args_length_def;
}
PROOF thm get_cm_rep_args_safe_def(void) {
  return cm_rep_args_safe_def;
}
PROOF thm get_cm_rep_tpair_safe_def(void) {
  return cm_rep_tpair_safe_def;
}
PROOF thm get_cm_rep_apair_safe_def(void) {
  return cm_rep_apair_safe_def;
}
PROOF thm get_cm_rep_expr_temps_safe_def(void) {
  return cm_rep_expr_temps_safe_def;
}
PROOF thm get_cm_rep_expr_temps_safe_pair(void) {
  return cm_rep_expr_temps_safe_pair;
}
PROOF thm get_cm_rep_stmt_children_safe_def(void) {
  return cm_rep_stmt_children_safe_def;
}
PROOF thm get_cm_rep_stmt_temps_safe_def(void) {
  return cm_rep_stmt_temps_safe_def;
}
PROOF thm get_cm_rep_stmt_temps_safe_bounds(void) {
  return cm_rep_stmt_temps_safe_bounds;
}
PROOF thm get_cm_rep_stmt_expr_child_safe(void) {
  return cm_rep_stmt_expr_child_safe;
}
PROOF thm get_cm_rep_stmt_init_child_safe(void) {
  return cm_rep_stmt_init_child_safe;
}
PROOF thm get_cm_rep_stmt_seq_children_safe(void) {
  return cm_rep_stmt_seq_children_safe;
}
PROOF thm get_cm_rep_stmt_block_child_safe(void) {
  return cm_rep_stmt_block_child_safe;
}
PROOF thm get_cm_rep_stmt_if_children_safe(void) {
  return cm_rep_stmt_if_children_safe;
}
PROOF thm get_cm_rep_stmt_while_children_safe(void) {
  return cm_rep_stmt_while_children_safe;
}
PROOF thm get_cm_rep_stmt_return_child_safe(void) {
  return cm_rep_stmt_return_child_safe;
}
PROOF thm get_cm_rep_binding_array_def(void) {
  return cm_rep_binding_array_def;
}
PROOF thm get_cm_rep_member_array_code_def(void) {
  return cm_rep_member_array_code_def;
}
PROOF thm get_cm_rep_struct_member_array_at(void) {
  return cm_rep_struct_member_array_at;
}
PROOF thm get_cm_rep_type_size_def(void) {
  return cm_rep_type_size_def;
}
PROOF thm get_cm_rep_structs_safe_def(void) {
  return cm_rep_structs_safe_def;
}
PROOF thm get_cm_rep_strings_safe_def(void) {
  return cm_rep_strings_safe_def;
}
PROOF thm get_cm_rep_program_valid_def(void) {
  return cm_rep_program_valid_def;
}
PROOF thm get_cm_rep_expr_kind_def(void) { return cm_rep_expr_kind_def; }
PROOF thm get_cm_rep_expr_kind_bounds(void) {
  return cm_rep_expr_kind_bounds;
}
PROOF thm get_cm_rep_expr_kind_exhaustive(void) {
  return cm_rep_expr_kind_exhaustive;
}
PROOF thm get_cm_expr_const_shape(void) { return cm_expr_const_shape; }
PROOF thm get_cm_expr_string_shape(void) { return cm_expr_string_shape; }
PROOF thm get_cm_expr_var_shape(void) { return cm_expr_var_shape; }
PROOF thm get_cm_expr_assign_shape(void) { return cm_expr_assign_shape; }
PROOF thm get_cm_expr_binary_shape(void) { return cm_expr_binary_shape; }
PROOF thm get_cm_expr_unary_shape(void) { return cm_expr_unary_shape; }
PROOF thm get_cm_expr_index_shape(void) { return cm_expr_index_shape; }
PROOF thm get_cm_expr_member_shape(void) { return cm_expr_member_shape; }
PROOF thm get_cm_expr_call_shape(void) { return cm_expr_call_shape; }
PROOF thm get_cm_expr_sizeof_shape(void) { return cm_expr_sizeof_shape; }
PROOF thm get_cm_expr_getc_shape(void) { return cm_expr_getc_shape; }
PROOF thm get_cm_expr_putc_shape(void) { return cm_expr_putc_shape; }
PROOF thm get_cm_expr_puti_shape(void) { return cm_expr_puti_shape; }
PROOF thm get_cm_expr_exit_shape(void) { return cm_expr_exit_shape; }
PROOF thm get_cm_expr_const_shape_ent(void) {
  return cm_expr_const_shape_ent;
}
PROOF thm get_cm_expr_string_shape_ent(void) {
  return cm_expr_string_shape_ent;
}
PROOF thm get_cm_expr_var_shape_ent(void) {
  return cm_expr_var_shape_ent;
}
PROOF thm get_cm_expr_assign_shape_ent(void) {
  return cm_expr_assign_shape_ent;
}
PROOF thm get_cm_expr_binary_shape_ent(void) {
  return cm_expr_binary_shape_ent;
}
PROOF thm get_cm_expr_unary_shape_ent(void) {
  return cm_expr_unary_shape_ent;
}
PROOF thm get_cm_expr_index_shape_ent(void) {
  return cm_expr_index_shape_ent;
}
PROOF thm get_cm_expr_member_shape_ent(void) {
  return cm_expr_member_shape_ent;
}
PROOF thm get_cm_expr_call_shape_ent(void) {
  return cm_expr_call_shape_ent;
}
PROOF thm get_cm_expr_sizeof_shape_ent(void) {
  return cm_expr_sizeof_shape_ent;
}
PROOF thm get_cm_expr_getc_shape_ent(void) {
  return cm_expr_getc_shape_ent;
}
PROOF thm get_cm_expr_putc_shape_ent(void) {
  return cm_expr_putc_shape_ent;
}
PROOF thm get_cm_expr_puti_shape_ent(void) {
  return cm_expr_puti_shape_ent;
}
PROOF thm get_cm_expr_exit_shape_ent(void) {
  return cm_expr_exit_shape_ent;
}
PROOF thm get_cm_rep_expr_op_def(void) { return cm_rep_expr_op_def; }
PROOF thm get_cm_rep_expr_value_def(void) { return cm_rep_expr_value_def; }
PROOF thm get_cm_expr_node_def(void) { return cm_expr_node_def; }
PROOF thm get_cm_expr_payload_def(void) { return cm_expr_payload_def; }
PROOF thm get_cm_expr_rep_def(void) { return cm_expr_rep_def; }
PROOF thm get_cm_arg_list_rep_def(void) { return cm_arg_list_rep_def; }
PROOF thm get_cm_rep_stmt_kind_def(void) { return cm_rep_stmt_kind_def; }
PROOF thm get_cm_rep_stmt_kind_bounds(void) {
  return cm_rep_stmt_kind_bounds;
}
PROOF thm get_cm_rep_stmt_kind_exhaustive(void) {
  return cm_rep_stmt_kind_exhaustive;
}
PROOF thm get_cm_stmt_skip_shape(void) { return cm_stmt_skip_shape; }
PROOF thm get_cm_stmt_expr_shape(void) { return cm_stmt_expr_shape; }
PROOF thm get_cm_stmt_decl_shape(void) { return cm_stmt_decl_shape; }
PROOF thm get_cm_stmt_init_shape(void) { return cm_stmt_init_shape; }
PROOF thm get_cm_stmt_seq_shape(void) { return cm_stmt_seq_shape; }
PROOF thm get_cm_stmt_block_shape(void) { return cm_stmt_block_shape; }
PROOF thm get_cm_stmt_if_shape(void) { return cm_stmt_if_shape; }
PROOF thm get_cm_stmt_while_shape(void) { return cm_stmt_while_shape; }
PROOF thm get_cm_stmt_break_shape(void) { return cm_stmt_break_shape; }
PROOF thm get_cm_stmt_continue_shape(void) {
  return cm_stmt_continue_shape;
}
PROOF thm get_cm_stmt_return_shape(void) { return cm_stmt_return_shape; }
PROOF thm get_cm_stmt_skip_shape_ent(void) {
  return cm_stmt_skip_shape_ent;
}
PROOF thm get_cm_stmt_expr_shape_ent(void) {
  return cm_stmt_expr_shape_ent;
}
PROOF thm get_cm_stmt_decl_shape_ent(void) {
  return cm_stmt_decl_shape_ent;
}
PROOF thm get_cm_stmt_init_shape_ent(void) {
  return cm_stmt_init_shape_ent;
}
PROOF thm get_cm_stmt_seq_shape_ent(void) {
  return cm_stmt_seq_shape_ent;
}
PROOF thm get_cm_stmt_block_shape_ent(void) {
  return cm_stmt_block_shape_ent;
}
PROOF thm get_cm_stmt_if_shape_ent(void) {
  return cm_stmt_if_shape_ent;
}
PROOF thm get_cm_stmt_while_shape_ent(void) {
  return cm_stmt_while_shape_ent;
}
PROOF thm get_cm_stmt_break_shape_ent(void) {
  return cm_stmt_break_shape_ent;
}
PROOF thm get_cm_stmt_continue_shape_ent(void) {
  return cm_stmt_continue_shape_ent;
}
PROOF thm get_cm_stmt_return_shape_ent(void) {
  return cm_stmt_return_shape_ent;
}
PROOF thm get_cm_rep_stmt_slot_def(void) { return cm_rep_stmt_slot_def; }
PROOF thm get_cm_stmt_node_def(void) { return cm_stmt_node_def; }
PROOF thm get_cm_stmt_payload_def(void) { return cm_stmt_payload_def; }
PROOF thm get_cm_stmt_rep_def(void) { return cm_stmt_rep_def; }
PROOF thm get_cm_slot_list_rep_def(void) { return cm_slot_list_rep_def; }
PROOF thm get_cm_member_list_rep_def(void) { return cm_member_list_rep_def; }
PROOF thm get_cm_struct_list_rep_def(void) { return cm_struct_list_rep_def; }
PROOF thm get_cm_global_list_rep_def(void) { return cm_global_list_rep_def; }
PROOF thm get_cm_uint8_buffer_def(void) { return cm_uint8_buffer_def; }
PROOF thm get_cm_string_list_rep_def(void) { return cm_string_list_rep_def; }
PROOF thm get_cm_function_list_rep_def(void) { return cm_function_list_rep_def; }
PROOF thm get_cm_function_header_list_rep_def(void) {
  return cm_function_header_list_rep_def;
}
PROOF thm get_cm_function_body_list_rep_def(void) {
  return cm_function_body_list_rep_def;
}
PROOF thm get_cm_program_rep_def(void) { return cm_program_rep_def; }
PROOF thm get_cm_rep_ops_def(void) { return cm_rep_ops_def; }
PROOF thm get_cm_rep_imms_def(void) { return cm_rep_imms_def; }
PROOF thm get_cm_decode_pairs_def(void) {
  return cm_decode_pairs_def;
}
PROOF thm get_cm_decode_pairs_rep(void) {
  return cm_decode_pairs_rep;
}
PROOF thm get_cm_output_decodes_def(void) {
  return cm_output_decodes_def;
}
PROOF thm get_cm_model_output_decodes(void) {
  return cm_model_output_decodes;
}
PROOF thm get_cm_output_decode_unique(void) {
  return cm_output_decode_unique;
}
PROOF thm get_cm_undef_int_buffer_def(void) {
  return cm_undef_int_buffer_def;
}
PROOF thm get_cm_undef_int64_buffer_def(void) {
  return cm_undef_int64_buffer_def;
}
PROOF thm get_cm_undef_uint8_buffer_def(void) {
  return cm_undef_uint8_buffer_def;
}
PROOF thm get_cm_int_prefix_buffer_def(void) {
  return cm_int_prefix_buffer_def;
}
PROOF thm get_cm_int64_prefix_buffer_def(void) {
  return cm_int64_prefix_buffer_def;
}
PROOF thm get_cm_uint8_prefix_buffer_def(void) {
  return cm_uint8_prefix_buffer_def;
}
PROOF thm get_cm_output_pre_def(void) { return cm_output_pre_def; }
PROOF thm get_cm_output_capacity_def(void) {
  return cm_output_capacity_def;
}
PROOF thm get_cm_output_ok_def(void) { return cm_output_ok_def; }
PROOF thm get_cm_begin_int_fill(void) { return cm_begin_int_fill; }
PROOF thm get_cm_open_int_fill(void) { return cm_open_int_fill; }
PROOF thm get_cm_close_int_fill(void) { return cm_close_int_fill; }
PROOF thm get_cm_finish_int_fill(void) { return cm_finish_int_fill; }
PROOF thm get_cm_begin_int64_fill(void) { return cm_begin_int64_fill; }
PROOF thm get_cm_open_int64_fill(void) { return cm_open_int64_fill; }
PROOF thm get_cm_close_int64_fill(void) { return cm_close_int64_fill; }
PROOF thm get_cm_finish_int64_fill(void) { return cm_finish_int64_fill; }
PROOF thm get_cm_begin_uint8_fill(void) { return cm_begin_uint8_fill; }
PROOF thm get_cm_open_uint8_fill(void) { return cm_open_uint8_fill; }
PROOF thm get_cm_close_uint8_fill(void) { return cm_close_uint8_fill; }
PROOF thm get_cm_finish_uint8_fill(void) { return cm_finish_uint8_fill; }
PROOF thm get_cm_expr_open(void) { return cm_expr_open; }
PROOF thm get_cm_expr_close(void) { return cm_expr_close; }
PROOF thm get_cm_expr_close_witness(void) {
  return cm_expr_close_witness;
}
PROOF thm get_cm_arg_cons_open(void) { return cm_arg_cons_open; }
PROOF thm get_cm_arg_cons_close(void) { return cm_arg_cons_close; }
PROOF thm get_cm_arg_unfold(void) { return cm_arg_unfold; }
PROOF thm get_cm_arg_null(void) { return cm_arg_null; }
PROOF thm get_cm_arg_fold(void) { return cm_arg_fold; }
PROOF thm get_cm_stmt_open(void) { return cm_stmt_open; }
PROOF thm get_cm_stmt_close(void) { return cm_stmt_close; }
PROOF thm get_cm_stmt_close_witness(void) {
  return cm_stmt_close_witness;
}
PROOF thm get_cm_slot_cons_open(void) { return cm_slot_cons_open; }
PROOF thm get_cm_slot_cons_close(void) { return cm_slot_cons_close; }
PROOF thm get_cm_member_cons_open(void) { return cm_member_cons_open; }
PROOF thm get_cm_member_cons_close(void) { return cm_member_cons_close; }
PROOF thm get_cm_struct_cons_open(void) { return cm_struct_cons_open; }
PROOF thm get_cm_struct_cons_close(void) { return cm_struct_cons_close; }
PROOF thm get_cm_global_cons_open(void) { return cm_global_cons_open; }
PROOF thm get_cm_global_cons_close(void) { return cm_global_cons_close; }
PROOF thm get_cm_string_cons_open(void) { return cm_string_cons_open; }
PROOF thm get_cm_string_cons_close(void) { return cm_string_cons_close; }
PROOF thm get_cm_function_cons_open(void) { return cm_function_cons_open; }
PROOF thm get_cm_function_cons_close(void) { return cm_function_cons_close; }
PROOF thm get_cm_program_open(void) { return cm_program_open; }
PROOF thm get_cm_program_close(void) { return cm_program_close; }
PROOF thm get_cm_function_split_open(void) { return cm_function_split_open; }
PROOF thm get_cm_function_split_close(void) { return cm_function_split_close; }
PROOF thm get_cm_function_header_cons_open(void) {
  return cm_function_header_cons_open;
}
PROOF thm get_cm_function_header_cons_close(void) {
  return cm_function_header_cons_close;
}
PROOF thm get_cm_function_body_cons_open(void) {
  return cm_function_body_cons_open;
}
PROOF thm get_cm_function_body_cons_close(void) {
  return cm_function_body_cons_close;
}
PROOF thm get_cm_slot_unfold(void) { return cm_slot_unfold; }
PROOF thm get_cm_slot_null(void) { return cm_slot_null; }
PROOF thm get_cm_slot_fold(void) { return cm_slot_fold; }
PROOF thm get_cm_member_unfold(void) { return cm_member_unfold; }
PROOF thm get_cm_member_null(void) { return cm_member_null; }
PROOF thm get_cm_member_fold(void) { return cm_member_fold; }
PROOF thm get_cm_global_unfold(void) { return cm_global_unfold; }
PROOF thm get_cm_global_null(void) { return cm_global_null; }
PROOF thm get_cm_global_fold(void) { return cm_global_fold; }
PROOF thm get_cm_struct_unfold(void) { return cm_struct_unfold; }
PROOF thm get_cm_struct_null(void) { return cm_struct_null; }
PROOF thm get_cm_struct_fold(void) { return cm_struct_fold; }
PROOF thm get_cm_string_unfold(void) { return cm_string_unfold; }
PROOF thm get_cm_string_null(void) { return cm_string_null; }
PROOF thm get_cm_string_fold(void) { return cm_string_fold; }
PROOF thm get_cm_function_header_unfold(void) {
  return cm_function_header_unfold;
}
PROOF thm get_cm_function_header_null(void) {
  return cm_function_header_null;
}
PROOF thm get_cm_function_header_fold(void) {
  return cm_function_header_fold;
}
PROOF thm get_cm_program_fold(void) { return cm_program_fold; }

PROOF static int cmc_rep_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) == _cmc_rep_axioms_before,
      "cmc_rep introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cm_output_decodes_def()) &&
      vector_size(hyp(get_cm_output_decodes_def())) == 0,
      "output decoder definition is not closed");
  ENSURE_COND(!IS_NULL(get_cm_decode_pairs_def()) &&
      vector_size(hyp(get_cm_decode_pairs_def())) == 0,
      "output pair decoder definition is not closed");
  ENSURE_COND(!IS_NULL(get_cm_decode_pairs_rep()) &&
      vector_size(hyp(get_cm_decode_pairs_rep())) == 0 &&
      alpha_compare(concl(get_cm_decode_pairs_rep()),
        `!(code:(tvm_inst)list).
           cm_decode_pairs (cm_rep_ops code) (cm_rep_imms code) ==
             code`) == 0,
      "output pair decoder roundtrip has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cm_output_decode_unique()) &&
      vector_size(hyp(get_cm_output_decode_unique())) == 0 &&
      alpha_compare(concl(get_cm_output_decode_unique()),
        `!entry ops imms data obj1 obj2.
           cm_output_decodes (entry:int) (ops:(int)list)
             (imms:(int)list) (data:(int)list) (obj1:tvm_object) &&
           cm_output_decodes entry ops imms data (obj2:tvm_object) ==>
           obj1 == obj2`) == 0,
      "output decoder uniqueness has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cm_model_output_decodes()) &&
      vector_size(hyp(get_cm_model_output_decodes())) == 0 &&
      alpha_compare(concl(get_cm_model_output_decodes()),
        `!(p:cm_program).
           cm_wf_program p ==>
           cm_output_decodes 0i
             (cm_rep_ops (cm_model_code p))
             (cm_rep_imms (cm_model_code p))
             (cm_model_data_bytes p)
             (cm_compile_model p)`) == 0,
      "modeled output decoder theorem has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_rep_checks = cmc_rep_final_checks();
