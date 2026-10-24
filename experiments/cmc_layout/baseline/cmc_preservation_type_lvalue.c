#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_lang.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_type_value.h"
#include "cmc_preservation_type_lvalue.h"

#require "cmc_preservation_type_args.c"

PROOF static size_t _cmc_preservation_type_lvalue_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_lvalue_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (is_conj(concl(fact))) {
    thm left = cm_lvalue_pick_conjunct(
        conjunct1_rule(fact), wanted);
    if (!IS_NULL(left)) return left;
    return cm_lvalue_pick_conjunct(
        conjunct2_rule(fact), wanted);
  }
  return empty_theorem;
}


PROOF static thm cm_prove_var_lvalue_output_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (scope:int)
         (slot:int) (ty:cm_type).
         cm_expr_wf p f (CMVarE scope slot ty) ==>
         cm_lvalue_output_type p f (CMVarE scope slot ty) ==
         CMPtrTy
           (if scope == 0i
            then cm_global_ty (inth slot (cm_program_globals p))
            else if scope == 1i
                 then cm_slot_ty (inth slot (cm_function_locals f))
                 else cm_slot_ty (inth slot (cm_function_params f)))`);
  thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_lvalue_output_type_def())), goal_ccl(root->g));
  ACCEPT_TAC(root, eqt_elim_rule(view));
  return gnode_prove(root);
}
PROOF static thm cm_var_lvalue_output_type =
    cm_prove_var_lvalue_output_type();

PROOF static thm cm_prove_binding_lvalue_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type) (st:cm_src_state).
         cm_expr_wf p
           (inth fid (cm_program_functions p))
           (CMVarE scope slot ty) ==>
         cm_binding_address_ok p fid scope slot st ==>
         cm_value_type_compatible
           (if scope == 0i then cm_global_pointer p slot
            else cm_state_env st scope slot)
           (cm_lvalue_output_type p
             (inth fid (cm_program_functions p))
             (CMVarE scope slot ty))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
      `st:cm_src_state`), cm_binding_value_type_ready),
      assume_rule(
        `cm_binding_address_ok (p:cm_program) (fid:int)
          (scope:int) (slot:int) (st:cm_src_state)`));
  thm output_equal = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`,
      `scope:int`, `slot:int`, `ty:cm_type`),
      cm_var_lvalue_output_type), assume_rule(
        `cm_expr_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))
          (CMVarE (scope:int) (slot:int) (ty:cm_type))`));
  thm view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible
           (if (scope:int) == 0i
            then cm_global_pointer (p:cm_program) (slot:int)
            else cm_state_env (st:cm_src_state) scope slot)
           target`, sym_rule(output_equal)));
  ACCEPT_TAC(leaf, eq_mp_rule(view, ready));
  return gnode_prove(root);
}
PROOF thm cm_binding_lvalue_type_ready =
    cm_prove_binding_lvalue_type_ready();


PROOF static thm cm_prove_member_lvalue_output_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (base:cm_expr)
         (mid:int) (ty:cm_type).
         cm_expr_wf p f (CMMemberE base mid ty) ==>
         cm_lvalue_output_type p f (CMMemberE base mid ty) ==
         CMPtrTy
           (cm_slot_ty
             (inth mid
               (cm_struct_members
                 (inth (cm_struct_id
                         (cm_pointee (cm_expr_type base)))
                   (cm_program_structs p)))))`);
  thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_lvalue_output_type_def(), get_cm_member_lvalue_type_def())),
      goal_ccl(root->g));
  ACCEPT_TAC(root, eqt_elim_rule(view));
  return gnode_prove(root);
}
PROOF thm cm_member_lvalue_output_type =
    cm_prove_member_lvalue_output_type();

PROOF static thm cm_prove_member_result_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (base:cm_expr)
         (mid:int) (ty:cm_type) (base_value:cm_value)
         (st:cm_src_state).
         cm_expr_wf p f (CMMemberE base mid ty) ==>
         cm_value_type_compatible base_value (cm_expr_type base) ==>
         cm_ptr_member_ok p base_value mid st ==>
         cm_value_type_compatible
           (cm_ptr_member p base_value mid)
           (cm_lvalue_output_type p f
             (CMMemberE base mid ty))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm expression_wf = assume_rule(
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
        (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type))`);
  thm opened_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm member_valid = conjunct1_rule(conjunct2_rule(opened_wf));
  thm opened_valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), member_valid);
  thm base_pointer = conjunct1_rule(opened_valid);
  thm opened_ok = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_member_ok_def())), assume_rule(
        `cm_ptr_member_ok (p:cm_program) (base_value:cm_value)
          (mid:int) (st:cm_src_state)`));
  thm base_live = conjunct1_rule(opened_ok);
  thm base_view = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `base_value:cm_value`,
      `cm_expr_type (base:cm_expr)`), cm_pointer_view_type),
      assume_rule(
        `cm_value_type_compatible (base_value:cm_value)
          (cm_expr_type (base:cm_expr))`)),
      base_pointer), base_live);
  thm member_slot_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_member_slot_def(), base_view)),
      `cm_member_slot (p:cm_program) (base_value:cm_value) (mid:int) ==
       inth mid
         (cm_struct_members
           (inth (cm_struct_id
                   (cm_pointee (cm_expr_type (base:cm_expr))))
             (cm_program_structs p)))`));
  thm ready = specl_rule(TERM_LIST(
      `p:cm_program`, `base_value:cm_value`, `mid:int`),
      cm_ptr_member_type_ready);
  thm member_type_equal = beta_norm(ap_term_rule(
      `\slot:cm_slot_d. CMPtrTy (cm_slot_ty slot)`,
      member_slot_equal));
  thm static_view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible
           (cm_ptr_member (p:cm_program)
             (base_value:cm_value) (mid:int)) target`,
      member_type_equal));
  thm static_ready = eq_mp_rule(static_view, ready);
  thm output_equal = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, `base:cm_expr`,
      `mid:int`, `ty:cm_type`), cm_member_lvalue_output_type),
      expression_wf);
  thm output_view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible
           (cm_ptr_member (p:cm_program)
             (base_value:cm_value) (mid:int)) target`,
      sym_rule(output_equal)));
  ACCEPT_TAC(leaf, eq_mp_rule(output_view, static_ready));
  return gnode_prove(root);
}
PROOF thm cm_member_result_type_ready =
    cm_prove_member_result_type_ready();

PROOF static thm cm_prove_index_result_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (base:cm_expr)
         (index:cm_expr) (ty:cm_type) (base_value:cm_value)
         (offset:int) (st:cm_src_state).
         cm_expr_wf p f (CMIndexE base index ty) ==>
         cm_value_type_compatible base_value (cm_expr_type base) ==>
         cm_ptr_shift_ok (cm_program_structs p) base_value offset st ==>
         cm_value_type_compatible
           (cm_ptr_add (cm_program_structs p) base_value offset)
           (cm_lvalue_output_type p f
             (CMIndexE base index ty))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm expression_wf = assume_rule(
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
        (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type))`);
  thm opened_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm base_pointer = cm_lvalue_pick_conjunct(opened_wf,
      `cm_is_pointer (cm_expr_type (base:cm_expr))`);
  thm result_equal = cm_lvalue_pick_conjunct(opened_wf,
      `(ty:cm_type) == cm_pointee (cm_expr_type (base:cm_expr))`);
  thm opened_shift = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_shift_ok_def())), assume_rule(
        `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
          (base_value:cm_value) (offset:int) (st:cm_src_state)`));
  thm base_live = conjunct1_rule(opened_shift);
  thm base_ready = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `st:cm_src_state`,
      `base_value:cm_value`, `cm_expr_type (base:cm_expr)`,
      `offset:int`), cm_ptr_add_result_type_ready),
      assume_rule(
        `cm_value_type_compatible (base_value:cm_value)
          (cm_expr_type (base:cm_expr))`)),
      base_pointer), base_live);
  thm pointer_shape = mp_rule(spec_rule(
      `cm_expr_type (base:cm_expr)`,
      cm_pointer_type_reconstruct), base_pointer);
  thm lifted_result = beta_norm(ap_term_rule(
      `\source:cm_type. CMPtrTy source`, result_equal));
  thm target_to_base = trans_rule(lifted_result, pointer_shape);
  thm result_view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible
           (cm_ptr_add (cm_program_structs (p:cm_program))
             (base_value:cm_value) (offset:int)) target`,
      sym_rule(target_to_base)));
  thm result_ready = eq_mp_rule(result_view, base_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_lvalue_output_type_def(), get_cm_expr_array_def(),
      get_cm_expr_type_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result_ready));
  return gnode_prove(root);
}
PROOF thm cm_index_result_type_ready =
    cm_prove_index_result_type_ready();

PROOF static int cmc_preservation_type_lvalue_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_lvalue_axioms_before,
      "lvalue type proofs introduced axioms");
  ENSURE_COND(vector_size(hyp(cm_binding_lvalue_type_ready)) == 0,
      "binding lvalue theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_lvalue_checks =
    cmc_preservation_type_lvalue_final_checks();
