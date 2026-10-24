#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_annotation.h"

#require "cmc_preservation_generation_task.c"

PROOF static size_t _cmc_preservation_generation_annotation_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_spills_generation_remove(void) {
  gnode root = gnode_new_with_ccl(
      `!(spills:(cm_spill)list) (limit:int) (slot:int).
         cm_spills_generation_below limit spills ==>
         cm_spills_generation_below limit
           (cm_spill_remove slot spills)`);
  gnode_list cases = INDUCT_TAC(root, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_remove_def, cm_spills_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(goal_lasmps(leaf->g)[0].tm);
    thm old = conv_rule(rewrite_conv(THM_LIST(
        cm_spills_generation_below_def)), assume_rule(
          `cm_spills_generation_below (limit:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm tail = match_mp_rule(specl_rule(TERM_LIST(
        `limit:int`, `slot:int`), ih), conjunct2_rule(old));
    gnode_list same = BOOL_CASES_TAC(leaf,
        `cm_spill_slot (a0:cm_spill) == (slot:int)`, "Hsame");
    for (size_t i = 0; i < vector_size(same); ++i) {
      thm body = i == 0
          ? tail : conj_rule(conjunct1_rule(old), tail);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            cm_spill_remove_def, cm_spills_generation_below_def,
            i == 0
              ? eqt_intro_rule(assume_rule(
                  `cm_spill_slot (a0:cm_spill) == (slot:int)`))
              : eqf_intro_rule(assume_rule(
                  `~(cm_spill_slot (a0:cm_spill) == (slot:int))`)))),
          goal_ccl(same[i]->g));
      ACCEPT_TAC(same[i], eq_mp_rule(sym_rule(target_view), body));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_generation_remove =
    cm_prove_spills_generation_remove();

PROOF static thm cm_prove_spills_generation_put(void) {
  gnode root = gnode_new_with_ccl(
      `!(spills:(cm_spill)list) (limit:int) (slot:int)
         (spill_value:cm_value).
         cm_value_generation_below limit spill_value ==>
         cm_spills_generation_below limit spills ==>
         cm_spills_generation_below limit
           (cm_spill_put slot spill_value spills)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm removed = match_mp_rule(specl_rule(TERM_LIST(
      `spills:(cm_spill)list`, `limit:int`, `slot:int`),
      cm_spills_generation_remove), assume_rule(
        `cm_spills_generation_below (limit:int)
          (spills:(cm_spill)list)`));
  thm body = conj_rule(assume_rule(
      `cm_value_generation_below (limit:int)
        (spill_value:cm_value)`), removed);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_spill_put_def, cm_spills_generation_below_def,
        cm_spill_value_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  return gnode_prove(root);
}
PROOF thm cm_spills_generation_put =
    cm_prove_spills_generation_put();

PROOF static thm cm_close_payload_same(
    term statement, thm_list rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), assume_rule(
        goal_lasmps(leaf->g)[0].tm));
  vector_add(&rules, cm_annotation_payload_generation_below_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), old));
  return gnode_prove(root);
}

PROOF thm cm_annotation_payload_plain = cm_close_payload_same(
    `!(limit:int) (pc:int) (temp:int) (breakpc:int)
       (continuepc:int) (ann:cm_annotation).
       cm_annotation_payload_generation_below limit ann ==>
       cm_annotation_payload_generation_below limit
         (cm_ann_plain pc temp breakpc continuepc ann)`,
    THM_LIST(cm_ann_plain_def, cm_ann_spills_def, cm_ann_saved_def));

PROOF thm cm_annotation_payload_linear = cm_close_payload_same(
    `!(limit:int) (code:(tvm_inst)list) (ann:cm_annotation).
       cm_annotation_payload_generation_below limit ann ==>
       cm_annotation_payload_generation_below limit
         (cm_ann_linear code ann)`,
    THM_LIST(cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_spills_def, cm_ann_saved_def));

PROOF thm cm_annotation_payload_push = cm_close_payload_same(
    `!(limit:int) (phase:cm_aphase) (pc:int) (temp:int)
       (breakpc:int) (continuepc:int) (ann:cm_annotation).
       cm_annotation_payload_generation_below limit ann ==>
       cm_annotation_payload_generation_below limit
         (cm_ann_push phase pc temp breakpc continuepc ann)`,
    THM_LIST(cm_ann_push_def, cm_ann_spills_def, cm_ann_saved_def));

PROOF thm cm_annotation_payload_replace = cm_close_payload_same(
    `!(limit:int) (phase:cm_aphase) (pc:int) (temp:int)
       (breakpc:int) (continuepc:int) (ann:cm_annotation).
       cm_annotation_payload_generation_below limit ann ==>
       cm_annotation_payload_generation_below limit
         (cm_ann_replace phase pc temp breakpc continuepc ann)`,
    THM_LIST(cm_ann_replace_def, cm_ann_spills_def, cm_ann_saved_def));

PROOF thm cm_annotation_payload_pop = cm_close_payload_same(
    `!(limit:int) (pc:int) (ann:cm_annotation).
       cm_annotation_payload_generation_below limit ann ==>
       cm_annotation_payload_generation_below limit
         (cm_ann_pop pc ann)`,
    THM_LIST(cm_ann_pop_def, cm_ann_spills_def, cm_ann_saved_def));

PROOF static thm cm_prove_annotation_payload_put_spill(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (slot:int) (spill_value:cm_value)
         (ann:cm_annotation).
         cm_value_generation_below limit spill_value ==>
         cm_annotation_payload_generation_below limit ann ==>
         cm_annotation_payload_generation_below limit
           (cm_ann_put_spill slot spill_value ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), assume_rule(
        `cm_annotation_payload_generation_below (limit:int)
          (ann:cm_annotation)`));
  thm spills = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_ann_spills (ann:cm_annotation)`, `limit:int`, `slot:int`,
      `spill_value:cm_value`), cm_spills_generation_put), assume_rule(
        `cm_value_generation_below (limit:int)
          (spill_value:cm_value)`)), conjunct1_rule(old));
  thm body = conj_rule(spills, conjunct2_rule(old));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_payload_generation_below_def,
        cm_ann_put_spill_def, cm_ann_spills_set_def,
        cm_ann_spills_def, cm_ann_saved_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  return gnode_prove(root);
}
PROOF thm cm_annotation_payload_put_spill =
    cm_prove_annotation_payload_put_spill();

PROOF static thm cm_prove_annotation_payload_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (caller:int) (callee:int)
         (st:cm_src_state) (ret:cm_type) (returnpc:int)
         (parent_temp:int) (parent_break:int) (parent_continue:int)
         (tail:(cm_acursor)list) (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_spills_generation_below limit caller_spills ==>
         cm_spill_frames_generation_below limit saved ==>
         cm_annotation_payload_generation_below limit
           (cm_ann_enter_call p caller callee st ret returnpc
             parent_temp parent_break parent_continue tail
             caller_spills saved calls)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm body = conj_rule(assume_rule(
      `cm_spills_generation_below (limit:int)
        (caller_spills:(cm_spill)list)`), assume_rule(
      `cm_spill_frames_generation_below (limit:int)
        (saved:(cm_spill_frame)list)`));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_payload_generation_below_def,
        cm_ann_enter_call_def, cm_ann_spills_def, cm_ann_saved_def,
        cm_spill_frames_generation_below_def,
        cm_spill_frame_spills_def,
        cm_spills_generation_below_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  return gnode_prove(root);
}
PROOF thm cm_annotation_payload_enter_call =
    cm_prove_annotation_payload_enter_call();

PROOF static thm cm_prove_annotation_payload_leave_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (returnpc:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (frame:cm_spill_frame) (rest:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_payload_generation_below limit
           (CMAnnotation pc temp breakpc continuepc cursors spills
             (frame :: rest) calls) ==>
         cm_annotation_payload_generation_below limit
           (cm_ann_leave_call returnpc
             (CMAnnotation pc temp breakpc continuepc cursors spills
               (frame :: rest) calls))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def,
      cm_ann_spills_def, cm_ann_saved_def,
      cm_spill_frames_generation_below_def)), assume_rule(
        `cm_annotation_payload_generation_below (limit:int)
          (CMAnnotation (pc:int) (temp:int) (breakpc:int)
            (continuepc:int) (cursors:(cm_acursor)list)
            (spills:(cm_spill)list)
            ((frame:cm_spill_frame) ::
             (rest:(cm_spill_frame)list))
            (calls:(cm_call_sim_frame)list))`));
  thm body = conjunct2_rule(old);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_payload_generation_below_def,
        cm_ann_leave_call_def, cm_ann_spills_def, cm_ann_saved_def,
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  return gnode_prove(root);
}
PROOF thm cm_annotation_payload_leave_call =
    cm_prove_annotation_payload_leave_call();

PROOF static int cmc_preservation_generation_annotation_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_annotation_axioms_before,
      "cmc_preservation_generation_annotation introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_annotation_payload_leave_call)) == 0,
      "annotation payload leave-call theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_generation_annotation_checks =
    cmc_preservation_generation_annotation_final_checks();
