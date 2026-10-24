#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_spill_transition.h"

#require "cmc_preservation_spill_semantic.c"

PROOF static size_t _cmc_preservation_spill_transition_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_staged_spills_put_next(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (values:(cm_value)list)
         (spills:(cm_spill)list) (current:int)
         (new_spill_value:cm_value).
         cm_staged_spills base values spills ==>
         current == base + ilength values ==>
         cm_staged_spills base (new_spill_value :: values)
           (cm_spill_put current new_spill_value spills)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm staged = assume_rule(
      `cm_staged_spills (base:int) (values:(cm_value)list)
        (spills:(cm_spill)list)`);
  thm current_equal = assume_rule(
      `(current:int) == (base:int) + ilength (values:(cm_value)list)`);
  thm retained_upper = mp_rule(int_arith_rule(
      `(current:int) == (base:int) + ilength (values:(cm_value)list) ==>
       base + ilength values <= current`), current_equal);
  thm retained = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `base:int`, `values:(cm_value)list`, `spills:(cm_spill)list`,
      `current:int`, `new_spill_value:cm_value`),
      cm_staged_spills_put_above), staged), retained_upper);
  retained = conv_rule(rewrite_conv(THM_LIST(current_equal)), retained);
  thm newest = conv_rule(rewrite_conv(THM_LIST(
      current_equal)), specl_rule(TERM_LIST(
        `current:int`, `new_spill_value:cm_value`,
        `spills:(cm_spill)list`), cm_spill_holds_put_same));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_staged_spills_def, current_equal)));
  ACCEPT_TAC(reduced, conj_rule(newest, retained));
  return gnode_prove(root);
}

PROOF thm cm_staged_spills_put_next =
    cm_prove_staged_spills_put_next();

PROOF static thm cm_prove_annotation_spill_plain(void) {
  gnode root = gnode_new_with_ccl(
      `!(ann:cm_annotation) (pc:int) (breakpc:int) (continuepc:int).
         cm_annotation_spill_consistent ann ==>
         cm_annotation_spill_consistent
          (cm_ann_plain pc (cm_ann_temp ann)
            breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv,
      THM_LIST(cm_annotation_spill_consistent_def,
        cm_ann_plain_def, cm_ann_temp_def, cm_ann_cursors_def,
        cm_ann_spills_def, cm_ann_saved_def));
  if (IS_NULL(reduced->solved)) {
    labeled_term_list assumptions = goal_lasmps(reduced->g);
    for (size_t index = 0; index < vector_size(assumptions); ++index) {
      thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_annotation_spill_consistent_def,
          cm_ann_plain_def, cm_ann_temp_def, cm_ann_cursors_def,
          cm_ann_spills_def, cm_ann_saved_def)),
          assume_rule(assumptions[index].tm));
      if (alpha_compare(concl(normalized), goal_ccl(reduced->g)) == 0) {
        ACCEPT_TAC(reduced, normalized);
        break;
      }
    }
  }
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_plain =
    cm_prove_annotation_spill_plain();

PROOF static thm cm_prove_annotation_spill_push(void) {
  gnode root = gnode_new_with_ccl(
      `!(ann:cm_annotation) (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int).
         cm_annotation_spill_consistent ann ==>
         ~cm_phase_is_call phase ==>
         cm_phase_spill_consistent temp (cm_ann_temp ann) phase
           (cm_ann_spills ann) ==>
         cm_annotation_spill_consistent
           (cm_ann_push phase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent (ann:cm_annotation)`);
  thm phase_consistent = assume_rule(
      `cm_phase_spill_consistent (temp:int) (cm_ann_temp ann)
        (phase:cm_aphase) (cm_ann_spills ann)`);
  thm not_call = assume_rule(`~cm_phase_is_call (phase:cm_aphase)`);
  thm old_cursors = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def)), old_consistent);
  thm result = conj_rule(phase_consistent,
      eq_mp_rule(sym_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(not_call)),
        `if cm_phase_is_call (phase:cm_aphase)
         then ~(cm_ann_saved (ann:cm_annotation) == []) &&
              cm_cursors_spill_consistent (cm_ann_temp ann)
                (cm_ann_cursors ann)
                (cm_spill_frame_spills (HD (cm_ann_saved ann)))
                (TL (cm_ann_saved ann))
         else cm_cursors_spill_consistent (cm_ann_temp ann)
                (cm_ann_cursors ann) (cm_ann_spills ann)
                (cm_ann_saved ann)`)), old_cursors));
  term target =
      `cm_annotation_spill_consistent
        (cm_ann_push (phase:cm_aphase) (pc:int) (temp:int)
          (breakpc:int) (continuepc:int) (ann:cm_annotation))`;
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_push_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def)), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_push =
    cm_prove_annotation_spill_push();

PROOF static thm cm_prove_annotation_spill_replace(void) {
  gnode root = gnode_new_with_ccl(
      `!(old_phase:cm_aphase) (new_phase:cm_aphase)
         (old_pc:int) (old_temp:int) (old_break:int)
         (old_continue:int) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (new_pc:int) (new_temp:int) (new_break:int)
         (new_continue:int).
         cm_annotation_spill_consistent
           (CMAnnotation old_pc old_temp old_break old_continue
             (CMACursor old_phase owner owner_break owner_continue ::
               rest) spills saved calls) ==>
         ~cm_phase_is_call old_phase ==>
         ~cm_phase_is_call new_phase ==>
         cm_phase_spill_consistent new_temp owner new_phase spills ==>
         cm_annotation_spill_consistent
           (cm_ann_replace new_phase new_pc new_temp
             new_break new_continue
             (CMAnnotation old_pc old_temp old_break old_continue
               (CMACursor old_phase owner owner_break owner_continue ::
                 rest) spills saved calls))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (old_pc:int) (old_temp:int) (old_break:int)
          (old_continue:int)
          (CMACursor (old_phase:cm_aphase) (owner:int)
            (owner_break:int) (owner_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm old_not_call =
      assume_rule(`~cm_phase_is_call (old_phase:cm_aphase)`);
  thm new_not_call =
      assume_rule(`~cm_phase_is_call (new_phase:cm_aphase)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def)), old_consistent);
  thm tail = conv_rule(reduce_rewrite_conv(THM_LIST(
      old_not_call)), conjunct2_rule(opened));
  term new_conditional =
      `if cm_phase_is_call (new_phase:cm_aphase)
       then ~((saved:(cm_spill_frame)list) == []) &&
            cm_cursors_spill_consistent (owner:int)
              (rest:(cm_acursor)list)
              (cm_spill_frame_spills (HD saved)) (TL saved)
       else cm_cursors_spill_consistent owner rest
              (spills:(cm_spill)list) saved`;
  thm conditional_equal = apply_conversion(
      reduce_rewrite_conv(THM_LIST(new_not_call)), new_conditional);
  thm conditional = eq_mp_rule(sym_rule(conditional_equal), tail);
  thm result = conj_rule(assume_rule(
      `cm_phase_spill_consistent (new_temp:int) (owner:int)
        (new_phase:cm_aphase) (spills:(cm_spill)list)`), conditional);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_replace_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_replace =
    cm_prove_annotation_spill_replace();

PROOF static thm cm_prove_annotation_spill_pop(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase) (old_pc:int) (old_temp:int)
         (old_break:int) (old_continue:int) (owner:int)
         (owner_break:int) (owner_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (new_pc:int).
         cm_annotation_spill_consistent
           (CMAnnotation old_pc old_temp old_break old_continue
             (CMACursor phase owner owner_break owner_continue :: rest)
             spills saved calls) ==>
         ~cm_phase_is_call phase ==>
         cm_annotation_spill_consistent
           (cm_ann_pop new_pc
             (CMAnnotation old_pc old_temp old_break old_continue
               (CMACursor phase owner owner_break owner_continue :: rest)
               spills saved calls))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (old_pc:int) (old_temp:int) (old_break:int)
          (old_continue:int)
          (CMACursor (phase:cm_aphase) (owner:int)
            (owner_break:int) (owner_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm not_call = assume_rule(`~cm_phase_is_call (phase:cm_aphase)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def)), old_consistent);
  thm tail = conv_rule(reduce_rewrite_conv(THM_LIST(
      not_call)), conjunct2_rule(opened));
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_pop_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), tail));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_pop =
    cm_prove_annotation_spill_pop();

PROOF static thm cm_prove_annotation_spill_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int) (st:cm_src_state)
         (ret:cm_type) (returnpc:int) (parent_temp:int)
         (parent_break:int) (parent_continue:int)
         (tail:(cm_acursor)list) (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_cursors_spill_consistent parent_temp tail
           caller_spills saved ==>
         cm_annotation_spill_consistent
           (cm_ann_enter_call p caller callee st ret returnpc
             parent_temp parent_break parent_continue tail
             caller_spills saved calls)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm premise = assume_rule(
      `cm_cursors_spill_consistent (parent_temp:int)
        (tail:(cm_acursor)list) (caller_spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)`);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_enter_call_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def, cm_phase_spill_consistent_def,
      cm_phase_is_call_def, cm_spill_frame_spills_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), premise));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_enter_call =
    cm_prove_annotation_spill_enter_call();

PROOF static thm cm_prove_annotation_spill_leave_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(caller:int) (env:int->int->cm_value) (fp:int)
         (regions:(cm_region)list) (ret:cm_type)
         (old_pc:int) (old_temp:int) (old_break:int)
         (old_continue:int) (parent_temp:int) (parent_break:int)
         (parent_continue:int) (rest:(cm_acursor)list)
         (current_spills:(cm_spill)list) (saved_fid:int)
         (saved_fp:int) (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (returnpc:int).
         cm_annotation_spill_consistent
           (CMAnnotation old_pc old_temp old_break old_continue
             (CMACursor (CACallP caller env fp regions ret)
               parent_temp parent_break parent_continue :: rest)
             current_spills
             (CMSpillFrame saved_fid saved_fp caller_spills :: saved)
             calls) ==>
         cm_annotation_spill_consistent
           (cm_ann_leave_call returnpc
             (CMAnnotation old_pc old_temp old_break old_continue
               (CMACursor (CACallP caller env fp regions ret)
                 parent_temp parent_break parent_continue :: rest)
               current_spills
               (CMSpillFrame saved_fid saved_fp caller_spills :: saved)
               calls))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (old_pc:int) (old_temp:int) (old_break:int)
          (old_continue:int)
          (CMACursor
            (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
              (regions:(cm_region)list) (ret:cm_type))
            (parent_temp:int) (parent_break:int) (parent_continue:int) ::
            (rest:(cm_acursor)list))
          (current_spills:(cm_spill)list)
          (CMSpillFrame (saved_fid:int) (saved_fp:int)
            (caller_spills:(cm_spill)list) ::
            (saved:(cm_spill_frame)list))
          (calls:(cm_call_sim_frame)list))`);
  thm tail = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def, cm_phase_spill_consistent_def,
      cm_phase_is_call_def, cm_spill_frame_spills_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"))), old_consistent);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_leave_call_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_spill_frame_spills_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), tail));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_leave_call =
    cm_prove_annotation_spill_leave_call();

PROOF static thm cm_prove_annotation_spill_replace_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(old_phase:cm_aphase) (new_phase:cm_aphase)
         (old_pc:int) (old_temp:int) (old_break:int)
         (old_continue:int) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (new_spill_value:cm_value)
         (new_pc:int) (new_break:int) (new_continue:int).
         cm_annotation_spill_consistent
           (CMAnnotation old_pc old_temp old_break old_continue
             (CMACursor old_phase owner owner_break owner_continue ::
               rest) spills saved calls) ==>
         ~cm_phase_is_call old_phase ==>
         ~cm_phase_is_call new_phase ==>
         cm_phase_spill_consistent (owner + 1i) owner new_phase
           (cm_spill_put owner new_spill_value spills) ==>
         cm_annotation_spill_consistent
           (cm_ann_put_spill owner new_spill_value
             (cm_ann_replace new_phase new_pc (owner + 1i)
               new_break new_continue
               (CMAnnotation old_pc old_temp old_break old_continue
                 (CMACursor old_phase owner owner_break owner_continue ::
                   rest) spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (old_pc:int) (old_temp:int) (old_break:int)
          (old_continue:int)
          (CMACursor (old_phase:cm_aphase) (owner:int)
            (owner_break:int) (owner_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm old_not_call =
      assume_rule(`~cm_phase_is_call (old_phase:cm_aphase)`);
  thm new_not_call =
      assume_rule(`~cm_phase_is_call (new_phase:cm_aphase)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def)), old_consistent);
  thm tail = conv_rule(reduce_rewrite_conv(THM_LIST(
      old_not_call)), conjunct2_rule(opened));
  thm tail_updated = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `rest:(cm_acursor)list`, `owner:int`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `owner:int`, `new_spill_value:cm_value`),
      cm_cursors_spill_consistent_put_above), tail),
      int_arith_rule(`(owner:int) <= owner`));
  term new_conditional =
      `if cm_phase_is_call (new_phase:cm_aphase)
       then ~((saved:(cm_spill_frame)list) == []) &&
            cm_cursors_spill_consistent (owner:int)
              (rest:(cm_acursor)list)
              (cm_spill_frame_spills (HD saved)) (TL saved)
       else cm_cursors_spill_consistent owner rest
              (cm_spill_put owner (new_spill_value:cm_value)
                (spills:(cm_spill)list)) saved`;
  thm conditional_equal = apply_conversion(
      reduce_rewrite_conv(THM_LIST(new_not_call)), new_conditional);
  thm conditional =
      eq_mp_rule(sym_rule(conditional_equal), tail_updated);
  thm result = conj_rule(assume_rule(
      `cm_phase_spill_consistent ((owner:int) + 1i) owner
        (new_phase:cm_aphase)
        (cm_spill_put owner (new_spill_value:cm_value)
          (spills:(cm_spill)list))`), conditional);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_put_spill_def,
      cm_ann_spills_set_def, cm_ann_replace_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_replace_store =
    cm_prove_annotation_spill_replace_store();

PROOF thm get_cm_annotation_spill_replace_store(void) {
  return cm_annotation_spill_replace_store;
}

PROOF static thm cm_prove_ilength_nonempty_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(items:('a)list).
         ~(items == []) ==>
         ilength items == 1i + ilength (TL items)`);
  gnode with_items = GEN_TAC(root, "items");
  gnode_list cases = INDUCT_TAC(with_items, `items:('a)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST()),
        assume_rule(`~(([]:('a)list) == [])`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("TL"))));
  }
  return gnode_prove(root);
}

PROOF thm cm_ilength_nonempty_tail =
    cm_prove_ilength_nonempty_tail();

PROOF static thm cm_prove_annotation_spill_arg_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(callee:int) (remaining:(cm_expr)list)
         (values:(cm_value)list) (ret:cm_type)
         (all_args:(cm_expr)list) (base_slot:int)
         (current_slot:int) (scratch:int)
         (old_pc:int) (old_temp:int) (old_break:int)
         (old_continue:int) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (new_spill_value:cm_value) (new_pc:int).
         cm_annotation_spill_consistent
           (CMAnnotation old_pc old_temp old_break old_continue
             (CMACursor
               (CAArgP callee remaining values ret all_args
                 base_slot current_slot scratch)
               owner owner_break owner_continue :: rest)
             spills saved calls) ==>
         old_temp == scratch ==>
         ~(remaining == []) ==>
         cm_annotation_spill_consistent
           (cm_ann_put_spill current_slot new_spill_value
             (cm_ann_replace
               (CAArgP callee (TL remaining)
                 (new_spill_value :: values) ret all_args
                 base_slot (current_slot + 1i) scratch)
               new_pc scratch old_break old_continue
               (CMAnnotation old_pc old_temp old_break old_continue
                 (CMACursor
                   (CAArgP callee remaining values ret all_args
                     base_slot current_slot scratch)
                   owner owner_break owner_continue :: rest)
                 spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (old_pc:int) (old_temp:int) (old_break:int)
          (old_continue:int)
          (CMACursor
            (CAArgP (callee:int) (remaining:(cm_expr)list)
              (values:(cm_value)list) (ret:cm_type)
              (all_args:(cm_expr)list) (base_slot:int)
              (current_slot:int) (scratch:int))
            (owner:int) (owner_break:int) (owner_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def, cm_phase_is_call_def,
      cm_phase_spill_consistent_def)), old_consistent);
  thm phase_parts = conjunct1_rule(opened);
  thm owner_bound = conjunct1_rule(phase_parts);
  thm after_owner = conjunct2_rule(phase_parts);
  thm base_equal = conjunct1_rule(after_owner);
  thm after_base = conjunct2_rule(after_owner);
  thm current_equal = conjunct1_rule(after_base);
  thm after_current = conjunct2_rule(after_base);
  thm scratch_equal = conjunct1_rule(after_current);
  thm after_scratch = conjunct2_rule(after_current);
  thm length_equal = conjunct1_rule(after_scratch);
  thm after_length = conjunct2_rule(after_scratch);
  thm current_bound = conjunct1_rule(after_length);
  thm staged = conjunct2_rule(after_length);
  thm tail = conjunct2_rule(opened);
  thm values_nonnegative = ispec_rule(
      `values:(cm_value)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm owner_current = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `(base_slot:int) == (owner:int) ==>
       (current_slot:int) == base_slot +
         ilength (values:(cm_value)list) ==>
       0i <= ilength values ==>
       owner <= current_slot`), base_equal), current_equal),
      values_nonnegative);
  thm tail_updated = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `rest:(cm_acursor)list`, `owner:int`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `current_slot:int`, `new_spill_value:cm_value`),
      cm_cursors_spill_consistent_put_above), tail), owner_current);
  thm staged_updated = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `base_slot:int`, `values:(cm_value)list`,
      `spills:(cm_spill)list`, `current_slot:int`,
      `new_spill_value:cm_value`), cm_staged_spills_put_next),
      staged), current_equal);
  thm next_current_equal = mp_rule(mp_rule(int_arith_rule(
      `(current_slot:int) ==
         (base_slot:int) + ilength (values:(cm_value)list) ==>
       ilength ((new_spill_value:cm_value) :: values) ==
         1i + ilength values ==>
       current_slot + 1i ==
         base_slot + ilength (new_spill_value :: values)`),
      current_equal), apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((new_spill_value:cm_value) ::
          (values:(cm_value)list))`));
  thm remaining_length = mp_rule(ispec_rule(
      `remaining:(cm_expr)list`, cm_ilength_nonempty_tail),
      assume_rule(`~((remaining:(cm_expr)list) == [])`));
  thm next_length_equal = mp_rule(mp_rule(mp_rule(
      int_arith_rule(
        `ilength (all_args:(cm_expr)list) ==
           ilength (values:(cm_value)list) + 1i +
             ilength (remaining:(cm_expr)list) ==>
         ilength remaining == 1i + ilength (TL remaining) ==>
         ilength ((new_spill_value:cm_value) :: values) ==
           1i + ilength values ==>
         ilength all_args ==
           ilength (new_spill_value :: values) + 1i +
             ilength (TL remaining)`),
      length_equal), remaining_length),
      apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((new_spill_value:cm_value) ::
          (values:(cm_value)list))`));
  thm current_strict = mp_rule(mp_rule(mp_rule(mp_rule(
      int_arith_rule(
        `(current_slot:int) ==
           (base_slot:int) + ilength (values:(cm_value)list) ==>
         (scratch:int) == base_slot +
           ilength (all_args:(cm_expr)list) ==>
         ilength all_args == ilength values + 1i +
           ilength (remaining:(cm_expr)list) ==>
         0i <= ilength remaining ==>
         current_slot < scratch`),
      current_equal), scratch_equal), length_equal),
      ispec_rule(`remaining:(cm_expr)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm next_bound = mp_rule(int_arith_rule(
      `(current_slot:int) < (scratch:int) ==>
       current_slot + 1i <= scratch`), current_strict);
  thm new_owner_bound = conv_rule(rewrite_conv(THM_LIST(
      assume_rule(`(old_temp:int) == (scratch:int)`))), owner_bound);
  thm new_phase = conj_rule(new_owner_bound,
      conj_rule(base_equal, conj_rule(next_current_equal,
        conj_rule(scratch_equal, conj_rule(next_length_equal,
          conj_rule(next_bound, staged_updated))))));
  thm result = conj_rule(new_phase, tail_updated);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_put_spill_def,
      cm_ann_spills_set_def, cm_ann_replace_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def, cm_phase_is_call_def,
      cm_phase_spill_consistent_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_arg_store =
    cm_prove_annotation_spill_arg_store();

PROOF thm get_cm_annotation_spill_arg_store(void) {
  return cm_annotation_spill_arg_store;
}

PROOF static thm cm_prove_annotation_spill_arg_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (st:cm_src_state) (ret:cm_type) (returnpc:int)
         (remaining:(cm_expr)list) (values:(cm_value)list)
         (all_args:(cm_expr)list) (base_slot:int)
         (current_slot:int) (scratch:int)
         (old_pc:int) (old_temp:int) (old_break:int)
         (old_continue:int) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (new_spill_value:cm_value).
         cm_annotation_spill_consistent
           (CMAnnotation old_pc old_temp old_break old_continue
             (CMACursor
               (CAArgP callee remaining values ret all_args
                 base_slot current_slot scratch)
               owner owner_break owner_continue :: rest)
             spills saved calls) ==>
         cm_annotation_spill_consistent
           (cm_ann_enter_call p caller callee st ret returnpc
             owner owner_break owner_continue rest
             (cm_spill_put current_slot new_spill_value spills)
             saved calls)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (old_pc:int) (old_temp:int) (old_break:int)
          (old_continue:int)
          (CMACursor
            (CAArgP (callee:int) (remaining:(cm_expr)list)
              (values:(cm_value)list) (ret:cm_type)
              (all_args:(cm_expr)list) (base_slot:int)
              (current_slot:int) (scratch:int))
            (owner:int) (owner_break:int) (owner_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def, cm_phase_is_call_def,
      cm_phase_spill_consistent_def)), old_consistent);
  thm phase_parts = conjunct1_rule(opened);
  thm after_owner = conjunct2_rule(phase_parts);
  thm base_equal = conjunct1_rule(after_owner);
  thm after_base = conjunct2_rule(after_owner);
  thm current_equal = conjunct1_rule(after_base);
  thm tail = conjunct2_rule(opened);
  thm owner_current = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `(base_slot:int) == (owner:int) ==>
       (current_slot:int) == base_slot +
         ilength (values:(cm_value)list) ==>
       0i <= ilength values ==>
       owner <= current_slot`), base_equal), current_equal),
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm tail_updated = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `rest:(cm_acursor)list`, `owner:int`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `current_slot:int`, `new_spill_value:cm_value`),
      cm_cursors_spill_consistent_put_above), tail), owner_current);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `callee:int`, `st:cm_src_state`,
      `ret:cm_type`, `returnpc:int`, `owner:int`, `owner_break:int`,
      `owner_continue:int`, `rest:(cm_acursor)list`,
      `cm_spill_put (current_slot:int) (new_spill_value:cm_value)
        (spills:(cm_spill)list)`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_annotation_spill_enter_call), tail_updated);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_arg_enter_call =
    cm_prove_annotation_spill_arg_enter_call();

PROOF thm get_cm_annotation_spill_arg_enter_call(void) {
  return cm_annotation_spill_arg_enter_call;
}

PROOF static int cmc_preservation_spill_transition_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_spill_transition_axioms_before,
      "cmc_preservation_spill_transition introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_spill_transition_checks =
    cmc_preservation_spill_transition_final_checks();
