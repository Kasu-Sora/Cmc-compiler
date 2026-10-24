#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_spill_semantic.h"

#require "cmc_preservation_code.c"
#require "cmc_preservation_code_value.c"
#require "cmc_sim.c"

PROOF static size_t _cmc_preservation_spill_semantic_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_spill_semantic_contains_const(
    term subject, const char *name) {
  if (is_const(subject)) {
    return strcmp(dest_const(subject).s, name) == 0;
  }
  if (is_comb(subject)) {
    struct dest_comb_results application = dest_comb(subject);
    return cm_spill_semantic_contains_const(application.tm1, name) ||
        cm_spill_semantic_contains_const(application.tm2, name);
  }
  return false;
}
PROOF static bool cm_spill_semantic_has_head_const(
    term subject, const char *name) {
  while (is_comb(subject)) {
    subject = dest_comb(subject).tm1;
  }
  return is_const(subject) &&
      strcmp(dest_const(subject).s, name) == 0;
}


/* Values accumulated by argument evaluation are kept in reverse order.  The
 * newest value therefore occupies base + LENGTH(rest). */
PROOF thm cm_staged_spills_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!base spills.
        cm_staged_spills (base:int) ([]:(cm_value)list)
          (spills:(cm_spill)list) = T) &&
     (!base value rest spills.
        cm_staged_spills (base:int)
          ((value:cm_value) :: (rest:(cm_value)list))
          (spills:(cm_spill)list) =
        (cm_spill_holds (base + ilength rest) value spills &&
         cm_staged_spills base rest spills))`);

/* Every non-call phase owns a half-open temporary interval [owner, limit).
 * Saved values must lie in that interval.  Call cursors switch to the saved
 * caller spill frame and therefore impose no relation on the callee interval. */
PROOF thm cm_phase_spill_consistent_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!limit owner. cm_phase_spill_consistent (limit:int) (owner:int)
        CAHaltP (spills:(cm_spill)list) = (owner <= limit)) &&
     (!limit owner ty. cm_phase_spill_consistent limit owner
        (CALoadP (ty:cm_type)) spills = (owner <= limit)) &&
     (!limit owner src ty. cm_phase_spill_consistent limit owner
        (CAAssignLP (src:cm_expr) (ty:cm_type)) spills =
        (owner <= limit)) &&
     (!limit owner ptr ty. cm_phase_spill_consistent limit owner
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) spills =
        (owner < limit && cm_spill_holds owner ptr spills)) &&
     (!limit owner op left right ty. cm_phase_spill_consistent limit owner
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type))
        spills = (owner <= limit)) &&
     (!limit owner op left right value ty.
        cm_phase_spill_consistent limit owner
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (value:cm_value) (ty:cm_type)) spills =
        (owner <= limit &&
         ((op == 0i || op == 1i) ||
          (owner < limit && cm_spill_holds owner value spills)))) &&
     (!limit owner op. cm_phase_spill_consistent limit owner
        (CAUnaryP (op:int)) spills = (owner <= limit)) &&
     (!limit owner index ty. cm_phase_spill_consistent limit owner
        (CAIndexLP (index:cm_expr) (ty:cm_type)) spills =
        (owner <= limit)) &&
     (!limit owner base ty. cm_phase_spill_consistent limit owner
        (CAIndexRP (base:cm_value) (ty:cm_type)) spills =
        (owner < limit && cm_spill_holds owner base spills)) &&
     (!limit owner mid base_ty. cm_phase_spill_consistent limit owner
        (CAMemberP (mid:int) (base_ty:cm_type)) spills =
        (owner <= limit)) &&
     (!limit owner. cm_phase_spill_consistent limit owner CAPutcP spills =
        (owner <= limit)) &&
     (!limit owner. cm_phase_spill_consistent limit owner CAPutiP spills =
        (owner <= limit)) &&
     (!limit owner. cm_phase_spill_consistent limit owner CAExitP spills =
        (owner <= limit)) &&
     (!limit owner. cm_phase_spill_consistent limit owner CAExprStmtP spills =
        (owner <= limit)) &&
     (!limit owner slot. cm_phase_spill_consistent limit owner
        (CAInitP (slot:int)) spills = (owner <= limit)) &&
     (!limit owner env regions jump target.
        cm_phase_spill_consistent limit owner
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) spills = (owner <= limit)) &&
     (!limit owner second. cm_phase_spill_consistent limit owner
        (CASeqP (second:cm_stmt)) spills = (owner <= limit)) &&
     (!limit owner yes no. cm_phase_spill_consistent limit owner
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) spills = (owner <= limit)) &&
     (!limit owner guard body loop_start loop_end.
        cm_phase_spill_consistent limit owner
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) spills = (owner <= limit)) &&
     (!limit owner guard body env regions loop_start loop_end.
        cm_phase_spill_consistent limit owner
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) spills = (owner <= limit)) &&
     (!limit owner. cm_phase_spill_consistent limit owner CAReturnP spills =
        (owner <= limit)) &&
     (!limit owner callee rest values ret all_args base_slot current_slot
         scratch.
        cm_phase_spill_consistent limit owner
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) spills =
        (owner <= limit && base_slot == owner &&
         current_slot == base_slot + ilength values &&
         scratch == base_slot + ilength all_args &&
         ilength all_args ==
           ilength values + 1i + ilength rest &&
         current_slot <= limit &&
         cm_staged_spills base_slot values spills)) &&
     (!limit owner caller env fp regions ret.
        cm_phase_spill_consistent limit owner
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) spills = T)`);

PROOF thm cm_cursors_spill_consistent_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!limit spills saved.
        cm_cursors_spill_consistent (limit:int) ([]:(cm_acursor)list)
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list) = T) &&
     (!limit cursor rest spills saved.
        cm_cursors_spill_consistent (limit:int)
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list) =
        (cm_phase_spill_consistent limit (cm_cursor_temp cursor)
           (cm_cursor_phase cursor) spills &&
         (if cm_phase_is_call (cm_cursor_phase cursor)
          then ~(saved == []) &&
               cm_cursors_spill_consistent (cm_cursor_temp cursor) rest
                 (cm_spill_frame_spills (HD saved)) (TL saved)
          else cm_cursors_spill_consistent (cm_cursor_temp cursor) rest
                 spills saved)))`);

PROOF thm cm_annotation_spill_consistent_def = new_fun_definition(
    `cm_annotation_spill_consistent (ann:cm_annotation) : bool =
       cm_cursors_spill_consistent (cm_ann_temp ann)
         (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann)`);

PROOF static thm cm_prove_spill_holds_remove_other(void) {
  gnode root = gnode_new_with_ccl(
      `!(slot:int) (other:int) (held_value:cm_value)
         (spills:(cm_spill)list).
         ~(other == slot) ==>
         cm_spill_holds other held_value spills ==>
         cm_spill_holds other held_value (cm_spill_remove slot spills)`);
  gnode with_slot = GEN_TAC(root, "slot");
  gnode with_other = GEN_TAC(with_slot, "other");
  gnode with_value = GEN_TAC(with_other, "held_value");
  gnode_list cases =
      INDUCT_TAC(with_value, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_spill_holds_def)), assume_rule(
          `cm_spill_holds (other:int) (held_value:cm_value)
            ([]:(cm_spill)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm different = assume_rule(`~((other:int) == (slot:int))`);
    thm holds = assume_rule(
        `cm_spill_holds (other:int) (held_value:cm_value)
          ((a0:cm_spill) :: (a1:(cm_spill)list))`);
    thm ih = assume_rule(
        `~((other:int) == (slot:int)) ==>
         cm_spill_holds other (held_value:cm_value) (a1:(cm_spill)list) ==>
         cm_spill_holds other held_value (cm_spill_remove slot a1)`);
    gnode_list slot_cases = BOOL_CASES_TAC(
        leaf, `cm_spill_slot (a0:cm_spill) == (slot:int)`,
        "Hremoved");
    {
      thm removed = assume_rule(
          `cm_spill_slot (a0:cm_spill) == (slot:int)`);
      thm head_different = not_intro(
          `cm_spill_slot (a0:cm_spill) == (other:int)`,
          contra(different, trans_rule(sym_rule(assume_rule(
            `cm_spill_slot (a0:cm_spill) == (other:int)`)), removed)));
      thm tail_holds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_spill_holds_def, head_different)), holds);
      thm result = mp_rule(mp_rule(ih, different), tail_holds);
      gnode reduced = CONV_TAC(slot_cases[0],
          reduce_rewrite_conv(THM_LIST(cm_spill_remove_def, removed)));
      ACCEPT_TAC(reduced, result);
    }
    {
      thm retained = assume_rule(
          `~(cm_spill_slot (a0:cm_spill) == (slot:int))`);
      gnode_list other_cases = BOOL_CASES_TAC(
          slot_cases[1],
          `cm_spill_slot (a0:cm_spill) == (other:int)`,
          "Hselected");
      {
        thm selected = assume_rule(
            `cm_spill_slot (a0:cm_spill) == (other:int)`);
        thm selected_value = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_spill_holds_def, selected)), holds);
        CONV_WITH_ASMP_TAC(other_cases[0], reduce_rewrite_conv,
            THM_LIST(cm_spill_remove_def, cm_spill_holds_def,
              retained, selected, selected_value));
      }
      {
        thm skipped = assume_rule(
            `~(cm_spill_slot (a0:cm_spill) == (other:int))`);
        thm tail_holds = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_spill_holds_def, skipped)), holds);
        thm result = mp_rule(mp_rule(ih, different), tail_holds);
        gnode reduced = CONV_TAC(other_cases[1],
            reduce_rewrite_conv(THM_LIST(
              cm_spill_remove_def, cm_spill_holds_def,
              retained, skipped)));
        ACCEPT_TAC(reduced, result);
      }
    }
  }
  return gnode_prove(root);
}

PROOF static thm cm_spill_holds_remove_other =
    cm_prove_spill_holds_remove_other();

PROOF static thm cm_prove_spill_holds_put_same(void) {
  gnode root = gnode_new_with_ccl(
      `!(slot:int) (held_value:cm_value) (spills:(cm_spill)list).
         cm_spill_holds slot held_value
           (cm_spill_put slot held_value spills)`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      cm_spill_put_def, cm_spill_holds_def,
      cm_spill_slot_def, cm_spill_value_def)));
  return gnode_prove(root);
}

PROOF thm cm_spill_holds_put_same =
    cm_prove_spill_holds_put_same();

PROOF static thm cm_prove_spill_holds_put_other(void) {
  gnode root = gnode_new_with_ccl(
      `!(slot:int) (new_spill_value:cm_value) (other:int)
         (held_value:cm_value) (spills:(cm_spill)list).
         ~(other == slot) ==>
         cm_spill_holds other held_value spills ==>
         cm_spill_holds other held_value
           (cm_spill_put slot new_spill_value spills)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm different = assume_rule(`~((other:int) == (slot:int))`);
  thm reversed_different = not_intro(
      `(slot:int) == (other:int)`,
      contra(different, sym_rule(assume_rule(
        `(slot:int) == (other:int)`))));
  thm retained = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `slot:int`, `other:int`, `held_value:cm_value`,
      `spills:(cm_spill)list`), cm_spill_holds_remove_other),
      different), assume_rule(
        `cm_spill_holds (other:int) (held_value:cm_value)
          (spills:(cm_spill)list)`));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_spill_put_def, cm_spill_holds_def,
      cm_spill_slot_def, reversed_different)));
  ACCEPT_TAC(reduced, retained);
  return gnode_prove(root);
}

PROOF thm cm_spill_holds_put_other =
    cm_prove_spill_holds_put_other();

PROOF static thm cm_prove_staged_spills_put_above(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (values:(cm_value)list)
         (spills:(cm_spill)list) (slot:int)
         (new_spill_value:cm_value).
         cm_staged_spills base values spills ==>
         base + ilength values <= slot ==>
         cm_staged_spills base values
           (cm_spill_put slot new_spill_value spills)`);
  gnode with_base = GEN_TAC(root, "base");
  gnode_list cases =
      INDUCT_TAC(with_base, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_staged_spills_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm staged = conv_rule(rewrite_conv(THM_LIST(
        cm_staged_spills_def)), assume_rule(
          `cm_staged_spills (base:int)
            ((a0:cm_value) :: (a1:(cm_value)list))
            (spills:(cm_spill)list)`));
    thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
          `(base:int) +
             ilength ((a0:cm_value) :: (a1:(cm_value)list)) <=
           (slot:int)`));
    thm existing_less = mp_rule(int_arith_rule(
        `(base:int) + (1i + ilength (a1:(cm_value)list)) <=
             (slot:int) ==>
         base + ilength a1 < slot`), upper);
    thm different = mp_rule(int_arith_rule(
        `(base:int) + ilength (a1:(cm_value)list) < (slot:int) ==>
         ~(base + ilength a1 == slot)`), existing_less);
    thm retained = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `slot:int`, `new_spill_value:cm_value`,
        `(base:int) + ilength (a1:(cm_value)list)`,
        `a0:cm_value`, `spills:(cm_spill)list`),
        cm_spill_holds_put_other), different),
        conjunct1_rule(staged));
    thm tail_upper = mp_rule(int_arith_rule(
        `(base:int) + (1i + ilength (a1:(cm_value)list)) <=
             (slot:int) ==>
         base + ilength a1 <= slot`), upper);
    thm tail = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `spills:(cm_spill)list`, `slot:int`,
        `new_spill_value:cm_value`), assume_rule(
          `!(spills:(cm_spill)list) (slot:int)
             (new_spill_value:cm_value).
             cm_staged_spills (base:int) (a1:(cm_value)list) spills ==>
             base + ilength a1 <= slot ==>
             cm_staged_spills base a1
               (cm_spill_put slot new_spill_value spills)`)),
        conjunct2_rule(staged)), tail_upper);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_staged_spills_def)));
    ACCEPT_TAC(reduced, conj_rule(retained, tail));
  }
  return gnode_prove(root);
}

PROOF thm cm_staged_spills_put_above =
    cm_prove_staged_spills_put_above();

PROOF thm get_cm_staged_spills_put_above(void) {
  return cm_staged_spills_put_above;
}

PROOF static thm cm_prove_spill_holds_put_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(other:int) (limit:int) (slot:int)
         (new_spill_value:cm_value) (held_value:cm_value)
         (spills:(cm_spill)list).
         other < limit ==>
         limit <= slot ==>
         cm_spill_holds other held_value spills ==>
         cm_spill_holds other held_value
           (cm_spill_put slot new_spill_value spills)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm different = mp_rule(mp_rule(int_arith_rule(
      `(other:int) < (limit:int) ==>
       limit <= (slot:int) ==>
       ~(other == slot)`), assume_rule(
        `(other:int) < (limit:int)`)), assume_rule(
          `(limit:int) <= (slot:int)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `slot:int`, `new_spill_value:cm_value`, `other:int`,
      `held_value:cm_value`, `spills:(cm_spill)list`),
      cm_spill_holds_put_other), different), assume_rule(
        `cm_spill_holds (other:int) (held_value:cm_value)
          (spills:(cm_spill)list)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}

PROOF static thm cm_spill_holds_put_below =
    cm_prove_spill_holds_put_below();

PROOF static thm cm_prove_phase_spill_consistent_put_above(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (owner:int) (phase:cm_aphase)
         (spills:(cm_spill)list) (slot:int)
         (new_spill_value:cm_value).
         cm_phase_spill_consistent limit owner phase spills ==>
         limit <= slot ==>
         cm_phase_spill_consistent limit owner phase
           (cm_spill_put slot new_spill_value spills)`);
  gnode with_limit = GEN_TAC(root, "limit");
  gnode with_owner = GEN_TAC(with_limit, "owner");
  gnode_list cases = INDUCT_TAC(with_owner, `phase:cm_aphase`);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    if (index == 3 || index == 5 || index == 8 ||
        index == 21) {
      continue;
    }
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv,
        THM_LIST(cm_phase_spill_consistent_def));
    if (IS_NULL(reduced->solved)) {
      labeled_term_list assumptions = goal_lasmps(reduced->g);
      for (size_t fact_index = 0;
           fact_index < vector_size(assumptions); ++fact_index) {
        thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_phase_spill_consistent_def)),
            assume_rule(assumptions[fact_index].tm));
        if (alpha_compare(concl(normalized),
              goal_ccl(reduced->g)) == 0) {
          ACCEPT_TAC(reduced, normalized);
          break;
        }
      }
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)), assume_rule(
          `cm_phase_spill_consistent (limit:int) (owner:int)
            (CAAssignRP (a0:cm_value) (a1:cm_type))
            (spills:(cm_spill)list)`));
    thm retained = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `owner:int`, `limit:int`, `slot:int`,
        `new_spill_value:cm_value`, `a0:cm_value`,
        `spills:(cm_spill)list`), cm_spill_holds_put_below),
        conjunct1_rule(opened)), assume_rule(
          `(limit:int) <= (slot:int)`)), conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)));
    ACCEPT_TAC(reduced, conj_rule(conjunct1_rule(opened), retained));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[5]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)), assume_rule(
          `cm_phase_spill_consistent (limit:int) (owner:int)
            (CABinRP (a0:int) (a1:cm_expr) (a2:cm_expr)
              (a3:cm_value) (a4:cm_type))
            (spills:(cm_spill)list)`));
    term short_term = `(a0:int) == 0i || a0 == 1i`;
    term updated_saved_term =
        `(owner:int) < (limit:int) &&
         cm_spill_holds owner (a3:cm_value)
           (cm_spill_put (slot:int) (new_spill_value:cm_value)
             (spills:(cm_spill)list))`;
    thm short_case = disj1_rule(assume_rule(short_term),
        updated_saved_term);
    thm saved = assume_rule(
        `(owner:int) < (limit:int) &&
         cm_spill_holds owner (a3:cm_value)
           (spills:(cm_spill)list)`);
    thm retained = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `owner:int`, `limit:int`, `slot:int`,
        `new_spill_value:cm_value`, `a3:cm_value`,
        `spills:(cm_spill)list`), cm_spill_holds_put_below),
        conjunct1_rule(saved)), assume_rule(
          `(limit:int) <= (slot:int)`)), conjunct2_rule(saved));
    thm saved_case = disj2_rule(short_term,
        conj_rule(conjunct1_rule(saved), retained));
    thm alternatives = disj_cases_rule(conjunct2_rule(opened),
        short_case, saved_case);
    thm result = conj_rule(conjunct1_rule(opened), alternatives);
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_phase_spill_consistent_def)));
    ACCEPT_TAC(reduced, result);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[8]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)), assume_rule(
          `cm_phase_spill_consistent (limit:int) (owner:int)
            (CAIndexRP (a0:cm_value) (a1:cm_type))
            (spills:(cm_spill)list)`));
    thm retained = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `owner:int`, `limit:int`, `slot:int`,
        `new_spill_value:cm_value`, `a0:cm_value`,
        `spills:(cm_spill)list`), cm_spill_holds_put_below),
        conjunct1_rule(opened)), assume_rule(
          `(limit:int) <= (slot:int)`)), conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)));
    ACCEPT_TAC(reduced, conj_rule(conjunct1_rule(opened), retained));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[21]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)), assume_rule(
          `cm_phase_spill_consistent (limit:int) (owner:int)
            (CAArgP (a0:int) (a1:(cm_expr)list)
              (a2:(cm_value)list) (a3:cm_type)
              (a4:(cm_expr)list) (a5:int) (a6:int) (a7:int))
            (spills:(cm_spill)list)`));
    thm owner_bound = conjunct1_rule(opened);
    thm after_owner = conjunct2_rule(opened);
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
    thm staged_upper = mp_rule(mp_rule(int_arith_rule(
        `(a6:int) == (a5:int) + ilength (a2:(cm_value)list) ==>
         a6 <= (limit:int) ==>
         limit <= (slot:int) ==>
         a5 + ilength a2 <= slot`), current_equal),
        current_bound);
    staged_upper = mp_rule(staged_upper, assume_rule(
        `(limit:int) <= (slot:int)`));
    thm retained = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `a5:int`, `a2:(cm_value)list`, `spills:(cm_spill)list`,
        `slot:int`, `new_spill_value:cm_value`),
        cm_staged_spills_put_above), staged), staged_upper);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)));
    ACCEPT_TAC(reduced, conj_rule(owner_bound,
        conj_rule(base_equal, conj_rule(current_equal,
          conj_rule(scratch_equal, conj_rule(length_equal,
            conj_rule(current_bound, retained)))))));
  }
  return gnode_prove(root);
}

PROOF thm cm_phase_spill_consistent_put_above =
    cm_prove_phase_spill_consistent_put_above();

PROOF static thm cm_prove_phase_spill_consistent_owner_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase) (limit:int) (owner:int)
         (spills:(cm_spill)list).
         ~cm_phase_is_call phase ==>
         cm_phase_spill_consistent limit owner phase spills ==>
         owner <= limit`);
  gnode_list cases = INDUCT_TAC(root, `phase:cm_aphase`);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    if (index == 3 || index == 8 || index == 22) {
      continue;
    }
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv,
        THM_LIST(cm_phase_is_call_def,
          cm_phase_spill_consistent_def));
    if (IS_NULL(reduced->solved)) {
      labeled_term_list assumptions = goal_lasmps(reduced->g);
      for (size_t fact_index = 0;
           fact_index < vector_size(assumptions); ++fact_index) {
        if (!cm_spill_semantic_has_head_const(
              assumptions[fact_index].tm,
              "cm_phase_spill_consistent")) {
          continue;
        }
        thm expanded = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_phase_is_call_def,
            cm_phase_spill_consistent_def)),
            assume_rule(assumptions[fact_index].tm));
        ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
            concl(expanded), goal_ccl(reduced->g))), expanded));
        break;
      }
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)), assume_rule(
          `cm_phase_spill_consistent (limit:int) (owner:int)
            (CAAssignRP (a0:cm_value) (a1:cm_type))
            (spills:(cm_spill)list)`));
    ACCEPT_TAC(leaf, mp_rule(int_arith_rule(
        `(owner:int) < (limit:int) ==> owner <= limit`),
        conjunct1_rule(opened)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[8]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def)), assume_rule(
          `cm_phase_spill_consistent (limit:int) (owner:int)
            (CAIndexRP (a0:cm_value) (a1:cm_type))
            (spills:(cm_spill)list)`));
    ACCEPT_TAC(leaf, mp_rule(int_arith_rule(
        `(owner:int) < (limit:int) ==> owner <= limit`),
        conjunct1_rule(opened)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[22]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_phase_is_call_def)), assume_rule(
          `~cm_phase_is_call
            (CACallP (a0:int) (a1:int->int->cm_value)
              (a2:int) (a3:(cm_region)list) (a4:cm_type))`));
    CONTR_TAC(leaf, impossible);
  }
  return gnode_prove(root);
}

PROOF static thm cm_phase_spill_consistent_owner_bound =
    cm_prove_phase_spill_consistent_owner_bound();

PROOF static thm cm_prove_cursors_spill_consistent_put_above(void) {
  gnode root = gnode_new_with_ccl(
      `!(cursors:(cm_acursor)list) (limit:int)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (slot:int) (new_spill_value:cm_value).
         cm_cursors_spill_consistent limit cursors spills saved ==>
         limit <= slot ==>
         cm_cursors_spill_consistent limit cursors
           (cm_spill_put slot new_spill_value spills) saved`);
  gnode_list cases =
      INDUCT_TAC(root, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_cursors_spill_consistent_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_cursors_spill_consistent_def)), assume_rule(
          `cm_cursors_spill_consistent (limit:int)
            ((a0:cm_acursor) :: (a1:(cm_acursor)list))
            (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)`));
    thm phase_consistent = conjunct1_rule(opened);
    thm phase_updated = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `limit:int`, `cm_cursor_temp (a0:cm_acursor)`,
        `cm_cursor_phase (a0:cm_acursor)`,
        `spills:(cm_spill)list`, `slot:int`,
        `new_spill_value:cm_value`),
        cm_phase_spill_consistent_put_above),
        phase_consistent), assume_rule(
          `(limit:int) <= (slot:int)`));
    term updated_conditional =
        `if cm_phase_is_call (cm_cursor_phase (a0:cm_acursor))
         then ~((saved:(cm_spill_frame)list) == []) &&
              cm_cursors_spill_consistent
                (cm_cursor_temp a0) (a1:(cm_acursor)list)
                (cm_spill_frame_spills (HD saved)) (TL saved)
         else cm_cursors_spill_consistent
                (cm_cursor_temp a0) a1
                (cm_spill_put (slot:int)
                  (new_spill_value:cm_value)
                  (spills:(cm_spill)list)) saved`;
    term call_term =
        `cm_phase_is_call (cm_cursor_phase (a0:cm_acursor))`;
    thm call_fact = assume_rule(call_term);
    thm call_tail = conv_rule(reduce_rewrite_conv(THM_LIST(
        call_fact)), conjunct2_rule(opened));
    thm call_conditional_equal = apply_conversion(
        reduce_rewrite_conv(THM_LIST(call_fact)),
        updated_conditional);
    thm call_conditional =
        eq_mp_rule(sym_rule(call_conditional_equal), call_tail);
    thm call_result = conj_rule(phase_updated, call_conditional);
    thm not_call = assume_rule(mk_not(call_term));
    thm tail = conv_rule(reduce_rewrite_conv(THM_LIST(
        not_call)), conjunct2_rule(opened));
    thm owner_bound = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `cm_cursor_phase (a0:cm_acursor)`, `limit:int`,
        `cm_cursor_temp (a0:cm_acursor)`,
        `spills:(cm_spill)list`),
        cm_phase_spill_consistent_owner_bound),
        not_call), phase_consistent);
    thm owner_upper = mp_rule(mp_rule(int_arith_rule(
        `cm_cursor_temp (a0:cm_acursor) <= (limit:int) ==>
         limit <= (slot:int) ==>
         cm_cursor_temp a0 <= slot`), owner_bound),
        assume_rule(`(limit:int) <= (slot:int)`));
    labeled_term_list induction_assumptions = goal_lasmps(leaf->g);
    thm ih_at_owner = spec_rule(
        `cm_cursor_temp (a0:cm_acursor)`,
        assume_rule(induction_assumptions[0].tm));
    thm tail_updated = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`, `slot:int`,
        `new_spill_value:cm_value`), ih_at_owner),
        tail), owner_upper);
    thm noncall_conditional_equal = apply_conversion(
        reduce_rewrite_conv(THM_LIST(not_call)),
        updated_conditional);
    thm noncall_conditional = eq_mp_rule(
        sym_rule(noncall_conditional_equal), tail_updated);
    thm noncall_result =
        conj_rule(phase_updated, noncall_conditional);
    thm result = disj_cases_rule(spec_rule(
        call_term, get_theorem_by_name("EXCLUDED_MIDDLE")),
        call_result, noncall_result);
    term target =
        `cm_cursors_spill_consistent (limit:int)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (cm_spill_put (slot:int) (new_spill_value:cm_value)
            (spills:(cm_spill)list))
          (saved:(cm_spill_frame)list)`;
    thm target_view = apply_conversion(
        rewrite_conv(THM_LIST(cm_cursors_spill_consistent_def)),
        target);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}

PROOF thm cm_cursors_spill_consistent_put_above =
    cm_prove_cursors_spill_consistent_put_above();

PROOF thm get_cm_cursors_spill_consistent_put_above(void) {
  return cm_cursors_spill_consistent_put_above;
}

PROOF static thm cm_prove_annotation_spill_consistent_initial(void) {
  gnode root = gnode_new_with_ccl(
      `cm_annotation_spill_consistent cm_initial_annotation`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_initial_annotation_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursors_spill_consistent_def)));
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_consistent_initial =
    cm_prove_annotation_spill_consistent_initial();
PROOF static int cmc_preservation_spill_semantic_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_spill_semantic_axioms_before,
      "cmc_preservation_spill_semantic introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_spill_semantic_checks =
    cmc_preservation_spill_semantic_final_checks();
