#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_syntax.h"

#require "cmc_preservation_generation_annotation.c"

PROOF static size_t _cmc_preservation_generation_syntax_axioms_before =
    vector_size(get_all_axioms());

PROOF static conv cm_generation_syntax_normalize(thm_list rules) {
  conv pass = reduce_rewrite_conv(rules);
  conv result = pass;
  for (size_t i = 0; i < 5; ++i) {
    result = then_conv(result, pass);
  }
  return result;
}
PROOF static bool cm_gs_has_conjunct(
    const term tree, const term wanted) {
  if (alpha_compare(tree, wanted) == 0) {
    return true;
  }
  if (!is_conj(tree)) {
    return false;
  }
  struct dest_conj_results parts = dest_conj(tree);
  return cm_gs_has_conjunct(parts.tm1, wanted) ||
         cm_gs_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_gs_pick_conjunct(
    const thm fact, const term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) {
    return fact;
  }
  struct dest_conj_results parts = dest_conj(concl(fact));
  return cm_gs_has_conjunct(parts.tm1, wanted)
      ? cm_gs_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_gs_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_gs_taut_from_assumptions(const gnode node) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  term_list premises = vector_create();
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    vector_add(&premises, assumptions[i].tm);
  }
  thm result = taut_rule(imp_chain(premises, goal_ccl(node->g)));
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    result = mp_rule(result, assume_rule(assumptions[i].tm));
  }
  return result;
}
PROOF static thm cm_gs_expr_ih(
    const thm packed, const term child, const thm child_wf) {
  term wanted =
      `!(p0:cm_program) (f0:cm_function_d).
         cm_expr_wf p0 f0 ${child:cm_expr} ==>
         cm_expr_static_valid p0 f0 ${child:cm_expr}`;
  thm ih = cm_gs_pick_conjunct(packed, wanted);
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`), ih), child_wf);
}

PROOF static thm cm_gs_args_ih(
    const thm packed, const term child, const term slots,
    const thm args_wf) {
  term wanted =
      `!(p0:cm_program) (f0:cm_function_d)
         (slots0:(cm_slot_d)list).
         cm_args_wf p0 f0 ${child:(cm_expr)list} slots0 ==>
         cm_args_static_valid p0 f0 ${child:(cm_expr)list}`;
  thm ih = cm_gs_pick_conjunct(packed, wanted);
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, slots), ih), args_wf);
}



PROOF static thm cm_prove_expr_and_args_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `((!(expr:cm_expr) (p:cm_program) (f:cm_function_d).
           cm_expr_wf p f expr ==>
           cm_expr_static_valid p f expr) &&
        (!(args:(cm_expr)list) (p:cm_program) (f:cm_function_d)
           (slots:(cm_slot_d)list).
           cm_args_wf p f args slots ==>
           cm_args_static_valid p f args))`);
  gnode matched = MATCH_MP_TAC(root, get_cm_expr_induction());
  gnode cursor = CONV_TAC(
      matched, reduce_rewrite_conv(THM_LIST()));
  gnode cases[16];
  for (size_t i = 0; i < 15; ++i) {
    gnode_list split = CONJ_TAC(cursor);
    cases[i] = split[0];
    cursor = split[1];
  }
  cases[15] = cursor;
  term_list expressions = TERM_LIST(
      `CMConstE (a0:int) (a1:cm_type):cm_expr`,
      `CMStringE (a0:int) (a1:cm_type):cm_expr`,
      `CMVarE (a0:int) (a1:int) (a2:cm_type):cm_expr`,
      `CMAssignE (a0:cm_expr) (a1:cm_expr) (a2:cm_type):cm_expr`,
      `CMBinaryE (a0:int) (a1:cm_expr) (a2:cm_expr)
        (a3:cm_type):cm_expr`,
      `CMUnaryE (a0:int) (a1:cm_expr) (a2:cm_type):cm_expr`,
      `CMIndexE (a0:cm_expr) (a1:cm_expr) (a2:cm_type):cm_expr`,
      `CMMemberE (a0:cm_expr) (a1:int) (a2:cm_type):cm_expr`,
      `CMCallE (a0:int) (a1:(cm_expr)list) (a2:cm_type):cm_expr`,
      `CMSizeofE (a0:cm_type) (a1:cm_type):cm_expr`,
      `CMGetcE (a0:cm_type):cm_expr`,
      `CMPutcE (a0:cm_expr) (a1:cm_type):cm_expr`,
      `CMPutiE (a0:cm_expr) (a1:cm_type):cm_expr`,
      `CMExitE (a0:cm_expr) (a1:cm_type):cm_expr`);
  for (size_t i = 0; i < 16; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    labeled_term_list induction_facts = goal_lasmps(leaf->g);
    if (i == 0 || i == 9 || i == 10 || i == 14) {
      CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
          cm_expr_static_valid_def, cm_args_static_valid_def)));
      continue;
    }
    if (i == 15) {
      thm opened = conv_rule(rewrite_conv(THM_LIST(
          get_cm_expr_wf_def())), assume_rule(
            `cm_args_wf (p:cm_program) (f:cm_function_d)
              ((a0:cm_expr) :: (a1:(cm_expr)list))
              (slots:(cm_slot_d)list)`));
      thm head_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a0:cm_expr)`);
      thm tail_wf = cm_gs_pick_conjunct(opened,
          `cm_args_wf (p:cm_program) (f:cm_function_d)
            (a1:(cm_expr)list) (TL (slots:(cm_slot_d)list))`);
      thm packed = assume_rule(induction_facts[0].tm);
      thm body = conj_rule(
          cm_gs_expr_ih(packed, `a0:cm_expr`, head_wf),
          cm_gs_args_ih(packed, `a1:(cm_expr)list`,
            `TL (slots:(cm_slot_d)list)`, tail_wf));
      thm target_view = apply_conversion(
          rewrite_conv(THM_LIST(cm_args_static_valid_def)),
          goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
      continue;
    }
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_wf_def())), assume_rule(
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            ${expressions[i]:cm_expr}`));
    thm body = empty_theorem;
    if (i == 1) {
      term bounds =
          `0i <= (a0:int) &&
           a0 < ilength (cm_program_strings (p:cm_program))`;
      body = mp_rule(taut_rule(mk_imp(concl(opened), bounds)), opened);
    } else if (i == 2) {
      body = cm_gs_pick_conjunct(opened,
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
            (a0:int) (a1:int)`);
    } else if (i == 3) {
      thm left_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a0:cm_expr)`);
      thm right_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a1:cm_expr)`);
      thm packed = assume_rule(induction_facts[0].tm);
      body = conj_rule(
          cm_gs_expr_ih(packed, `a0:cm_expr`, left_wf),
          cm_gs_expr_ih(packed, `a1:cm_expr`, right_wf));
    } else if (i == 4) {
      thm left_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a1:cm_expr)`);
      thm right_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a2:cm_expr)`);
      thm packed = assume_rule(induction_facts[0].tm);
      body = conj_rule(
          cm_gs_expr_ih(packed, `a1:cm_expr`, left_wf),
          cm_gs_expr_ih(packed, `a2:cm_expr`, right_wf));
    } else if (i == 5) {
      thm child_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a1:cm_expr)`);
      body = cm_gs_expr_ih(
          assume_rule(induction_facts[0].tm), `a1:cm_expr`, child_wf);
    } else if (i == 6) {
      thm left_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a0:cm_expr)`);
      thm right_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a1:cm_expr)`);
      thm packed = assume_rule(induction_facts[0].tm);
      body = conj_rule(
          cm_gs_expr_ih(packed, `a0:cm_expr`, left_wf),
          cm_gs_expr_ih(packed, `a1:cm_expr`, right_wf));
    } else if (i == 7 || i == 11 || i == 12 || i == 13) {
      thm child_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a0:cm_expr)`);
      body = cm_gs_expr_ih(
          assume_rule(induction_facts[0].tm), `a0:cm_expr`, child_wf);
    } else {
      term params =
          `cm_function_params
            (inth (a0:int) (cm_program_functions (p:cm_program)))`;
      thm args_wf = cm_gs_pick_conjunct(opened,
          `cm_args_wf (p:cm_program) (f:cm_function_d)
            (a1:(cm_expr)list) ${params:(cm_slot_d)list}`);
      term bounds =
          `0i <= (a0:int) &&
           a0 < ilength (cm_program_functions (p:cm_program))`;
      thm bounded = mp_rule(
          taut_rule(mk_imp(concl(opened), bounds)), opened);
      thm args_static = cm_gs_args_ih(
          assume_rule(induction_facts[0].tm),
          `a1:(cm_expr)list`, params, args_wf);
      body = conj_rule(conjunct1_rule(bounded),
          conj_rule(conjunct2_rule(bounded), args_static));
    }
    thm target_view = apply_conversion(
        rewrite_conv(THM_LIST(cm_expr_static_valid_def)),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  }
  return gnode_prove(root);
}
PROOF static thm cm_expr_and_args_static_valid =
    cm_prove_expr_and_args_static_valid();
PROOF thm cm_expr_wf_static_valid =
    conjunct1_rule(cm_expr_and_args_static_valid);
PROOF thm cm_args_wf_static_valid =
    conjunct2_rule(cm_expr_and_args_static_valid);

PROOF static thm cm_gs_stmt_ih(
    const thm packed, const term child, const term child_loop,
    const thm child_wf) {
  term wanted =
      `!(p0:cm_program) (f0:cm_function_d) (loop0:bool).
         cm_stmt_wf p0 f0 loop0 ${child:cm_stmt} ==>
         cm_stmt_static_valid p0 f0 ${child:cm_stmt}`;
  thm ih = cm_gs_pick_conjunct(packed, wanted);
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, child_loop), ih), child_wf);
}

PROOF static thm cm_prove_stmt_wf_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt) (p:cm_program) (f:cm_function_d)
         (loop:bool).
         cm_stmt_wf p f loop stmt ==>
         cm_stmt_static_valid p f stmt`);
  gnode matched = MATCH_MP_TAC(root, get_cm_stmt_induction());
  gnode cursor = CONV_TAC(
      matched, reduce_rewrite_conv(THM_LIST()));
  gnode cases[11];
  for (size_t i = 0; i < 10; ++i) {
    gnode_list split = CONJ_TAC(cursor);
    cases[i] = split[0];
    cursor = split[1];
  }
  cases[10] = cursor;
  term_list statements = TERM_LIST(
      `CMSkipS:cm_stmt`,
      `CMExprS (a:cm_expr):cm_stmt`,
      `CMDeclS (a:int):cm_stmt`,
      `CMInitS (a0:int) (a1:cm_expr):cm_stmt`,
      `CMSeqS (a0:cm_stmt) (a1:cm_stmt):cm_stmt`,
      `CMBlockS (a:cm_stmt):cm_stmt`,
      `CMIfS (a0:cm_expr) (a1:cm_stmt) (a2:cm_stmt):cm_stmt`,
      `CMWhileS (a0:cm_expr) (a1:cm_stmt):cm_stmt`,
      `CMBreakS:cm_stmt`,
      `CMContinueS:cm_stmt`,
      `CMReturnS (a:cm_expr):cm_stmt`);
  for (size_t i = 0; i < 11; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    labeled_term_list induction_facts = goal_lasmps(leaf->g);
    if (i == 0 || i == 2 || i == 8 || i == 9) {
      CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
          cm_stmt_static_valid_def)));
      continue;
    }
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_wf_def())), assume_rule(
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            (loop:bool) ${statements[i]:cm_stmt}`));
    thm body = empty_theorem;
    if (i == 1) {
      thm expr_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a:cm_expr)`);
      body = mp_rule(specl_rule(TERM_LIST(
          `a:cm_expr`, `p:cm_program`, `f:cm_function_d`),
          cm_expr_wf_static_valid), expr_wf);
    } else if (i == 3) {
      thm expr_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a1:cm_expr)`);
      body = mp_rule(specl_rule(TERM_LIST(
          `a1:cm_expr`, `p:cm_program`, `f:cm_function_d`),
          cm_expr_wf_static_valid), expr_wf);
    } else if (i == 4) {
      thm first_wf = cm_gs_pick_conjunct(opened,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            (loop:bool) (a0:cm_stmt)`);
      thm second_wf = cm_gs_pick_conjunct(opened,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            (loop:bool) (a1:cm_stmt)`);
      thm packed = assume_rule(induction_facts[0].tm);
      body = conj_rule(
          cm_gs_stmt_ih(packed, `a0:cm_stmt`, `loop:bool`, first_wf),
          cm_gs_stmt_ih(packed, `a1:cm_stmt`, `loop:bool`, second_wf));
    } else if (i == 5) {
      thm child_wf = cm_gs_pick_conjunct(opened,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            (loop:bool) (a:cm_stmt)`);
      body = cm_gs_stmt_ih(
          assume_rule(induction_facts[0].tm),
          `a:cm_stmt`, `loop:bool`, child_wf);
    } else if (i == 6) {
      thm guard_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a0:cm_expr)`);
      thm yes_wf = cm_gs_pick_conjunct(opened,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            (loop:bool) (a1:cm_stmt)`);
      thm no_wf = cm_gs_pick_conjunct(opened,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            (loop:bool) (a2:cm_stmt)`);
      thm guard_static = mp_rule(specl_rule(TERM_LIST(
          `a0:cm_expr`, `p:cm_program`, `f:cm_function_d`),
          cm_expr_wf_static_valid), guard_wf);
      thm packed = assume_rule(induction_facts[0].tm);
      body = conj_rule(guard_static, conj_rule(
          cm_gs_stmt_ih(packed, `a1:cm_stmt`, `loop:bool`, yes_wf),
          cm_gs_stmt_ih(packed, `a2:cm_stmt`, `loop:bool`, no_wf)));
    } else if (i == 7) {
      thm guard_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a0:cm_expr)`);
      thm child_wf = cm_gs_pick_conjunct(opened,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
            T (a1:cm_stmt)`);
      thm guard_static = mp_rule(specl_rule(TERM_LIST(
          `a0:cm_expr`, `p:cm_program`, `f:cm_function_d`),
          cm_expr_wf_static_valid), guard_wf);
      body = conj_rule(guard_static,
          cm_gs_stmt_ih(assume_rule(induction_facts[0].tm),
            `a1:cm_stmt`, `T`, child_wf));
    } else {
      thm expr_wf = cm_gs_pick_conjunct(opened,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (a:cm_expr)`);
      body = mp_rule(specl_rule(TERM_LIST(
          `a:cm_expr`, `p:cm_program`, `f:cm_function_d`),
          cm_expr_wf_static_valid), expr_wf);
    }
    thm target_view = apply_conversion(
        rewrite_conv(THM_LIST(cm_stmt_static_valid_def)),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  }
  return gnode_prove(root);
}
PROOF thm cm_stmt_wf_static_valid =
    cm_prove_stmt_wf_static_valid();

PROOF static thm cm_prove_function_body_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d).
         cm_function_wf p f ==>
         cm_stmt_static_valid p f (cm_function_body f)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program) (f:cm_function_d)`));
  thm stmt_wf = cm_gs_pick_conjunct(opened,
      `cm_stmt_wf (p:cm_program) (f:cm_function_d) F
        (cm_function_body f)`);
  ACCEPT_TAC(leaf, mp_rule(specl_rule(TERM_LIST(
      `cm_function_body (f:cm_function_d)`, `p:cm_program`,
      `f:cm_function_d`, `F`), cm_stmt_wf_static_valid), stmt_wf));
  return gnode_prove(root);
}
PROOF thm cm_function_body_static_valid =
    cm_prove_function_body_static_valid();

PROOF static thm cm_prove_typed_function_body_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_stmt_static_valid p
           (inth fid (cm_program_functions p))
           (cm_function_body
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), assume_rule(
        `cm_typed_program (p:cm_program)`));
  thm all_functions = cm_gs_pick_conjunct(typed,
      `!i. 0i <= i ==>
         i < ilength (cm_program_functions (p:cm_program)) ==>
         cm_function_wf p
           (inth i (cm_program_functions p))`);
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, all_functions), assume_rule(
        `0i <= (fid:int)`)), assume_rule(
        `(fid:int) < ilength (cm_program_functions (p:cm_program))`));
  ACCEPT_TAC(leaf, mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`),
      cm_function_body_static_valid), function_wf));
  return gnode_prove(root);
}
PROOF thm cm_typed_function_body_static_valid =
    cm_prove_typed_function_body_static_valid();

PROOF static int cmc_preservation_generation_syntax_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_syntax_axioms_before,
      "cmc_preservation_generation_syntax introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_typed_function_body_static_valid)) == 0,
      "typed function body static-valid theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_generation_syntax_checks =
    cmc_preservation_generation_syntax_final_checks();
