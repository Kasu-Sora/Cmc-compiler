#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_stack_local_core.h"
#require "cmc_stack_local_core.c"
#include "cmc_stack_local_syntax.h"

PROOF static size_t _cmc_stack_local_syntax_axioms_before = vector_size(get_all_axioms());

PROOF static thm cm_prove_binding_heights_start(void) {
  gnode root = gnode_new_with_ccl(
      `!(scope:int) (suffix:(int)list).
         cm_local_next
           (cm_binding_address_heights scope ++ suffix) 0i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(scope:int) == 0i`, "hglobal");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i],
        reduce_rewrite_conv, THM_LIST(
          cm_binding_address_heights_def,
          cm_local_next_def,
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"),
          get_theorem_by_name("TL")));
  }
  return gnode_prove(root);
}
PROOF static gnode cm_assume_conjunct_leaves(
    gnode branch, const thm fact, size_t *counter) {
  if (is_conj(concl(fact))) {
    branch = cm_assume_conjunct_leaves(
        branch, conjunct1_rule(fact), counter);
    return cm_assume_conjunct_leaves(
        branch, conjunct2_rule(fact), counter);
  }
  return ASSUME_TAC(branch, fact,
      gc_sprintf("hwfpart%zu", (*counter)++));
}

PROOF thm cm_binding_heights_start =
    cm_prove_binding_heights_start();
PROOF static thm cm_prove_binding_heights_start_nested(void) {
  thm base = ispecl_rule(TERM_LIST(
      `scope:int`,
      `(middle:(int)list) ++ (suffix:(int)list)`),
      cm_binding_heights_start);
  thm assoc = ispecl_rule(TERM_LIST(
      `cm_binding_address_heights (scope:int)`,
      `middle:(int)list`, `suffix:(int)list`),
      get_theorem_by_name("APPEND_ASSOC"));
  thm moved = eq_mp_rule(beta_norm(ap_term_rule(
      `\xs:(int)list. cm_local_next xs 0i`, assoc)), base);
  return genl_rule(TERM_LIST(
      `scope:int`, `middle:(int)list`, `suffix:(int)list`),
      moved);
}
PROOF thm cm_binding_heights_start_nested =
    cm_prove_binding_heights_start_nested();


PROOF static thm cm_prove_codegen_height_starts(void) {
  gnode root = gnode_new_with_ccl(
      `((!(expr:cm_expr).
           (!(p:cm_program) (f:cm_function_d) fid
               (annotations:(int)list).
              cm_expr_wf p f expr ==>
              cm_local_next annotations 1i ==>
              cm_local_next
                (cm_rvalue_heights p fid expr ++ annotations) 0i) &&
           (!(p:cm_program) (f:cm_function_d) fid
               (annotations:(int)list).
              cm_expr_wf p f expr ==>
              cm_lvalue expr ==>
              cm_local_next annotations 1i ==>
              cm_local_next
                (cm_lvalue_heights p fid expr ++ annotations) 0i)) &&
        (!(args:(cm_expr)list).
           !(p:cm_program) (f:cm_function_d)
             (slots:(cm_slot_d)list) fid
             (annotations:(int)list).
           cm_args_wf p f args slots ==>
           cm_local_next annotations 0i ==>
           cm_local_next
             (cm_args_store_heights p fid args ++ annotations) 0i))`);
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
  for (size_t i = 0; i < 16; ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode_list opened = AUTO_ASMP_DESTRUCT_TAC(constructor);
    gnode leaf = opened[0];
    gnode_list obligations;
    if (i < 14) {
      obligations = CONJ_TAC(leaf);
    } else {
      obligations = gnode_list_from_array(1, &leaf);
    }
    for (size_t j = 0; j < vector_size(obligations); ++j) {
      gnode quantified = AUTO_INTROS_TAC(obligations[j]);
      gnode_list destructed =
          AUTO_ASMP_DESTRUCT_TAC(quantified);
      gnode branch = destructed[0];
      thm wf;
      thm parts;
      if (i < 14) {
        wf = cm_predicate_assumption(branch, "cm_expr_wf");
        parts = conv_rule(
            reduce_rewrite_conv(THM_LIST(
              get_cm_expr_wf_def())), wf);
      } else {
        wf = cm_predicate_assumption(branch, "cm_args_wf");
        parts = conv_rule(
            reduce_rewrite_conv(THM_LIST(
              get_cm_args_wf_def())), wf);
      }
      size_t wf_part = 0;
      branch = cm_assume_conjunct_leaves(
          branch, parts, &wf_part);
      bool false_lvalue =
          j == 1 &&
          (i == 0 || i == 1 || i == 3 || i == 4 ||
           i == 8 || i == 9 || i == 10 || i == 11 ||
           i == 12 || i == 13);
      if (false_lvalue) {
        thm lvalue = cm_predicate_assumption(
            branch, "cm_lvalue");
        thm impossible = conv_rule(
            reduce_rewrite_conv(THM_LIST(
              get_cm_lvalue_def())), lvalue);
        CONTR_TAC(branch, impossible);
        continue;
      }
      if (i == 2) {
        gnode shaped = CONV_WITH_ASMP_TAC(
            branch, reduce_rewrite_conv, THM_LIST(
              get_cm_expr_wf_def(), get_cm_lvalue_def(),
              cm_expr_heights_def,
              cm_lvalue_heights_def, cm_rvalue_heights_def,
              cm_lheights_of_def, cm_rheights_of_def));
        thm start;
        if (j == 0) {
          start = ispecl_rule(TERM_LIST(
              `a0:int`,
              `if cm_binding_array (p:cm_program) fid a0 a1
               then ([]:(int)list) else [1i]`,
              `annotations:(int)list`),
              cm_binding_heights_start_nested);
        } else {
          start = ispecl_rule(TERM_LIST(
              `a0:int`, `annotations:(int)list`),
              cm_binding_heights_start);
        }
        ACCEPT_TAC(shaped, start);
        continue;
      }
      if (i == 3) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              cm_rvalue_heights_def,
              cm_rheights_of_def)));
        term suffix =
            `cm_temp_access_heights 1i ++
             cm_rheights_of
               (cm_expr_heights (p:cm_program) fid (a1:cm_expr)) ++
             cm_normalize_heights (a2:cm_type) 1i ++
             cm_temp_access_heights 1i ++ [2i] ++
             cm_temp_access_heights 0i ++ [1i] ++
             (annotations:(int)list)`;
        thm boundary = cm_fixed_local_next(
            suffix, `1i`, THM_LIST());
        thm start = cm_expr_start_ih(
            branch, `a0:cm_expr`, true, suffix, boundary);
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))));
        ACCEPT_TAC(normalized, conv_rule(
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))), start));
        continue;
      }
      if (i == 4) {
        term is_zero = `(a0:int) == 0i`;
        term is_one = `(a0:int) == 1i`;
        gnode_list zero_cases =
            BOOL_CASES_TAC(branch, is_zero, "hopzero");
        gnode_list one_cases =
            BOOL_CASES_TAC(zero_cases[1], is_one, "hopone");
        gnode binary_cases[3] = {
          zero_cases[0], one_cases[0], one_cases[1]
        };
        for (size_t k = 0; k < 3; ++k) {
          thm_list decisions = THM_LIST();
          if (k == 0) {
            vector_add(&decisions,
                eqt_intro_rule(cm_matching_assumption(
                  binary_cases[k], is_zero)));
          } else {
            vector_add(&decisions,
                eqf_intro_rule(cm_matching_assumption(
                  binary_cases[k], mk_not(is_zero))));
            if (k == 1) {
              vector_add(&decisions,
                  eqt_intro_rule(cm_matching_assumption(
                    binary_cases[k], is_one)));
            } else {
              vector_add(&decisions,
                  eqf_intro_rule(cm_matching_assumption(
                    binary_cases[k], mk_not(is_one))));
            }
          }
          vector_add(&decisions, cm_expr_heights_def);
          vector_add(&decisions, cm_rvalue_heights_def);
          vector_add(&decisions, cm_rheights_of_def);
          gnode shaped = CONV_TAC(binary_cases[k],
              reduce_rewrite_conv(decisions));
          term suffix;
          if (k < 2) {
            suffix =
                `[1i] ++
                 cm_rheights_of
                   (cm_expr_heights (p:cm_program) fid
                     (a2:cm_expr)) ++
                 [1i; 2i; 1i; 0i] ++
                 (annotations:(int)list)`;
          } else {
            suffix =
                `cm_temp_access_heights 1i ++
                 cm_rheights_of
                   (cm_expr_heights (p:cm_program) fid
                     (a2:cm_expr)) ++
                 cm_binary_finish_heights p a0 a1 a2 ++
                 (annotations:(int)list)`;
          }
          thm boundary = cm_fixed_local_next(
              suffix, `1i`, THM_LIST());
          thm start = cm_expr_start_ih(
              binary_cases[k], `a1:cm_expr`, false,
              suffix, boundary);
          gnode normalized = CONV_TAC(shaped,
              rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND_ASSOC"))));
          ACCEPT_TAC(normalized, conv_rule(
              rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND_ASSOC"))), start));
        }
        continue;
      }
      if (i == 5) {
        term is_two = `(a0:int) == 2i`;
        term is_three = `(a0:int) == 3i`;
        if (j == 1) {
          thm current_lvalue = cm_matching_assumption(branch,
              `cm_lvalue
                 (CMUnaryE (a0:int) (a1:cm_expr)
                   (a2:cm_type))`);
          thm op_two = conv_rule(
              reduce_rewrite_conv(THM_LIST(
                get_cm_lvalue_def())), current_lvalue);
          thm decision = eqt_intro_rule(op_two);
          gnode shaped = CONV_TAC(branch,
              reduce_rewrite_conv(THM_LIST(
                decision, cm_expr_heights_def,
                cm_lvalue_heights_def,
                cm_lheights_of_def)));
          thm boundary = cm_matching_assumption(branch,
              `cm_local_next
                 (annotations:(int)list) 1i`);
          thm start = cm_expr_start_ih(
              branch, `a1:cm_expr`, false,
              `annotations:(int)list`, boundary);
          ACCEPT_TAC(shaped, start);
        } else {
          gnode_list two_cases =
              BOOL_CASES_TAC(branch, is_two, "hunarytwo");
          gnode_list three_cases =
              BOOL_CASES_TAC(two_cases[1], is_three,
                  "hunarythree");
          gnode unary_cases[3] = {
            two_cases[0], three_cases[0], three_cases[1]
          };
          for (size_t k = 0; k < 3; ++k) {
            gnode unary_branch = unary_cases[k];
            thm_list decisions = THM_LIST();
            if (k == 0) {
              vector_add(&decisions,
                  eqt_intro_rule(cm_matching_assumption(
                    unary_branch, is_two)));
            } else {
              vector_add(&decisions,
                  eqf_intro_rule(cm_matching_assumption(
                    unary_branch, mk_not(is_two))));
              if (k == 1) {
                thm op_three = cm_matching_assumption(
                    unary_branch, is_three);
                vector_add(&decisions,
                    eqt_intro_rule(op_three));
                thm needs_lvalue = cm_matching_assumption(
                    unary_branch,
                    `(a0:int) == 3i ==>
                     (cm_lvalue (a1:cm_expr) &&
                      ~cm_expr_array
                        (p:cm_program) (f:cm_function_d) a1)`);
                thm lvalue_and_array =
                    mp_rule(needs_lvalue, op_three);
                unary_branch = ASSUME_TAC(unary_branch,
                    conjunct1_rule(lvalue_and_array),
                    "harglvalue");
              } else {
                vector_add(&decisions,
                    eqf_intro_rule(cm_matching_assumption(
                      unary_branch, mk_not(is_three))));
              }
            }
            vector_add(&decisions, cm_expr_heights_def);
            vector_add(&decisions, cm_rvalue_heights_def);
            vector_add(&decisions, cm_rheights_of_def);
            gnode shaped = CONV_TAC(unary_branch,
                reduce_rewrite_conv(decisions));
            term suffix;
            bool child_lvalue = k == 1;
            thm boundary;
            if (k == 0) {
              suffix =
                  `[1i] ++ (annotations:(int)list)`;
              boundary = cm_fixed_local_next(
                  suffix, `1i`, THM_LIST());
            } else if (k == 1) {
              suffix = `annotations:(int)list`;
              boundary = cm_matching_assumption(
                  unary_branch,
                  `cm_local_next
                     (annotations:(int)list) 1i`);
            } else {
              suffix =
                  `[1i; 2i] ++ (annotations:(int)list)`;
              boundary = cm_fixed_local_next(
                  suffix, `1i`, THM_LIST());
            }
            thm start = cm_expr_start_ih(
                unary_branch, `a1:cm_expr`,
                child_lvalue, suffix, boundary);
            gnode normalized = CONV_TAC(shaped,
                rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND_ASSOC"))));
            ACCEPT_TAC(normalized, conv_rule(
                rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND_ASSOC"))),
                start));
          }
        }
        continue;
      }
      if (i == 6) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              cm_lvalue_heights_def, cm_rvalue_heights_def,
              cm_lheights_of_def, cm_rheights_of_def)));
        term suffix;
        if (j == 0) {
          suffix =
              `cm_temp_access_heights 1i ++
               cm_rheights_of
                 (cm_expr_heights (p:cm_program) fid
                   (a1:cm_expr)) ++
               [1i; 2i] ++ cm_temp_access_heights 1i ++
               [2i; 1i] ++ (annotations:(int)list)`;
        } else {
          suffix =
              `cm_temp_access_heights 1i ++
               cm_rheights_of
                 (cm_expr_heights (p:cm_program) fid
                   (a1:cm_expr)) ++
               [1i; 2i] ++ cm_temp_access_heights 1i ++
               [2i] ++ (annotations:(int)list)`;
        }
        thm boundary = cm_fixed_local_next(
            suffix, `1i`, THM_LIST());
        thm start = cm_expr_start_ih(
            branch, `a0:cm_expr`, false, suffix, boundary);
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))));
        ACCEPT_TAC(normalized, conv_rule(
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))), start));
        continue;
      }
      if (i == 7) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              cm_lvalue_heights_def, cm_rvalue_heights_def,
              cm_lheights_of_def, cm_rheights_of_def)));
        term suffix;
        if (j == 0) {
          suffix =
              `[1i; 2i] ++
               (if cm_member_array (p:cm_program)
                   (cm_expr_type (a0:cm_expr)) (a1:int)
                then ([]:(int)list) else [1i]) ++
               (annotations:(int)list)`;
        } else {
          suffix =
              `[1i; 2i] ++ (annotations:(int)list)`;
        }
        thm boundary = cm_fixed_local_next(
            suffix, `1i`, THM_LIST());
        thm start = cm_expr_start_ih(
            branch, `a0:cm_expr`, false, suffix, boundary);
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))));
        ACCEPT_TAC(normalized, conv_rule(
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))), start));
        continue;
      }
      if (i == 8) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              cm_rvalue_heights_def,
              cm_rheights_of_def)));
        term call_tail =
            `[ilength (a1:(cm_expr)list)] ++
             (annotations:(int)list)`;
        thm call_boundary = cm_fixed_local_next(
            call_tail, `ilength (a1:(cm_expr)list)`,
            THM_LIST());
        thm reload_rule = specl_rule(TERM_LIST(
            `a1:(cm_expr)list`, `0i`, call_tail),
            cm_args_reload_starts);
        thm boundary_index = int_arith_rule(
            `0i + ilength (a1:(cm_expr)list) ==
             ilength a1`);
        thm required_boundary = eq_mp_rule(
            sym_rule(beta_norm(ap_term_rule(
              `\next_height:int.
                 cm_local_next
                   ${call_tail:(int)list} next_height`,
              boundary_index))), call_boundary);
        thm reload_boundary =
            mp_rule(reload_rule, required_boundary);
        term suffix =
            `cm_args_reload_heights 0i
               (a1:(cm_expr)list) ++
             [ilength a1] ++
             (annotations:(int)list)`;
        term slots =
            `cm_function_params
               (inth (a0:int)
                 (cm_program_functions (p:cm_program)))`;
        thm start = cm_args_start_ih(
            branch, `a1:(cm_expr)list`, slots,
            suffix, reload_boundary);
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))));
        ACCEPT_TAC(normalized, conv_rule(
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))), start));
        continue;
      }
      if (i == 11 || i == 12 || i == 13) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              cm_rvalue_heights_def,
              cm_rheights_of_def)));
        term suffix;
        if (i == 13) {
          suffix =
              `cm_normalize_heights CMCharTy 1i ++ [1i] ++
               (annotations:(int)list)`;
        } else {
          suffix =
              `[1i; 2i] ++ (annotations:(int)list)`;
        }
        thm boundary = cm_fixed_local_next(
            suffix, `1i`, THM_LIST());
        thm start = cm_expr_start_ih(
            branch, `a0:cm_expr`, false, suffix, boundary);
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))));
        ACCEPT_TAC(normalized, conv_rule(
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))), start));
        continue;
      }
      if (i == 14) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              get_theorem_by_name("APPEND"))));
        ACCEPT_TAC(shaped, cm_matching_assumption(
            branch,
            `cm_local_next
               (annotations:(int)list) 0i`));
        continue;
      }
      if (i == 15) {
        gnode shaped = CONV_TAC(branch,
            reduce_rewrite_conv(THM_LIST(
              cm_expr_heights_def)));
        term suffix =
            `cm_temp_access_heights 1i ++
             cm_args_store_heights (p:cm_program) fid
               (a1:(cm_expr)list) ++
             (annotations:(int)list)`;
        thm boundary = cm_fixed_local_next(
            suffix, `1i`, THM_LIST());
        thm start = cm_expr_start_ih(
            branch, `a0:cm_expr`, false, suffix, boundary);
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))));
        ACCEPT_TAC(normalized, conv_rule(
            rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))), start));
        continue;
      }
      gnode reduced = CONV_WITH_ASMP_TAC(
          branch, reduce_rewrite_conv, THM_LIST(
            get_cm_expr_wf_def(), get_cm_lvalue_def(),
            cm_expr_heights_def,
            cm_lvalue_heights_def, cm_rvalue_heights_def,
            cm_lheights_of_def, cm_rheights_of_def,
            cm_binding_heights_start_nested,
            cm_fp_address_heights_def,
            cm_temp_access_heights_def,
            cm_normalize_heights_def,
            get_theorem_by_name("APPEND_ASSOC"),
            cm_binding_heights_start,
            cm_binary_finish_heights_def,
            cm_args_reload_heights_def,
            cm_local_next_def,
            get_theorem_by_name("APPEND"),
            get_theorem_by_name("NOT_CONS_NIL"),
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL")));
      if (IS_NULL(reduced->solved)) {
        if (is_false(goal_ccl(reduced->g))) {
          ACCEPT_TAC(reduced,
              cm_matching_assumption(reduced, mk_false()));
        } else {
          ACCEPT_TAC(reduced,
              taut_rule(goal_ccl(reduced->g)));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_codegen_height_starts =
    cm_prove_codegen_height_starts();

PROOF static thm cm_expr_codegen_ih(
    const gnode branch, const term expr, bool lvalue,
    const term pc, const term temp,
    const term tail, const term annotations,
    const thm stream, const thm boundary,
    const thm tail_ok) {
  term ih_term;
  if (lvalue) {
    ih_term =
        `!(p:cm_program) (f:cm_function_d) fid pc temp
            (target:int->int) (tail:(tvm_inst)list)
            (annotations:(int)list).
           cm_expr_wf p f ${expr:cm_expr} ==>
           cm_function_target_heights p target ==>
           cm_height_stream target pc
             (cm_lvalue_heights p fid ${expr:cm_expr} ++
              annotations) ==>
           cm_local_next annotations 1i ==>
           cm_local_codegen_ok p target tail annotations ==>
           cm_local_codegen_ok p target
             (cm_emit_lvalue p fid pc temp ${expr:cm_expr} ++
              tail)
             (cm_lvalue_heights p fid ${expr:cm_expr} ++
              annotations)`;
  } else {
    ih_term =
        `!(p:cm_program) (f:cm_function_d) fid pc temp
            (target:int->int) (tail:(tvm_inst)list)
            (annotations:(int)list).
           cm_expr_wf p f ${expr:cm_expr} ==>
           cm_function_target_heights p target ==>
           cm_height_stream target pc
             (cm_rvalue_heights p fid ${expr:cm_expr} ++
              annotations) ==>
           cm_local_next annotations 1i ==>
           cm_local_codegen_ok p target tail annotations ==>
           cm_local_codegen_ok p target
             (cm_emit_rvalue p fid pc temp ${expr:cm_expr} ++
              tail)
             (cm_rvalue_heights p fid ${expr:cm_expr} ++
              annotations)`;
  }
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, `fid:int`,
      pc, temp, `target:int->int`, tail, annotations),
      cm_matching_assumption(branch, ih_term));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
         ${expr:cm_expr}`));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_function_target_heights
         (p:cm_program) (target:int->int)`));
  result = conv_rule(rewrite_conv(THM_LIST(
      get_cm_emit_lvalue_def(), get_cm_emit_rvalue_def(),
      cm_lvalue_heights_def, cm_rvalue_heights_def)), result);
  result = mp_rule(result, stream);
  result = mp_rule(result, boundary);
  return mp_rule(result, tail_ok);
}

PROOF static thm cm_args_codegen_ih(
    const gnode branch, const term args, const term slots,
    const term pc, const term slot, const term scratch,
    const term tail, const term annotations,
    const thm stream, const thm boundary,
    const thm tail_ok) {
  term ih_term =
      `!(p:cm_program) (f:cm_function_d)
          (slots:(cm_slot_d)list) fid pc slot scratch
          (target:int->int) (tail:(tvm_inst)list)
          (annotations:(int)list).
         cm_args_wf p f ${args:(cm_expr)list} slots ==>
         cm_function_target_heights p target ==>
         cm_height_stream target pc
           (cm_args_store_heights p fid ${args:(cm_expr)list} ++
            annotations) ==>
         cm_local_next annotations 0i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_args_store p fid pc slot scratch
              ${args:(cm_expr)list} ++ tail)
           (cm_args_store_heights p fid ${args:(cm_expr)list} ++
            annotations)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, slots, `fid:int`,
      pc, slot, scratch, `target:int->int`, tail, annotations),
      cm_matching_assumption(branch, ih_term));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_args_wf (p:cm_program) (f:cm_function_d)
         ${args:(cm_expr)list} ${slots:(cm_slot_d)list}`));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_function_target_heights
         (p:cm_program) (target:int->int)`));
  result = mp_rule(result, stream);
  result = mp_rule(result, boundary);
  return mp_rule(result, tail_ok);
}

PROOF static thm cm_expr_height_length_fact(
    const term expr, bool lvalue) {
  thm pair = spec_rule(expr, cm_expr_height_lengths);
  thm selected =
      lvalue ? conjunct1_rule(pair) : conjunct2_rule(pair);
  return specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), selected);
}
PROOF static thm cm_generated_expr_start(
    const gnode branch, const term expr, bool lvalue,
    const term annotations, const thm boundary) {
  thm properties = spec_rule(expr,
      conjunct1_rule(cm_codegen_height_starts));
  thm selected =
      lvalue ? conjunct2_rule(properties)
             : conjunct1_rule(properties);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, `fid:int`,
      annotations), selected);
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
         ${expr:cm_expr}`));
  if (lvalue) {
    result = mp_rule(result, cm_matching_assumption(branch,
        `cm_lvalue ${expr:cm_expr}`));
  }
  return conv_rule(rewrite_conv(THM_LIST(
      cm_lvalue_heights_def, cm_rvalue_heights_def)),
      mp_rule(result, boundary));
}


PROOF static thm cm_drop_stream_to(
    const thm stream, const term prefix, const term suffix,
    const term from_pc, const term to_pc,
    const thm_list facts) {
  thm dropped = mp_rule(specl_rule(TERM_LIST(
      `target:int->int`, from_pc, prefix, suffix),
      cm_height_stream_drop), stream);
  thm_list definitions = THM_LIST(
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      cm_fp_address_heights_def,
      cm_temp_access_heights_def,
      cm_normalize_heights_def,
      cm_binding_address_heights_def,
      cm_binary_finish_heights_def,
      cm_args_reload_heights_def,
      cm_lvalue_heights_def,
      cm_rvalue_heights_def);
  for (size_t i = 0; i < vector_size(facts); ++i) {
    vector_add(&definitions, facts[i]);
  }
  thm address = by_defs_arith(
      `(${from_pc:int}) + ilength ${prefix:(int)list} ==
       ${to_pc:int}`,
      definitions, facts);
  return eq_mp_rule(beta_norm(ap_term_rule(
      `\address:int.
         cm_height_stream (target:int->int) address
           ${suffix:(int)list}`,
      address)), dropped);
}

PROOF static term cm_stream_annotations(
    const thm stream) {
  ENSURE_COND(cm_term_head_named(
      concl(stream), "cm_height_stream"),
      "Expected height-stream theorem");
  return dest_comb(concl(stream)).tm2;
err:
  ERR_FUN_PUTS("cm_stream_annotations", cstr_thm(stream));
  return empty_term;
}

PROOF static thm cm_stream_relist(
    const thm stream, const term pc,
    const thm list_equality) {
  return eq_mp_rule(beta_norm(ap_term_rule(
      `\heights:(int)list.
         cm_height_stream (target:int->int)
           ${pc:int} heights`,
      list_equality)), stream);
}

PROOF static thm cm_codegen_tail(
    const gnode branch) {
  return cm_matching_assumption(branch,
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
}

PROOF static thm cm_codegen_boundary(
    const gnode branch) {
  return cm_matching_assumption(branch,
      `cm_local_next (annotations:(int)list) 1i`);
}

PROOF static thm cm_codegen_stream(
    const gnode branch, bool lvalue, const term expr) {
  return cm_matching_assumption(branch, lvalue
      ? `cm_height_stream (target:int->int) (pc:int)
           (cm_lvalue_heights (p:cm_program) (fid:int)
              ${expr:cm_expr} ++
            (annotations:(int)list))`
      : `cm_height_stream (target:int->int) (pc:int)
           (cm_rvalue_heights (p:cm_program) (fid:int)
              ${expr:cm_expr} ++
            (annotations:(int)list))`);
}

PROOF static gnode cm_shape_codegen_goal(
    const gnode branch, const thm_list extra_rules) {
  thm_list rules = THM_LIST(
      get_cm_emit_lvalue_def(), get_cm_emit_rvalue_def(),
      get_cm_emit_expr_pair_def(),
      get_cm_lcode_of_def(), get_cm_rcode_of_def(),
      cm_lvalue_heights_def, cm_rvalue_heights_def,
      cm_expr_heights_def,
      cm_lheights_of_def, cm_rheights_of_def,
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("APPEND_ASSOC"),
      get_theorem_by_name("APPEND"));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  return CONV_TAC(branch, reduce_rewrite_conv(rules));
}
PROOF static thm cm_prove_normalize_heights_start(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) height (annotations:(int)list).
         cm_local_next annotations height ==>
         cm_local_next
           (cm_normalize_heights ty height ++ annotations)
           height`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term condition = `(ty:cm_type) == CMCharTy`;
  gnode_list cases =
      BOOL_CASES_TAC(leaf, condition, "hnormalize");
  for (size_t i = 0; i < 2; ++i) {
    thm decision = i == 0
        ? eqt_intro_rule(cm_matching_assumption(
            cases[i], condition))
        : eqf_intro_rule(cm_matching_assumption(
            cases[i], mk_not(condition)));
    gnode reduced = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          decision, cm_normalize_heights_def,
          cm_local_next_def,
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"),
          get_theorem_by_name("TL"))));
    if (IS_NULL(reduced->solved)) {
      thm boundary = cm_matching_assumption(
          reduced,
          `cm_local_next (annotations:(int)list)
             (height:int)`);
      ACCEPT_TAC(reduced, conv_rule(
          rewrite_conv(THM_LIST(cm_local_next_def)),
          boundary));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_normalize_heights_start =
    cm_prove_normalize_heights_start();


PROOF static thm cm_local_ok_transport(
    const thm local_ok, const term desired_code,
    const term desired_heights) {
  dest_comb_results height_app = dest_comb(concl(local_ok));
  term actual_heights = height_app.tm2;
  dest_comb_results code_app = dest_comb(height_app.tm1);
  term actual_code = code_app.tm2;
  thm with_code = local_ok;
  if (alpha_compare(desired_code, actual_code) != 0) {
    thm code_equality = by_rewrite(
        mk_eq(desired_code, actual_code),
        THM_LIST(get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL")));
    with_code = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
        `\code:(tvm_inst)list.
           cm_local_codegen_ok (p:cm_program)
             (target:int->int) code
             ${actual_heights:(int)list}`,
        code_equality))), local_ok);
  }
  if (alpha_compare(desired_heights, actual_heights) == 0) {
    return with_code;
  }
  thm height_equality = by_rewrite(
      mk_eq(desired_heights, actual_heights),
      THM_LIST(get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL")));
  return eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\heights:(int)list.
         cm_local_codegen_ok (p:cm_program)
           (target:int->int)
           ${desired_code:(tvm_inst)list} heights`,
      height_equality))), with_code);
}

PROOF static thm cm_prove_expr_local_codegen(void) {
  gnode root = gnode_new_with_ccl(
      `((!(expr:cm_expr).
           (!(p:cm_program) (f:cm_function_d) fid pc temp
               (target:int->int) (tail:(tvm_inst)list)
               (annotations:(int)list).
              cm_expr_wf p f expr ==>
              cm_function_target_heights p target ==>
              cm_height_stream target pc
                (cm_rvalue_heights p fid expr ++ annotations) ==>
              cm_local_next annotations 1i ==>
              cm_local_codegen_ok p target tail annotations ==>
              cm_local_codegen_ok p target
                (cm_emit_rvalue p fid pc temp expr ++ tail)
                (cm_rvalue_heights p fid expr ++ annotations)) &&
           (!(p:cm_program) (f:cm_function_d) fid pc temp
               (target:int->int) (tail:(tvm_inst)list)
               (annotations:(int)list).
              cm_expr_wf p f expr ==>
              cm_function_target_heights p target ==>
              cm_height_stream target pc
                (cm_lvalue_heights p fid expr ++ annotations) ==>
              cm_local_next annotations 1i ==>
              cm_local_codegen_ok p target tail annotations ==>
              cm_local_codegen_ok p target
                (cm_emit_lvalue p fid pc temp expr ++ tail)
                (cm_lvalue_heights p fid expr ++ annotations))) &&
        (!(args:(cm_expr)list).
           !(p:cm_program) (f:cm_function_d)
             (slots:(cm_slot_d)list) fid pc slot scratch
             (target:int->int) (tail:(tvm_inst)list)
             (annotations:(int)list).
           cm_args_wf p f args slots ==>
           cm_function_target_heights p target ==>
           cm_height_stream target pc
             (cm_args_store_heights p fid args ++ annotations) ==>
           cm_local_next annotations 0i ==>
           cm_local_codegen_ok p target tail annotations ==>
           cm_local_codegen_ok p target
             (cm_emit_args_store p fid pc slot scratch args ++ tail)
             (cm_args_store_heights p fid args ++ annotations)))`);
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
  for (size_t i = 0; i < 16; ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode branch = AUTO_ASMP_DESTRUCT_TAC(constructor)[0];
    gnode_list obligations;
    if (i < 14) {
      obligations = CONJ_TAC(branch);
    } else {
      obligations = gnode_list_from_array(1, &branch);
    }
    for (size_t j = 0; j < vector_size(obligations); ++j) {
      gnode leaf = AUTO_INTROS_TAC(obligations[j]);
      leaf = AUTO_ASMP_DESTRUCT_TAC(leaf)[0];
      thm wf = cm_predicate_assumption(
          leaf, i < 14 ? "cm_expr_wf" : "cm_args_wf");
      thm wf_parts = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            i < 14 ? get_cm_expr_wf_def()
                   : get_cm_args_wf_def())), wf);
      size_t wf_part = 0;
      leaf = cm_assume_conjunct_leaves(
          leaf, wf_parts, &wf_part);
      thm tail_ok = cm_codegen_tail(leaf);
      if (i < 14 && j == 1 &&
          (i == 0 || i == 1 || i == 3 || i == 4 ||
           i == 8 || i == 9 || i == 10 || i == 11 ||
           i == 12 || i == 13)) {
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        ACCEPT_TAC(shaped, tail_ok);
        continue;
      }
      if (i < 14 && j == 0 &&
          (i == 0 || i == 1 || i == 9)) {
        term imm;
        if (i == 0) {
          imm = `cm_const_immediate (a1:cm_type) (a0:int)`;
        } else if (i == 1) {
          imm = `cm_string_address
                   (p:cm_program) (a0:int)`;
        } else {
          imm = `cm_type_size
                   (cm_program_structs (p:cm_program))
                   (a0:cm_type)`;
        }
        thm result = cm_local_fixed(
            `p:cm_program`, `target:int->int`,
            `[(TVMInst TVMPushOp ${imm:int})]`, `[0i]`,
            `tail:(tvm_inst)list`,
            `annotations:(int)list`, tail_ok,
            cm_codegen_boundary(leaf), THM_LIST());
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST(get_cm_push_code_def()));
        ACCEPT_TAC(shaped, result);
        continue;
      }
      if (i == 10 && j == 0) {
        thm result = cm_local_fixed(
            `p:cm_program`, `target:int->int`,
            `[TVMInst TVMGetcOp 0i]`, `[0i]`,
            `tail:(tvm_inst)list`,
            `annotations:(int)list`, tail_ok,
            cm_codegen_boundary(leaf), THM_LIST());
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        ACCEPT_TAC(shaped, result);
        continue;
      }
      if (i == 2) {
        thm boundary = cm_codegen_boundary(leaf);
        term scope = `a0:int`;
        term slot = `a1:int`;
        term ty = `a2:cm_type`;
        if (j == 1) {
          thm result = specl_rule(TERM_LIST(
              `p:cm_program`, `target:int->int`,
              `fid:int`, scope, slot,
              `tail:(tvm_inst)list`,
              `annotations:(int)list`),
              cm_local_binding_address);
          result = mp_rule(mp_rule(result, boundary), tail_ok);
          gnode shaped = cm_shape_codegen_goal(
              leaf, THM_LIST());
          ACCEPT_TAC(shaped, result);
        } else {
          term is_array =
              `cm_binding_array (p:cm_program) (fid:int)
                 ${scope:int} ${slot:int}`;
          gnode_list array_cases =
              BOOL_CASES_TAC(leaf, is_array, "harray");
          {
            thm array = cm_matching_assumption(
                array_cases[0], is_array);
            thm result = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`,
                `fid:int`, scope, slot,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`),
                cm_local_binding_address);
            result = mp_rule(mp_rule(
                result, boundary), tail_ok);
            gnode shaped = cm_shape_codegen_goal(
                array_cases[0], THM_LIST(
                  eqt_intro_rule(array)));
            ACCEPT_TAC(shaped, result);
          }
          {
            thm not_array = cm_matching_assumption(
                array_cases[1], mk_not(is_array));
            thm loaded = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`, ty, `1i`,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`), cm_local_load);
            loaded = mp_rule(mp_rule(mp_rule(
                loaded, int_arith_rule(`1i <= 1i`)),
                boundary), tail_ok);
            term load_annotations =
                `(1i :: (annotations:(int)list))`;
            thm binding_boundary = cm_fixed_local_next(
                load_annotations, `1i`, THM_LIST());
            thm result = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`,
                `fid:int`, scope, slot,
                `(cm_load_code ${ty:cm_type} ++
                  (tail:(tvm_inst)list))`,
                load_annotations),
                cm_local_binding_address);
            result = mp_rule(mp_rule(
                result, binding_boundary), loaded);
            gnode shaped = cm_shape_codegen_goal(
                array_cases[1], THM_LIST(
                  eqf_intro_rule(not_array)));
            gnode normalized = CONV_TAC(shaped,
                rewrite_conv(THM_LIST(
                  gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
                  get_theorem_by_name("APPEND"))));
            ACCEPT_TAC(normalized, result);
          }
        }
        continue;
      }
      if (i == 3 && j == 0) {
        term dst = `a0:cm_expr`;
        term src = `a1:cm_expr`;
        term ty = `a2:cm_type`;
        term h1 = `(1i :: (annotations:(int)list))`;
        term c1 =
            `(cm_load_code ${ty:cm_type} ++
              (tail:(tvm_inst)list))`;
        thm load1 = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, ty, `1i`,
            `tail:(tvm_inst)list`, `annotations:(int)list`),
            cm_local_load);
        load1 = mp_rule(mp_rule(mp_rule(
            load1, int_arith_rule(`1i <= 1i`)),
            cm_codegen_boundary(leaf)), tail_ok);

        term h2 =
            `(cm_temp_access_heights 0i ++ ${h1:(int)list})`;
        term c2 =
            `(cm_temp_load_code (p:cm_program) (fid:int)
                (temp:int) ++ ${c1:(tvm_inst)list})`;
        thm temp0_boundary = cm_fixed_local_next(
            h1, `1i`, THM_LIST());
        thm temp0 = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `fid:int`,
            `temp:int`, `0i`, c1, h1),
            cm_local_temp_load);
        temp0 = conv_rule(
            reduce_rewrite_conv(THM_LIST()), temp0);
        temp0 = mp_rule(mp_rule(
            temp0, temp0_boundary), load1);

        term h3 = `(2i :: ${h2:(int)list})`;
        term c3 =
            `(cm_store_code ${ty:cm_type} ++
              ${c2:(tvm_inst)list})`;
        thm store_boundary = cm_fixed_local_next(
            h2, `0i`, THM_LIST());
        thm stored = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, ty, `2i`,
            c2, h2), cm_local_store);
        stored = conv_rule(
            reduce_rewrite_conv(THM_LIST()), stored);
        stored = mp_rule(mp_rule(
            stored, store_boundary), temp0);

        term h4 =
            `(cm_temp_access_heights 1i ++ ${h3:(int)list})`;
        term c4 =
            `(cm_temp_load_code (p:cm_program) (fid:int)
                (temp:int) ++ ${c3:(tvm_inst)list})`;
        thm temp1_boundary = cm_fixed_local_next(
            h3, `2i`, THM_LIST());
        thm temp1 = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `fid:int`,
            `temp:int`, `1i`, c3, h3),
            cm_local_temp_load);
        temp1 = conv_rule(
            reduce_rewrite_conv(THM_LIST()), temp1);
        temp1 = mp_rule(mp_rule(
            temp1, temp1_boundary), stored);

        term h5 =
            `(cm_normalize_heights ${ty:cm_type} 1i ++
              ${h4:(int)list})`;
        term c5 =
            `(cm_char_normalize_code ${ty:cm_type} ++
              ${c4:(tvm_inst)list})`;
        thm normalize_boundary = cm_fixed_local_next(
            h4, `1i`, THM_LIST());
        thm normalized_value = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, ty, `1i`,
            c4, h4), cm_local_char_normalize);
        normalized_value = mp_rule(mp_rule(mp_rule(
            normalized_value, int_arith_rule(`1i <= 1i`)),
            normalize_boundary), temp1);

        thm source_boundary = mp_rule(
            specl_rule(TERM_LIST(ty, `1i`, h4),
              cm_normalize_heights_start),
            normalize_boundary);
        thm whole_stream = cm_codegen_stream(
            leaf, false,
            `CMAssignE ${dst:cm_expr} ${src:cm_expr}
               ${ty:cm_type}`);
        thm direct_stream = conv_rule(
            rewrite_conv(THM_LIST(
              cm_rvalue_heights_def, cm_expr_heights_def,
              cm_rheights_of_def,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))),
            whole_stream);
        term dst_heights =
            `cm_lheights_of
               (cm_expr_heights (p:cm_program) (fid:int)
                 ${dst:cm_expr})`;
        term src_heights =
            `cm_rheights_of
               (cm_expr_heights (p:cm_program) (fid:int)
                 ${src:cm_expr})`;
        term source_suffix =
            `(${src_heights:(int)list} ++ ${h5:(int)list})`;
        term source_prefix =
            `(${dst_heights:(int)list} ++
              cm_temp_access_heights 1i)`;
        thm split_stream = conv_rule(
            once_rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))),
            direct_stream);
        term source_pc =
            `(pc:int) +
             cm_lvalue_code_count (p:cm_program) (fid:int)
               ${dst:cm_expr} + 5i`;
        thm source_stream = cm_drop_stream_to(
            split_stream, source_prefix, source_suffix,
            `pc:int`, source_pc,
            THM_LIST(cm_expr_height_length_fact(
              dst, true)));
        thm source_ok = cm_expr_codegen_ih(
            leaf, src, false, source_pc,
            `(temp:int) + 1i`, c5, h5,
            source_stream, source_boundary,
            normalized_value);

        term h6 =
            `(${src_heights:(int)list} ++ ${h5:(int)list})`;
        term c6 =
            `(cm_rcode_of
                (cm_emit_expr_pair (p:cm_program) (fid:int)
                  ${source_pc:int} ((temp:int) + 1i)
                  ${src:cm_expr}) ++
              ${c5:(tvm_inst)list})`;
        thm source_start = cm_generated_expr_start(
            leaf, src, false, h5, source_boundary);
        term h7 =
            `(cm_temp_access_heights 1i ++ ${h6:(int)list})`;
        term c7 =
            `(cm_temp_store_code (p:cm_program) (fid:int)
                (temp:int) ++ ${c6:(tvm_inst)list})`;
        thm saved_source = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `fid:int`,
            `temp:int`, `1i`, c6, h6),
            cm_local_temp_store);
        saved_source = conv_rule(
            reduce_rewrite_conv(THM_LIST()), saved_source);
        saved_source = mp_rule(mp_rule(
            saved_source, source_start), source_ok);

        thm destination_boundary = cm_fixed_local_next(
            h7, `1i`, THM_LIST());
        thm result = cm_expr_codegen_ih(
            leaf, dst, true, `pc:int`, `temp:int`,
            c7, h7, direct_stream,
            destination_boundary, saved_source);
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))));
        ACCEPT_TAC(normalized, result);
        continue;
      }
      if (i == 4 && j == 0) {
        term op = `a0:int`;
        term left = `a1:cm_expr`;
        term right = `a2:cm_expr`;
        term ty = `a3:cm_type`;
        term is_zero = `(${op:int}) == 0i`;
        term is_one = `(${op:int}) == 1i`;
        gnode_list zero_cases =
            BOOL_CASES_TAC(leaf, is_zero, "hbinzero");
        gnode_list one_cases =
            BOOL_CASES_TAC(zero_cases[1], is_one, "hbinone");
        gnode binary_cases[3] = {
          zero_cases[0], one_cases[0], one_cases[1]
        };
        for (size_t k = 0; k < 3; ++k) {
          gnode binary_branch = binary_cases[k];
          thm_list decisions = THM_LIST();
          if (k == 0) {
            vector_add(&decisions,
                eqt_intro_rule(cm_matching_assumption(
                  binary_branch, is_zero)));
          } else {
            vector_add(&decisions,
                eqf_intro_rule(cm_matching_assumption(
                  binary_branch, mk_not(is_zero))));
            if (k == 1) {
              vector_add(&decisions,
                  eqt_intro_rule(cm_matching_assumption(
                    binary_branch, is_one)));
            } else {
              vector_add(&decisions,
                  eqf_intro_rule(cm_matching_assumption(
                    binary_branch, mk_not(is_one))));
            }
          }
          thm_list stream_rules =
              (thm_list)vector_copy(decisions);
          vector_add(&stream_rules, cm_rvalue_heights_def);
          vector_add(&stream_rules, cm_expr_heights_def);
          vector_add(&stream_rules, cm_rheights_of_def);
          vector_add(&stream_rules,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")));
          thm whole_stream = cm_codegen_stream(
              binary_branch, false,
              `CMBinaryE ${op:int} ${left:cm_expr}
                 ${right:cm_expr} ${ty:cm_type}`);
          thm direct_stream = conv_rule(
              rewrite_conv(stream_rules), whole_stream);
          term left_heights =
              `cm_rheights_of
                 (cm_expr_heights (p:cm_program) (fid:int)
                   ${left:cm_expr})`;
          term right_heights =
              `cm_rheights_of
                 (cm_expr_heights (p:cm_program) (fid:int)
                   ${right:cm_expr})`;
          thm left_length =
              cm_expr_height_length_fact(left, false);
          thm right_length =
              cm_expr_height_length_fact(right, false);
          if (k == 2) {
            term finish_heights =
                `(cm_binary_finish_heights
                    (p:cm_program) ${op:int}
                    ${left:cm_expr} ${right:cm_expr} ++
                  (annotations:(int)list))`;
            term finish_code =
                `(cm_binary_finish_code
                    (p:cm_program) (fid:int) ${op:int}
                    ${left:cm_expr} ${right:cm_expr}
                    (temp:int) ++
                  (tail:(tvm_inst)list))`;
            thm finish_ok = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`, `fid:int`,
                op, left, right, `temp:int`,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`),
                cm_local_binary_finish);
            finish_ok = mp_rule(mp_rule(finish_ok,
                cm_codegen_boundary(binary_branch)),
                cm_codegen_tail(binary_branch));
            thm right_boundary = cm_fixed_local_next(
                finish_heights, `1i`, THM_LIST());
            term right_suffix =
                `(${right_heights:(int)list} ++
                  ${finish_heights:(int)list})`;
            term right_prefix =
                `(${left_heights:(int)list} ++
                  cm_temp_access_heights 1i)`;
            thm split_stream = conv_rule(
                once_rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND_ASSOC"))),
                direct_stream);
            term right_pc =
                `(pc:int) +
                 cm_rvalue_code_count (p:cm_program) (fid:int)
                   ${left:cm_expr} + 5i`;
            thm right_stream = cm_drop_stream_to(
                split_stream, right_prefix, right_suffix,
                `pc:int`, right_pc,
                THM_LIST(left_length));
            thm right_ok = cm_expr_codegen_ih(
                binary_branch, right, false, right_pc,
                `(temp:int) + 1i`, finish_code,
                finish_heights, right_stream,
                right_boundary, finish_ok);
            thm right_start = cm_generated_expr_start(
                binary_branch, right, false,
                finish_heights, right_boundary);
            term right_annotations =
                `(${right_heights:(int)list} ++
                  ${finish_heights:(int)list})`;
            term right_code =
                `(cm_rcode_of
                    (cm_emit_expr_pair (p:cm_program) (fid:int)
                      ${right_pc:int} ((temp:int) + 1i)
                      ${right:cm_expr}) ++
                  ${finish_code:(tvm_inst)list})`;
            term saved_heights =
                `(cm_temp_access_heights 1i ++
                  ${right_annotations:(int)list})`;
            term saved_code =
                `(cm_temp_store_code (p:cm_program) (fid:int)
                    (temp:int) ++
                  ${right_code:(tvm_inst)list})`;
            thm saved = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`, `fid:int`,
                `temp:int`, `1i`, right_code,
                right_annotations), cm_local_temp_store);
            saved = conv_rule(
                reduce_rewrite_conv(THM_LIST()), saved);
            saved = mp_rule(mp_rule(
                saved, right_start), right_ok);
            thm left_boundary = cm_fixed_local_next(
                saved_heights, `1i`, THM_LIST());
            thm result = cm_expr_codegen_ih(
                binary_branch, left, false, `pc:int`,
                `temp:int`, saved_code, saved_heights,
                direct_stream, left_boundary, saved);
            gnode shaped = cm_shape_codegen_goal(
                binary_branch, decisions);
            gnode normalized = CONV_TAC(shaped,
                rewrite_conv(THM_LIST(
                  gsym_rule(get_theorem_by_name(
                    "APPEND_ASSOC")),
                  get_theorem_by_name("APPEND"))));
            ACCEPT_TAC(normalized, result);
          } else {
            term final_heights =
                `([1i; 2i; 1i; 0i] ++
                  (annotations:(int)list))`;
            term end_pc =
                `(pc:int) +
                 cm_rvalue_code_count (p:cm_program) (fid:int)
                   ${left:cm_expr} +
                 cm_rvalue_code_count p fid
                   ${right:cm_expr} + 5i`;
            term branch_pc =
                `(pc:int) +
                 cm_rvalue_code_count (p:cm_program) (fid:int)
                   ${left:cm_expr} +
                 cm_rvalue_code_count p fid
                   ${right:cm_expr} + 4i`;
            term right_pc =
                `(pc:int) +
                 cm_rvalue_code_count (p:cm_program) (fid:int)
                   ${left:cm_expr} + 1i`;
            term right_suffix =
                `(${right_heights:(int)list} ++
                  ${final_heights:(int)list})`;
            term right_prefix =
                `(${left_heights:(int)list} ++ [1i])`;
            thm split_stream = conv_rule(
                once_rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND_ASSOC"))),
                direct_stream);
            thm right_stream = cm_drop_stream_to(
                split_stream, right_prefix, right_suffix,
                `pc:int`, right_pc,
                THM_LIST(left_length));

            term end_prefix =
                `(${right_heights:(int)list} ++
                  [1i; 2i; 1i; 0i])`;
            thm end_split = conv_rule(
                once_rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND_ASSOC"))),
                right_stream);
            thm end_stream = cm_drop_stream_to(
                end_split, end_prefix,
                `annotations:(int)list`,
                right_pc, end_pc, THM_LIST(right_length));
            thm end_target = mp_rule(mp_rule(
                specl_rule(TERM_LIST(
                  `target:int->int`, end_pc,
                  `annotations:(int)list`, `1i`),
                  cm_stream_local_next),
                end_stream), cm_codegen_boundary(binary_branch));

            term final_code =
                `[(TVMInst TVMPushOp 0i);
                  (TVMInst TVMNeOp 0i);
                  (TVMInst TVMJmpOp ${end_pc:int});
                  (TVMInst TVMPushOp
                    (if ${op:int} == 0i then 1i else 0i))]`;
            thm final_ok = cm_local_fixed(
                `p:cm_program`, `target:int->int`,
                final_code, `[1i; 2i; 1i; 0i]`,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`,
                cm_codegen_tail(binary_branch),
                cm_codegen_boundary(binary_branch),
                THM_LIST(end_target));
            thm final_boundary = cm_fixed_local_next(
                final_heights, `1i`, THM_LIST());
            term final_tail_code =
                `(${final_code:(tvm_inst)list} ++
                  (tail:(tvm_inst)list))`;
            final_ok = cm_local_ok_transport(
                final_ok, final_tail_code, final_heights);
            thm right_ok = cm_expr_codegen_ih(
                binary_branch, right, false, right_pc,
                `temp:int`, final_tail_code, final_heights,
                right_stream, final_boundary, final_ok);
            thm right_start = cm_generated_expr_start(
                binary_branch, right, false,
                final_heights, final_boundary);

            term branch_tail =
                `(0i :: (annotations:(int)list))`;
            term branch_prefix =
                `(${right_heights:(int)list} ++
                  [1i; 2i; 1i])`;
            thm final_tail_shape = by_rewrite(
                `([1i; 2i; 1i; 0i] ++
                    (annotations:(int)list)) ==
                 [1i; 2i; 1i] ++
                    ${branch_tail:(int)list}`,
                THM_LIST(get_theorem_by_name("APPEND")));
            thm lifted_tail_shape = beta_norm(ap_term_rule(
                `\suffix:(int)list.
                   ${right_heights:(int)list} ++ suffix`,
                final_tail_shape));
            thm grouped_tail = ispecl_rule(TERM_LIST(
                right_heights, `[1i; 2i; 1i]`,
                branch_tail),
                get_theorem_by_name("APPEND_ASSOC"));
            thm branch_shape =
                trans_rule(lifted_tail_shape, grouped_tail);
            thm branch_shaped_stream = cm_stream_relist(
                right_stream, right_pc, branch_shape);
            thm branch_stream = cm_drop_stream_to(
                branch_shaped_stream, branch_prefix,
                branch_tail, right_pc, branch_pc,
                THM_LIST(right_length));
            thm branch_boundary = cm_fixed_local_next(
                branch_tail, `0i`, THM_LIST());
            thm branch_target = mp_rule(mp_rule(
                specl_rule(TERM_LIST(
                  `target:int->int`, branch_pc,
                  branch_tail, `0i`),
                  cm_stream_local_next),
                branch_stream), branch_boundary);

            term right_annotations =
                `(${right_heights:(int)list} ++
                  ${final_heights:(int)list})`;
            term right_code =
                `(cm_rcode_of
                    (cm_emit_expr_pair (p:cm_program) (fid:int)
                      ${right_pc:int} (temp:int)
                      ${right:cm_expr}) ++
                  ${final_code:(tvm_inst)list} ++
                  (tail:(tvm_inst)list))`;
            term branch_op = k == 0 ? `TVMJnzOp` : `TVMJzOp`;
            term branch_instruction =
                `TVMInst ${branch_op:tvm_opcode}
                   ${branch_pc:int}`;
            thm conditional_ok = cm_local_fixed(
                `p:cm_program`, `target:int->int`,
                `[${branch_instruction:tvm_inst}]`, `[1i]`,
                right_code, right_annotations,
                right_ok, right_start,
                THM_LIST(branch_target));
            term after_branch_heights =
                `(1i :: ${right_annotations:(int)list})`;
            term after_branch_code =
                `(${branch_instruction:tvm_inst} ::
                  ${right_code:(tvm_inst)list})`;
            thm left_boundary = cm_fixed_local_next(
                after_branch_heights, `1i`, THM_LIST());
            thm branch_height_shape = by_rewrite(
                `([1i] ++ ${right_annotations:(int)list}) ==
                 ${after_branch_heights:(int)list}`,
                THM_LIST(get_theorem_by_name("APPEND")));
            thm left_list_shape = beta_norm(ap_term_rule(
                `\suffix:(int)list.
                   ${left_heights:(int)list} ++ suffix`,
                branch_height_shape));
            thm left_stream = cm_stream_relist(
                direct_stream, `pc:int`, left_list_shape);
            thm result = cm_expr_codegen_ih(
                binary_branch, left, false, `pc:int`,
                `temp:int`, after_branch_code,
                after_branch_heights, left_stream,
                left_boundary, conditional_ok);
            gnode shaped = cm_shape_codegen_goal(
                binary_branch, decisions);
            gnode normalized = CONV_TAC(shaped,
                rewrite_conv(THM_LIST(
                  gsym_rule(get_theorem_by_name(
                    "APPEND_ASSOC")),
                  get_theorem_by_name("APPEND"))));
            result = conv_rule(
                rewrite_conv(decisions), result);
            dest_comb_results desired_height =
                dest_comb(goal_ccl(normalized->g));
            term desired_heights = desired_height.tm2;
            term desired_code =
                dest_comb(desired_height.tm1).tm2;
            result = cm_local_ok_transport(
                result, desired_code, desired_heights);
            ACCEPT_TAC(normalized, result);
          }
        }
        continue;
      }
      if (i == 5) {
        term op = `a0:int`;
        term arg = `a1:cm_expr`;
        term ty = `a2:cm_type`;
        term is_two = `(${op:int}) == 2i`;
        term is_three = `(${op:int}) == 3i`;
        term is_zero = `(${op:int}) == 0i`;
        gnode_list two_cases =
            BOOL_CASES_TAC(leaf, is_two, "hunarytwo");
        gnode_list three_cases =
            BOOL_CASES_TAC(two_cases[1], is_three,
                "hunarythree");
        gnode_list zero_cases =
            BOOL_CASES_TAC(three_cases[1], is_zero,
                "hunaryzero");
        gnode unary_cases[4] = {
          two_cases[0], three_cases[0],
          zero_cases[0], zero_cases[1]
        };
        for (size_t k = 0; k < 4; ++k) {
          gnode unary_branch = unary_cases[k];
          thm_list decisions = THM_LIST();
          if (k == 0) {
            vector_add(&decisions,
                eqt_intro_rule(cm_matching_assumption(
                  unary_branch, is_two)));
          } else {
            vector_add(&decisions,
                eqf_intro_rule(cm_matching_assumption(
                  unary_branch, mk_not(is_two))));
            if (k == 1) {
              vector_add(&decisions,
                  eqt_intro_rule(cm_matching_assumption(
                    unary_branch, is_three)));
            } else {
              vector_add(&decisions,
                  eqf_intro_rule(cm_matching_assumption(
                    unary_branch, mk_not(is_three))));
              vector_add(&decisions,
                  k == 2
                    ? eqt_intro_rule(cm_matching_assumption(
                        unary_branch, is_zero))
                    : eqf_intro_rule(cm_matching_assumption(
                        unary_branch, mk_not(is_zero))));
            }
          }
          if (j == 1 && k != 0) {
            gnode shaped = cm_shape_codegen_goal(
                unary_branch, decisions);
            ACCEPT_TAC(shaped,
                cm_codegen_tail(unary_branch));
            continue;
          }
          thm_list stream_rules =
              (thm_list)vector_copy(decisions);
          vector_add(&stream_rules,
              j == 0 ? cm_rvalue_heights_def
                     : cm_lvalue_heights_def);
          vector_add(&stream_rules, cm_expr_heights_def);
          vector_add(&stream_rules,
              j == 0 ? cm_rheights_of_def
                     : cm_lheights_of_def);
          vector_add(&stream_rules,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")));
          thm direct_stream = conv_rule(
              rewrite_conv(stream_rules),
              cm_codegen_stream(unary_branch, j == 1,
                `CMUnaryE ${op:int} ${arg:cm_expr}
                   ${ty:cm_type}`));
          thm result;
          if (k == 0 && j == 0) {
            term load_heights =
                `([1i] ++ (annotations:(int)list))`;
            term load_code =
                `(cm_load_code ${ty:cm_type} ++
                  (tail:(tvm_inst)list))`;
            thm loaded = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`, ty, `1i`,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`), cm_local_load);
            loaded = mp_rule(mp_rule(mp_rule(
                loaded, int_arith_rule(`1i <= 1i`)),
                cm_codegen_boundary(unary_branch)),
                cm_codegen_tail(unary_branch));
            loaded = cm_local_ok_transport(
                loaded, load_code, load_heights);
            thm child_boundary = cm_fixed_local_next(
                load_heights, `1i`, THM_LIST());
            result = cm_expr_codegen_ih(
                unary_branch, arg, false, `pc:int`,
                `temp:int`, load_code, load_heights,
                direct_stream, child_boundary, loaded);
          } else if (k == 0) {
            result = cm_expr_codegen_ih(
                unary_branch, arg, false, `pc:int`,
                `temp:int`, `tail:(tvm_inst)list`,
                `annotations:(int)list`, direct_stream,
                cm_codegen_boundary(unary_branch),
                cm_codegen_tail(unary_branch));
          } else if (k == 1) {
            result = cm_expr_codegen_ih(
                unary_branch, arg, true, `pc:int`,
                `temp:int`, `tail:(tvm_inst)list`,
                `annotations:(int)list`, direct_stream,
                cm_codegen_boundary(unary_branch),
                cm_codegen_tail(unary_branch));
          } else {
            term final_code = k == 2
                ? `[(TVMInst TVMPushOp (--1i));
                    (TVMInst TVMMulOp 0i)]`
                : `[(TVMInst TVMPushOp 0i);
                    (TVMInst TVMEqOp 0i)]`;
            term final_heights =
                `([1i; 2i] ++ (annotations:(int)list))`;
            term final_tail =
                `(${final_code:(tvm_inst)list} ++
                  (tail:(tvm_inst)list))`;
            thm fixed = cm_local_fixed(
                `p:cm_program`, `target:int->int`,
                final_code, `[1i; 2i]`,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`,
                cm_codegen_tail(unary_branch),
                cm_codegen_boundary(unary_branch),
                THM_LIST());
            fixed = cm_local_ok_transport(
                fixed, final_tail, final_heights);
            thm child_boundary = cm_fixed_local_next(
                final_heights, `1i`, THM_LIST());
            result = cm_expr_codegen_ih(
                unary_branch, arg, false, `pc:int`,
                `temp:int`, final_tail, final_heights,
                direct_stream, child_boundary, fixed);
          }
          gnode shaped = cm_shape_codegen_goal(
              unary_branch, decisions);
          gnode normalized = CONV_TAC(shaped,
              rewrite_conv(THM_LIST(
                gsym_rule(get_theorem_by_name(
                  "APPEND_ASSOC")),
                get_theorem_by_name("APPEND"))));
          result = conv_rule(
              rewrite_conv(decisions), result);
          dest_comb_results desired_height =
              dest_comb(goal_ccl(normalized->g));
          term desired_heights = desired_height.tm2;
          term desired_code =
              dest_comb(desired_height.tm1).tm2;
          result = cm_local_ok_transport(
              result, desired_code, desired_heights);
          ACCEPT_TAC(normalized, result);
        }
        continue;
      }
      if (i == 6) {
        term base = `a0:cm_expr`;
        term index = `a1:cm_expr`;
        term ty = `a2:cm_type`;
        thm outer_boundary = cm_codegen_boundary(leaf);
        thm outer_tail = cm_codegen_tail(leaf);
        term add_heights;
        term add_code;
        thm add_ok;
        if (j == 0) {
          term load_heights =
              `([1i] ++ (annotations:(int)list))`;
          term load_code =
              `(cm_load_code ${ty:cm_type} ++
                (tail:(tvm_inst)list))`;
          thm loaded = specl_rule(TERM_LIST(
              `p:cm_program`, `target:int->int`, ty, `1i`,
              `tail:(tvm_inst)list`,
              `annotations:(int)list`), cm_local_load);
          loaded = mp_rule(mp_rule(mp_rule(
              loaded, int_arith_rule(`1i <= 1i`)),
              outer_boundary), outer_tail);
          loaded = cm_local_ok_transport(
              loaded, load_code, load_heights);
          add_heights =
              `([2i] ++ ${load_heights:(int)list})`;
          add_code =
              `([TVMInst TVMAddOp 0i] ++
                ${load_code:(tvm_inst)list})`;
          add_ok = cm_local_fixed(
              `p:cm_program`, `target:int->int`,
              `[TVMInst TVMAddOp 0i]`, `[2i]`,
              load_code, load_heights, loaded,
              cm_fixed_local_next(
                load_heights, `1i`, THM_LIST()),
              THM_LIST());
          add_ok = cm_local_ok_transport(
              add_ok, add_code, add_heights);
        } else {
          add_heights =
              `([2i] ++ (annotations:(int)list))`;
          add_code =
              `([TVMInst TVMAddOp 0i] ++
                (tail:(tvm_inst)list))`;
          add_ok = cm_local_fixed(
              `p:cm_program`, `target:int->int`,
              `[TVMInst TVMAddOp 0i]`, `[2i]`,
              `tail:(tvm_inst)list`,
              `annotations:(int)list`,
              outer_tail, outer_boundary, THM_LIST());
          add_ok = cm_local_ok_transport(
              add_ok, add_code, add_heights);
        }

        term temp_heights =
            `(cm_temp_access_heights 1i ++
              ${add_heights:(int)list})`;
        term temp_code =
            `(cm_temp_load_code (p:cm_program) (fid:int)
                (temp:int) ++
              ${add_code:(tvm_inst)list})`;
        thm temp_loaded = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `fid:int`,
            `temp:int`, `1i`, add_code, add_heights),
            cm_local_temp_load);
        temp_loaded = conv_rule(
            reduce_rewrite_conv(THM_LIST()), temp_loaded);
        temp_loaded = mp_rule(mp_rule(
            temp_loaded, cm_fixed_local_next(
              add_heights, `2i`, THM_LIST())), add_ok);
        temp_loaded = cm_local_ok_transport(
            temp_loaded, temp_code, temp_heights);

        term scale_heights =
            `([1i; 2i] ++ ${temp_heights:(int)list})`;
        term scale_code =
            `([TVMInst TVMPushOp
                 (cm_type_size
                   (cm_program_structs (p:cm_program))
                   ${ty:cm_type});
               TVMInst TVMMulOp 0i] ++
              ${temp_code:(tvm_inst)list})`;
        thm scaled = cm_local_fixed(
            `p:cm_program`, `target:int->int`,
            `[TVMInst TVMPushOp
                (cm_type_size
                  (cm_program_structs (p:cm_program))
                  ${ty:cm_type});
              TVMInst TVMMulOp 0i]`,
            `[1i; 2i]`, temp_code, temp_heights,
            temp_loaded, cm_fixed_local_next(
              temp_heights, `1i`, THM_LIST()),
            THM_LIST());
        scaled = cm_local_ok_transport(
            scaled, scale_code, scale_heights);

        thm index_boundary = cm_fixed_local_next(
            scale_heights, `1i`, THM_LIST());
        thm whole_stream = cm_codegen_stream(
            leaf, j == 1,
            `CMIndexE ${base:cm_expr} ${index:cm_expr}
               ${ty:cm_type}`);
        thm_list stream_rules = THM_LIST(
            j == 0 ? cm_rvalue_heights_def
                   : cm_lvalue_heights_def,
            cm_expr_heights_def,
            j == 0 ? cm_rheights_of_def
                   : cm_lheights_of_def,
            gsym_rule(get_theorem_by_name("APPEND_ASSOC")));
        thm direct_stream = conv_rule(
            rewrite_conv(stream_rules), whole_stream);
        term base_heights =
            `cm_rheights_of
               (cm_expr_heights (p:cm_program) (fid:int)
                 ${base:cm_expr})`;
        term index_heights =
            `cm_rheights_of
               (cm_expr_heights (p:cm_program) (fid:int)
                 ${index:cm_expr})`;
        term index_suffix =
            `(${index_heights:(int)list} ++
              ${scale_heights:(int)list})`;
        term index_prefix =
            `(${base_heights:(int)list} ++
              cm_temp_access_heights 1i)`;
        term split_annotations =
            `(${index_prefix:(int)list} ++
              ${index_suffix:(int)list})`;
        thm old_normal = apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))),
            cm_stream_annotations(direct_stream));
        thm desired_normal = apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_theorem_by_name("APPEND_ASSOC"))),
            split_annotations);
        thm split_shape;
        if (j == 0) {
          term final_prefix =
              `(((${index_prefix:(int)list} ++
                   ${index_heights:(int)list}) ++
                  [1i; 2i]) ++
                 cm_temp_access_heights 1i)`;
          thm chunk_split = sym_rule(apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"))),
              `([2i] ++ [1i])`));
          thm embedded_split = beta_norm(ap_term_rule(
              `\middle:(int)list.
                 ((${final_prefix:(int)list} ++ middle) ++
                  (annotations:(int)list))`,
              chunk_split));
          thm reassociate = beta_norm(ap_term_rule(
              `\middle:(int)list.
                 middle ++ (annotations:(int)list)`,
              ispecl_rule(TERM_LIST(
                final_prefix, `[2i]`, `[1i]`),
                get_theorem_by_name("APPEND_ASSOC"))));
          split_shape = trans_rule(trans_rule(trans_rule(
              old_normal, embedded_split), reassociate),
              sym_rule(desired_normal));
        } else {
          split_shape = trans_rule(
              old_normal, sym_rule(desired_normal));
        }
        thm split_stream = cm_stream_relist(
            direct_stream, `pc:int`, split_shape);
        term index_pc =
            `(pc:int) +
             cm_rvalue_code_count (p:cm_program) (fid:int)
               ${base:cm_expr} + 5i`;
        thm index_stream = cm_drop_stream_to(
            split_stream, index_prefix, index_suffix,
            `pc:int`, index_pc,
            THM_LIST(cm_expr_height_length_fact(
              base, false)));
        thm index_ok = cm_expr_codegen_ih(
            leaf, index, false, index_pc,
            `(temp:int) + 1i`, scale_code,
            scale_heights, index_stream,
            index_boundary, scaled);
        thm index_start = cm_generated_expr_start(
            leaf, index, false, scale_heights,
            index_boundary);

        term index_annotations =
            `(${index_heights:(int)list} ++
              ${scale_heights:(int)list})`;
        term index_code =
            `(cm_rcode_of
                (cm_emit_expr_pair (p:cm_program) (fid:int)
                  ${index_pc:int} ((temp:int) + 1i)
                  ${index:cm_expr}) ++
              ${scale_code:(tvm_inst)list})`;
        term saved_heights =
            `(cm_temp_access_heights 1i ++
              ${index_annotations:(int)list})`;
        term saved_code =
            `(cm_temp_store_code (p:cm_program) (fid:int)
                (temp:int) ++
              ${index_code:(tvm_inst)list})`;
        thm saved = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `fid:int`,
            `temp:int`, `1i`, index_code,
            index_annotations), cm_local_temp_store);
        saved = conv_rule(
            reduce_rewrite_conv(THM_LIST()), saved);
        saved = mp_rule(mp_rule(
            saved, index_start), index_ok);
        saved = cm_local_ok_transport(
            saved, saved_code, saved_heights);
        thm base_shape = gsym_rule(ispecl_rule(TERM_LIST(
            base_heights, `cm_temp_access_heights 1i`,
            index_annotations),
            get_theorem_by_name("APPEND_ASSOC")));
        thm base_stream = cm_stream_relist(
            split_stream, `pc:int`, base_shape);

        thm base_boundary = cm_fixed_local_next(
            saved_heights, `1i`, THM_LIST());
        thm result = cm_expr_codegen_ih(
            leaf, base, false, `pc:int`, `temp:int`,
            saved_code, saved_heights, base_stream,
            base_boundary, saved);
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              gsym_rule(get_theorem_by_name(
                "APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))));
        dest_comb_results desired_height =
            dest_comb(goal_ccl(normalized->g));
        term desired_heights = desired_height.tm2;
        term desired_code =
            dest_comb(desired_height.tm1).tm2;
        result = cm_local_ok_transport(
            result, desired_code, desired_heights);
        ACCEPT_TAC(normalized, result);
        continue;
      }
      if (i == 7) {
        term base = `a0:cm_expr`;
        term mid = `a1:int`;
        term ty = `a2:cm_type`;
        term is_array =
            `cm_member_array (p:cm_program)
               (cm_expr_type ${base:cm_expr}) ${mid:int}`;
        gnode_list array_cases =
            BOOL_CASES_TAC(leaf, is_array, "hmemberarray");
        for (size_t k = 0; k < 2; ++k) {
          gnode member_branch = array_cases[k];
          thm decision = k == 0
              ? eqt_intro_rule(cm_matching_assumption(
                  member_branch, is_array))
              : eqf_intro_rule(cm_matching_assumption(
                  member_branch, mk_not(is_array)));
          thm_list decisions = THM_LIST(decision);
          thm_list stream_rules = THM_LIST(
              decision,
              j == 0 ? cm_rvalue_heights_def
                     : cm_lvalue_heights_def,
              cm_expr_heights_def,
              j == 0 ? cm_rheights_of_def
                     : cm_lheights_of_def,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")));
          thm direct_stream = conv_rule(
              rewrite_conv(stream_rules),
              cm_codegen_stream(member_branch, j == 1,
                `CMMemberE ${base:cm_expr} ${mid:int}
                   ${ty:cm_type}`));
          term final_heights;
          term final_code;
          thm final_ok;
          thm final_boundary;
          if (j == 0 && k == 1) {
            final_heights =
                `([1i] ++ (annotations:(int)list))`;
            final_code =
                `(cm_load_code ${ty:cm_type} ++
                  (tail:(tvm_inst)list))`;
            final_ok = specl_rule(TERM_LIST(
                `p:cm_program`, `target:int->int`, ty, `1i`,
                `tail:(tvm_inst)list`,
                `annotations:(int)list`), cm_local_load);
            final_ok = mp_rule(mp_rule(mp_rule(
                final_ok, int_arith_rule(`1i <= 1i`)),
                cm_codegen_boundary(member_branch)),
                cm_codegen_tail(member_branch));
            final_ok = cm_local_ok_transport(
                final_ok, final_code, final_heights);
            final_boundary = cm_fixed_local_next(
                final_heights, `1i`, THM_LIST());
          } else {
            final_heights = `annotations:(int)list`;
            final_code = `tail:(tvm_inst)list`;
            final_ok = cm_codegen_tail(member_branch);
            final_boundary = cm_codegen_boundary(member_branch);
          }
          term add_prefix =
              `[TVMInst TVMPushOp
                   (cm_member_offset
                     (cm_program_structs (p:cm_program))
                     (cm_struct_id
                       (cm_pointee
                         (cm_expr_type ${base:cm_expr})))
                     ${mid:int});
                TVMInst TVMAddOp 0i]`;
          term add_heights =
              `([1i; 2i] ++ ${final_heights:(int)list})`;
          term add_code =
              `(${add_prefix:(tvm_inst)list} ++
                ${final_code:(tvm_inst)list})`;
          thm added = cm_local_fixed(
              `p:cm_program`, `target:int->int`,
              add_prefix, `[1i; 2i]`,
              final_code, final_heights, final_ok,
              final_boundary,
              THM_LIST());
          added = cm_local_ok_transport(
              added, add_code, add_heights);
          thm base_boundary = cm_fixed_local_next(
              add_heights, `1i`, THM_LIST());
          term expected_annotations =
              `(cm_rheights_of
                  (cm_expr_heights (p:cm_program) (fid:int)
                    ${base:cm_expr}) ++
                ${add_heights:(int)list})`;
          thm base_stream = direct_stream;
          if (alpha_compare(
                cm_stream_annotations(direct_stream),
                expected_annotations) != 0) {
            thm old_normal = apply_conversion(
                reduce_rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND"),
                  get_theorem_by_name("APPEND_NIL"))),
                cm_stream_annotations(direct_stream));
            thm expected_normal = apply_conversion(
                reduce_rewrite_conv(THM_LIST(
                  get_theorem_by_name("APPEND"),
                  get_theorem_by_name("APPEND_NIL"))),
                expected_annotations);
            thm stream_shape = trans_rule(
                old_normal, sym_rule(expected_normal));
            base_stream = cm_stream_relist(
                direct_stream, `pc:int`, stream_shape);
          }
          thm result = cm_expr_codegen_ih(
              member_branch, base, false, `pc:int`,
              `temp:int`, add_code, add_heights,
              base_stream, base_boundary, added);
          gnode shaped = cm_shape_codegen_goal(
              member_branch, decisions);
          gnode normalized = CONV_TAC(shaped,
              rewrite_conv(THM_LIST(
                gsym_rule(get_theorem_by_name(
                  "APPEND_ASSOC")),
                get_theorem_by_name("APPEND"))));
          result = conv_rule(
              rewrite_conv(decisions), result);
          dest_comb_results desired_height =
              dest_comb(goal_ccl(normalized->g));
          term desired_heights = desired_height.tm2;
          term desired_code =
              dest_comb(desired_height.tm1).tm2;
          result = cm_local_ok_transport(
              result, desired_code, desired_heights);
          ACCEPT_TAC(normalized, result);
        }
        continue;
      }
      if (i == 8) {
        term callee = `a0:int`;
        term args = `a1:(cm_expr)list`;
        term params =
            `cm_function_params
               (inth ${callee:int}
                 (cm_program_functions (p:cm_program)))`;
        thm args_wf = cm_matching_assumption(leaf,
            `cm_args_wf (p:cm_program) (f:cm_function_d)
               ${args:(cm_expr)list}
               ${params:(cm_slot_d)list}`);
        thm args_length = mp_rule(specl_rule(TERM_LIST(
            args, `p:cm_program`, `f:cm_function_d`, params),
            cm_args_wf_length), args_wf);
        thm lower = cm_matching_assumption(
            leaf, `0i <= ${callee:int}`);
        thm upper = cm_matching_assumption(leaf,
            `${callee:int} <
             ilength (cm_program_functions (p:cm_program))`);
        term call_inst =
            `TVMInst TVMCallOp
               (cm_function_pc (p:cm_program) ${callee:int})`;
        thm immediate = by_rewrite(
            `tvm_inst_imm ${call_inst:tvm_inst} ==
             cm_function_pc (p:cm_program) ${callee:int}`,
            THM_LIST(get_tvm_inst_imm_def()));
        term call_exists =
            `?called.
               0i <= called &&
               called <
                 ilength (cm_program_functions (p:cm_program)) &&
               tvm_inst_imm ${call_inst:tvm_inst} ==
                 cm_function_pc p called &&
               ilength ${args:(cm_expr)list} ==
                 ilength (cm_function_params
                   (inth called (cm_program_functions p)))`;
        thm witness = exists_rule(
            call_exists, callee,
            conj_rule(lower, conj_rule(upper,
              conj_rule(immediate, args_length))));
        term is_call =
            `tvm_inst_op ${call_inst:tvm_inst} == TVMCallOp`;
        thm call_fact = disch_rule(is_call, witness);
        thm args_nonnegative = ispec_rule(
            args, get_theorem_by_name("ILENGTH_NONNEG"));
        thm target_rule = conv_rule(
            rewrite_conv(THM_LIST(
              cm_function_target_heights_def)),
            cm_matching_assumption(leaf,
              `cm_function_target_heights
                 (p:cm_program) (target:int->int)`));
        thm target_arity = mp_rule(mp_rule(
            spec_rule(callee, target_rule), lower), upper);
        thm target_height = trans_rule(
            target_arity, sym_rule(args_length));
        term call_heights =
            `([ilength ${args:(cm_expr)list}] ++
              (annotations:(int)list))`;
        term call_code =
            `([${call_inst:tvm_inst}] ++
              (tail:(tvm_inst)list))`;
        thm called = cm_local_fixed(
            `p:cm_program`, `target:int->int`,
            `[${call_inst:tvm_inst}]`,
            `[ilength ${args:(cm_expr)list}]`,
            `tail:(tvm_inst)list`,
            `annotations:(int)list`,
            cm_codegen_tail(leaf), cm_codegen_boundary(leaf),
            THM_LIST(call_fact, args_nonnegative, target_height));
        called = cm_local_ok_transport(
            called, call_code, call_heights);
        thm call_boundary = cm_fixed_local_next(
            call_heights, `ilength ${args:(cm_expr)list}`,
            THM_LIST());
        thm zero_plus_length = int_arith_rule(
            `0i + ilength ${args:(cm_expr)list} ==
             ilength ${args:(cm_expr)list}`);
        thm reload_boundary = eq_mp_rule(
            sym_rule(beta_norm(ap_term_rule(
              `\height:int.
                 cm_local_next ${call_heights:(int)list} height`,
              zero_plus_length))),
            call_boundary);
        term reload_heights =
            `(cm_args_reload_heights 0i ${args:(cm_expr)list} ++
              ${call_heights:(int)list})`;
        term reload_code =
            `(cm_emit_args_reload (p:cm_program) (fid:int)
                (temp:int) ${args:(cm_expr)list} ++
              ${call_code:(tvm_inst)list})`;
        thm reloaded = specl_rule(TERM_LIST(
            args, `p:cm_program`, `target:int->int`, `fid:int`,
            `temp:int`, `0i`, call_code, call_heights),
            cm_local_args_reload);
        reloaded = mp_rule(mp_rule(mp_rule(
            reloaded, int_arith_rule(`0i <= 0i`)),
            reload_boundary), called);
        reloaded = cm_local_ok_transport(
            reloaded, reload_code, reload_heights);
        thm store_boundary = mp_rule(specl_rule(TERM_LIST(
            args, `0i`, call_heights),
            cm_args_reload_starts), reload_boundary);
        thm direct_stream = conv_rule(
            rewrite_conv(THM_LIST(
              cm_rvalue_heights_def, cm_expr_heights_def,
              cm_rheights_of_def,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
            cm_codegen_stream(leaf, false,
              `CMCallE ${callee:int} ${args:(cm_expr)list}
                 (a2:cm_type)`));
        term expected_annotations =
            `(cm_args_store_heights (p:cm_program) (fid:int)
                ${args:(cm_expr)list} ++
              ${reload_heights:(int)list})`;
        thm args_stream = direct_stream;
        if (alpha_compare(
              cm_stream_annotations(direct_stream),
              expected_annotations) != 0) {
          thm old_normal = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"),
                get_theorem_by_name("APPEND_NIL"),
                get_theorem_by_name("APPEND_ASSOC"))),
              cm_stream_annotations(direct_stream));
          thm expected_normal = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"),
                get_theorem_by_name("APPEND_NIL"),
                get_theorem_by_name("APPEND_ASSOC"))),
              expected_annotations);
          thm stream_shape = trans_rule(
              old_normal, sym_rule(expected_normal));
          args_stream = cm_stream_relist(
              direct_stream, `pc:int`, stream_shape);
        }
        thm result = cm_args_codegen_ih(
            leaf, args, params, `pc:int`, `temp:int`,
            `(temp:int) + ilength ${args:(cm_expr)list}`,
            reload_code, reload_heights, args_stream,
            store_boundary, reloaded);
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))));
        dest_comb_results desired_height =
            dest_comb(goal_ccl(normalized->g));
        term desired_heights = desired_height.tm2;
        term desired_code =
            dest_comb(desired_height.tm1).tm2;
        result = cm_local_ok_transport(
            result, desired_code, desired_heights);
        ACCEPT_TAC(normalized, result);
        continue;
      }
      if (i == 11 || i == 12) {
        term arg = `a0:cm_expr`;
        term output_op =
            i == 11 ? `TVMPutcOp` : `TVMPutiOp`;
        term final_prefix =
            `[TVMInst TVMDupOp 0i;
              TVMInst ${output_op:tvm_opcode} 0i]`;
        term final_heights =
            `([1i; 2i] ++ (annotations:(int)list))`;
        term final_code =
            `(${final_prefix:(tvm_inst)list} ++
              (tail:(tvm_inst)list))`;
        thm fixed = cm_local_fixed(
            `p:cm_program`, `target:int->int`,
            final_prefix, `[1i; 2i]`,
            `tail:(tvm_inst)list`,
            `annotations:(int)list`,
            cm_codegen_tail(leaf), cm_codegen_boundary(leaf),
            THM_LIST());
        fixed = cm_local_ok_transport(
            fixed, final_code, final_heights);
        thm arg_boundary = cm_fixed_local_next(
            final_heights, `1i`, THM_LIST());
        thm direct_stream = conv_rule(
            rewrite_conv(THM_LIST(
              cm_rvalue_heights_def, cm_expr_heights_def,
              cm_rheights_of_def,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
            cm_codegen_stream(leaf, false,
              i == 11
                ? `CMPutcE ${arg:cm_expr} (a1:cm_type)`
                : `CMPutiE ${arg:cm_expr} (a1:cm_type)`));
        thm result = cm_expr_codegen_ih(
            leaf, arg, false, `pc:int`, `temp:int`,
            final_code, final_heights, direct_stream,
            arg_boundary, fixed);
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))));
        dest_comb_results desired_height =
            dest_comb(goal_ccl(normalized->g));
        term desired_heights = desired_height.tm2;
        term desired_code =
            dest_comb(desired_height.tm1).tm2;
        result = cm_local_ok_transport(
            result, desired_code, desired_heights);
        ACCEPT_TAC(normalized, result);
        continue;
      }
      if (i == 13) {
        term arg = `a0:cm_expr`;
        term halt_heights =
            `([1i] ++ (annotations:(int)list))`;
        term halt_code =
            `([TVMInst TVMHaltOp 0i] ++
              (tail:(tvm_inst)list))`;
        thm halted = cm_local_fixed(
            `p:cm_program`, `target:int->int`,
            `[TVMInst TVMHaltOp 0i]`, `[1i]`,
            `tail:(tvm_inst)list`,
            `annotations:(int)list`,
            cm_codegen_tail(leaf), cm_codegen_boundary(leaf),
            THM_LIST());
        halted = cm_local_ok_transport(
            halted, halt_code, halt_heights);
        thm halt_boundary = cm_fixed_local_next(
            halt_heights, `1i`, THM_LIST());
        term normalize_heights =
            `(cm_normalize_heights CMCharTy 1i ++
              ${halt_heights:(int)list})`;
        term normalize_code =
            `(cm_char_normalize_code CMCharTy ++
              ${halt_code:(tvm_inst)list})`;
        thm normalized_value = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `CMCharTy`,
            `1i`, halt_code, halt_heights),
            cm_local_char_normalize);
        normalized_value = mp_rule(mp_rule(mp_rule(
            normalized_value, int_arith_rule(`1i <= 1i`)),
            halt_boundary), halted);
        normalized_value = cm_local_ok_transport(
            normalized_value, normalize_code, normalize_heights);
        thm arg_boundary = mp_rule(specl_rule(TERM_LIST(
            `CMCharTy`, `1i`, halt_heights),
            cm_normalize_heights_start), halt_boundary);
        thm direct_stream = conv_rule(
            rewrite_conv(THM_LIST(
              cm_rvalue_heights_def, cm_expr_heights_def,
              cm_rheights_of_def,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
            cm_codegen_stream(leaf, false,
              `CMExitE ${arg:cm_expr} (a1:cm_type)`));
        thm result = cm_expr_codegen_ih(
            leaf, arg, false, `pc:int`, `temp:int`,
            normalize_code, normalize_heights, direct_stream,
            arg_boundary, normalized_value);
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))));
        dest_comb_results desired_height =
            dest_comb(goal_ccl(normalized->g));
        term desired_heights = desired_height.tm2;
        term desired_code =
            dest_comb(desired_height.tm1).tm2;
        result = cm_local_ok_transport(
            result, desired_code, desired_heights);
        ACCEPT_TAC(normalized, result);
        continue;
      }
      if (i == 14) {
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        ACCEPT_TAC(shaped, cm_codegen_tail(leaf));
        continue;
      }
      if (i == 15) {
        term head = `a0:cm_expr`;
        term rest = `a1:(cm_expr)list`;
        term rest_slots = `TL (slots:(cm_slot_d)list)`;
        thm outer_boundary = cm_matching_assumption(leaf,
            `cm_local_next (annotations:(int)list) 0i`);
        thm tail_wf = cm_matching_assumption(leaf,
            `cm_args_wf (p:cm_program) (f:cm_function_d)
               ${rest:(cm_expr)list}
               ${rest_slots:(cm_slot_d)list}`);
        term rest_heights =
            `(cm_args_store_heights (p:cm_program) (fid:int)
                ${rest:(cm_expr)list} ++
              (annotations:(int)list))`;
        term rest_pc =
            `(pc:int) +
             cm_rvalue_code_count (p:cm_program) (fid:int)
               ${head:cm_expr} + 5i`;
        term rest_code =
            `(cm_emit_args_store (p:cm_program) (fid:int)
                ${rest_pc:int} ((slot:int) + 1i)
                (scratch:int) ${rest:(cm_expr)list} ++
              (tail:(tvm_inst)list))`;
        thm whole_stream = cm_matching_assumption(leaf,
            `cm_height_stream (target:int->int) (pc:int)
               (cm_args_store_heights
                  (p:cm_program) (fid:int)
                  (${head:cm_expr} :: ${rest:(cm_expr)list}) ++
                (annotations:(int)list))`);
        thm direct_stream = conv_rule(
            rewrite_conv(THM_LIST(
              cm_expr_heights_def,
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
            whole_stream);
        term head_heights =
            `cm_rheights_of
               (cm_expr_heights (p:cm_program) (fid:int)
                 ${head:cm_expr})`;
        term rest_prefix =
            `(${head_heights:(int)list} ++
              cm_temp_access_heights 1i)`;
        term split_annotations =
            `(${rest_prefix:(int)list} ++
              ${rest_heights:(int)list})`;
        thm split_stream = direct_stream;
        if (alpha_compare(
              cm_stream_annotations(direct_stream),
              split_annotations) != 0) {
          thm old_normal = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"),
                get_theorem_by_name("APPEND_NIL"),
                get_theorem_by_name("APPEND_ASSOC"))),
              cm_stream_annotations(direct_stream));
          thm expected_normal = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"),
                get_theorem_by_name("APPEND_NIL"),
                get_theorem_by_name("APPEND_ASSOC"))),
              split_annotations);
          thm stream_shape = trans_rule(
              old_normal, sym_rule(expected_normal));
          split_stream = cm_stream_relist(
              direct_stream, `pc:int`, stream_shape);
        }
        thm rest_stream = cm_drop_stream_to(
            split_stream, rest_prefix, rest_heights,
            `pc:int`, rest_pc,
            THM_LIST(cm_expr_height_length_fact(
              head, false)));
        thm rest_ok = cm_args_codegen_ih(
            leaf, rest, rest_slots, rest_pc,
            `(slot:int) + 1i`, `scratch:int`,
            `tail:(tvm_inst)list`,
            `annotations:(int)list`,
            rest_stream, outer_boundary,
            cm_codegen_tail(leaf));
        thm rest_start_rule = specl_rule(TERM_LIST(
            `p:cm_program`, `f:cm_function_d`, rest_slots,
            `fid:int`, `annotations:(int)list`),
            spec_rule(rest,
              conjunct2_rule(cm_codegen_height_starts)));
        thm rest_start = mp_rule(mp_rule(
            rest_start_rule, tail_wf), outer_boundary);
        thm store_boundary = eq_mp_rule(
            sym_rule(beta_norm(ap_term_rule(
              `\height:int.
                 cm_local_next ${rest_heights:(int)list} height`,
              int_arith_rule(`1i - 1i == 0i`)))),
            rest_start);
        term stored_heights =
            `(cm_temp_access_heights 1i ++
              ${rest_heights:(int)list})`;
        term stored_code =
            `(cm_temp_store_code (p:cm_program) (fid:int)
                (slot:int) ++
              ${rest_code:(tvm_inst)list})`;
        thm stored = specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`, `fid:int`,
            `slot:int`, `1i`, rest_code, rest_heights),
            cm_local_temp_store);
        stored = mp_rule(mp_rule(mp_rule(
            stored, int_arith_rule(`1i <= 1i`)),
            store_boundary), rest_ok);
        stored = cm_local_ok_transport(
            stored, stored_code, stored_heights);
        thm head_boundary = cm_fixed_local_next(
            stored_heights, `1i`, THM_LIST());
        term head_annotations =
            `(${head_heights:(int)list} ++
              ${stored_heights:(int)list})`;
        thm head_stream = direct_stream;
        if (alpha_compare(
              cm_stream_annotations(direct_stream),
              head_annotations) != 0) {
          thm old_normal = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"),
                get_theorem_by_name("APPEND_NIL"),
                get_theorem_by_name("APPEND_ASSOC"))),
              cm_stream_annotations(direct_stream));
          thm expected_normal = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                get_theorem_by_name("APPEND"),
                get_theorem_by_name("APPEND_NIL"),
                get_theorem_by_name("APPEND_ASSOC"))),
              head_annotations);
          thm stream_shape = trans_rule(
              old_normal, sym_rule(expected_normal));
          head_stream = cm_stream_relist(
              direct_stream, `pc:int`, stream_shape);
        }
        thm result = cm_expr_codegen_ih(
            leaf, head, false, `pc:int`, `scratch:int`,
            stored_code, stored_heights, head_stream,
            head_boundary, stored);
        gnode shaped = cm_shape_codegen_goal(
            leaf, THM_LIST());
        gnode normalized = CONV_TAC(shaped,
            rewrite_conv(THM_LIST(
              gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
              get_theorem_by_name("APPEND"))));
        dest_comb_results desired_height =
            dest_comb(goal_ccl(normalized->g));
        term desired_heights = desired_height.tm2;
        term desired_code =
            dest_comb(desired_height.tm1).tm2;
        result = cm_local_ok_transport(
            result, desired_code, desired_heights);
        ACCEPT_TAC(normalized, result);
        continue;
      }
      ENSURE_COND(false,
          "unfinished expression checker constructor %zu/%zu",
          i, j);
    }
  }
  return gnode_prove(root);
err:
  ERR_FUN_PUTS("cm_prove_expr_local_codegen");
  return empty_theorem;
}
PROOF thm cm_expr_local_codegen =
    cm_prove_expr_local_codegen();


PROOF static thm cm_stmt_start_ih(
    const gnode branch, const term stmt, const term loop,
    const term suffix, const thm boundary) {
  term ih_term =
      `!(p:cm_program) (f:cm_function_d) (loop:bool) fid
          (annotations:(int)list).
         cm_stmt_wf p f loop ${stmt:cm_stmt} ==>
         cm_local_next annotations 0i ==>
         cm_local_next
           (cm_stmt_heights p fid ${stmt:cm_stmt} ++ annotations)
           0i`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, loop, `fid:int`, suffix),
      cm_matching_assumption(branch, ih_term));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_stmt_wf (p:cm_program) (f:cm_function_d)
         ${loop:bool} ${stmt:cm_stmt}`));
  return mp_rule(result, boundary);
}

PROOF static thm cm_local_next_transport(
    const thm next, const term desired_heights,
    const term height) {
  dest_comb_results actual_outer = dest_comb(concl(next));
  term actual_heights = dest_comb(actual_outer.tm1).tm2;
  if (alpha_compare(desired_heights, actual_heights) == 0) {
    return next;
  }
  thm equality = by_rewrite(
      mk_eq(desired_heights, actual_heights),
      THM_LIST(cm_rvalue_heights_def,
        gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL")));
  return eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\heights:(int)list.
         cm_local_next heights ${height:int}`,
      equality))), next);
}

PROOF static thm cm_prove_stmt_height_starts(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt).
         !(p:cm_program) (f:cm_function_d) (loop:bool) fid
           (annotations:(int)list).
         cm_stmt_wf p f loop stmt ==>
         cm_local_next annotations 0i ==>
         cm_local_next
           (cm_stmt_heights p fid stmt ++ annotations) 0i`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode leaf = AUTO_ASMP_DESTRUCT_TAC(constructor)[0];
    leaf = AUTO_INTROS_TAC(leaf);
    if (i == 1 || i == 3 || i == 4 || i == 5 ||
        i == 6 || i == 7 || i == 10) {
      thm wf = cm_predicate_assumption(leaf, "cm_stmt_wf");
      thm parts = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_cm_stmt_wf_def())), wf);
      size_t wf_part = 0;
      leaf = cm_assume_conjunct_leaves(
          leaf, parts, &wf_part);
    }
    thm outer_boundary = cm_matching_assumption(leaf,
        `cm_local_next (annotations:(int)list) 0i`);
    thm result;
    if (i == 0 || i == 2) {
      result = outer_boundary;
    } else if (i == 1) {
      term suffix = `([1i] ++ (annotations:(int)list))`;
      thm boundary = cm_fixed_local_next(
          suffix, `1i`, THM_LIST());
      result = cm_generated_expr_start(
          leaf, `a:cm_expr`, false, suffix, boundary);
    } else if (i == 3) {
      term ty =
          `cm_slot_ty
             (inth (a0:int)
               (cm_function_locals
                 (inth (fid:int)
                   (cm_program_functions (p:cm_program)))))`;
      term store_suffix =
          `(cm_fp_address_heights 1i ++ [2i] ++
            (annotations:(int)list))`;
      thm store_start = cm_fixed_local_next(
          store_suffix, `1i`, THM_LIST());
      term normalize_suffix =
          `(cm_normalize_heights ${ty:cm_type} 1i ++
            ${store_suffix:(int)list})`;
      thm normalize_start = mp_rule(specl_rule(TERM_LIST(
          ty, `1i`, store_suffix),
          cm_normalize_heights_start), store_start);
      result = cm_generated_expr_start(
          leaf, `a1:cm_expr`, false,
          normalize_suffix, normalize_start);
    } else if (i == 4) {
      term second_suffix =
          `(cm_stmt_heights (p:cm_program) (fid:int)
              (a1:cm_stmt) ++
            (annotations:(int)list))`;
      thm second_start = cm_stmt_start_ih(
          leaf, `a1:cm_stmt`, `loop:bool`,
          `annotations:(int)list`, outer_boundary);
      result = cm_stmt_start_ih(
          leaf, `a0:cm_stmt`, `loop:bool`,
          second_suffix, second_start);
    } else if (i == 5) {
      result = cm_stmt_start_ih(
          leaf, `a:cm_stmt`, `loop:bool`,
          `annotations:(int)list`, outer_boundary);
    } else if (i == 6) {
      term suffix =
          `([1i] ++
            cm_stmt_heights (p:cm_program) (fid:int)
              (a1:cm_stmt) ++
            [0i] ++
            cm_stmt_heights p fid (a2:cm_stmt) ++
            (annotations:(int)list))`;
      thm boundary = cm_fixed_local_next(
          suffix, `1i`, THM_LIST());
      result = cm_generated_expr_start(
          leaf, `a0:cm_expr`, false, suffix, boundary);
    } else if (i == 7) {
      term suffix =
          `([1i] ++
            cm_stmt_heights (p:cm_program) (fid:int)
              (a1:cm_stmt) ++
            [0i] ++ (annotations:(int)list))`;
      thm boundary = cm_fixed_local_next(
          suffix, `1i`, THM_LIST());
      result = cm_generated_expr_start(
          leaf, `a0:cm_expr`, false, suffix, boundary);
    } else if (i == 8 || i == 9) {
      result = cm_fixed_local_next(
          `([0i] ++ (annotations:(int)list))`,
          `0i`, THM_LIST());
    } else {
      term ty =
          `cm_function_ret
             (inth (fid:int)
               (cm_program_functions (p:cm_program)))`;
      term return_suffix =
          `(cm_return_heights ++ (annotations:(int)list))`;
      thm return_start = cm_fixed_local_next(
          return_suffix, `1i`, THM_LIST(cm_return_heights_def));
      term normalize_suffix =
          `(cm_normalize_heights ${ty:cm_type} 1i ++
            ${return_suffix:(int)list})`;
      thm normalize_start = mp_rule(specl_rule(TERM_LIST(
          ty, `1i`, return_suffix),
          cm_normalize_heights_start), return_start);
      result = cm_generated_expr_start(
          leaf, `a:cm_expr`, false,
          normalize_suffix, normalize_start);
    }
    gnode shaped = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          cm_stmt_heights_def,
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL"))));
    gnode normalized = CONV_TAC(shaped,
        rewrite_conv(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")))));
    gnode fully_normalized = CONV_TAC(normalized,
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL"))));
    dest_comb_results desired_outer =
        dest_comb(goal_ccl(fully_normalized->g));
    term desired_heights =
        dest_comb(desired_outer.tm1).tm2;
    ACCEPT_TAC(fully_normalized, cm_local_next_transport(
        result, desired_heights, `0i`));
  }
  return gnode_prove(root);
}
PROOF thm cm_stmt_height_starts =
    cm_prove_stmt_height_starts();

PROOF static thm cm_stream_expected(
    const thm stream, const term pc,
    const term expected_annotations) {
  term actual_annotations = cm_stream_annotations(stream);
  if (alpha_compare(actual_annotations, expected_annotations) == 0) {
    return stream;
  }
  thm_list rules = THM_LIST(
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("APPEND_ASSOC"));
  thm actual_normal = apply_conversion(
      reduce_rewrite_conv(rules), actual_annotations);
  thm expected_normal = apply_conversion(
      reduce_rewrite_conv(rules), expected_annotations);
  thm equality = trans_rule(
      actual_normal, sym_rule(expected_normal));
  return cm_stream_relist(stream, pc, equality);
}

PROOF static thm cm_expr_local_apply(
    const gnode branch, const term expr,
    const term pc, const term temp,
    const term tail, const term annotations,
    const thm stream, const thm boundary,
    const thm tail_ok) {
  thm property = conjunct1_rule(
      spec_rule(expr, conjunct1_rule(cm_expr_local_codegen)));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, `fid:int`,
      pc, temp, `target:int->int`, tail, annotations),
      property);
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
         ${expr:cm_expr}`));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_function_target_heights
         (p:cm_program) (target:int->int)`));
  result = mp_rule(result, stream);
  result = mp_rule(result, boundary);
  result = mp_rule(result, tail_ok);
  return conv_rule(rewrite_conv(THM_LIST(
      get_cm_emit_rvalue_def(), cm_rvalue_heights_def)), result);
}

PROOF static thm cm_stmt_codegen_ih(
    const gnode branch, const term stmt, const term loop,
    const term pc, const term temp,
    const term breakpc, const term continuepc,
    const term tail, const term annotations,
    const thm stream, const thm break_target,
    const thm continue_target, const thm boundary,
    const thm tail_ok) {
  term ih_term =
      `!(p:cm_program) (f:cm_function_d) (loop:bool)
          fid pc temp (target:int->int) breakpc continuepc
          (tail:(tvm_inst)list) (annotations:(int)list).
         cm_stmt_wf p f loop ${stmt:cm_stmt} ==>
         cm_function_target_heights p target ==>
         cm_height_stream target pc
           (cm_stmt_heights p fid ${stmt:cm_stmt} ++ annotations) ==>
         target breakpc == 0i ==>
         target continuepc == 0i ==>
         cm_local_next annotations 0i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_stmt p fid pc temp breakpc continuepc
              ${stmt:cm_stmt} ++ tail)
           (cm_stmt_heights p fid ${stmt:cm_stmt} ++
            annotations)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, loop,
      `fid:int`, pc, temp, `target:int->int`,
      breakpc, continuepc, tail, annotations),
      cm_matching_assumption(branch, ih_term));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_stmt_wf (p:cm_program) (f:cm_function_d)
         ${loop:bool} ${stmt:cm_stmt}`));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_function_target_heights
         (p:cm_program) (target:int->int)`));
  result = mp_rule(result, stream);
  result = mp_rule(result, break_target);
  result = mp_rule(result, continue_target);
  result = mp_rule(result, boundary);
  return mp_rule(result, tail_ok);
}

PROOF static thm cm_stmt_height_length_fact(
    const term stmt) {
  return specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`),
      spec_rule(stmt, cm_stmt_height_length));
}

PROOF static gnode cm_shape_stmt_goal(
    const gnode branch, const thm_list extra_rules) {
  thm_list rules = THM_LIST(
      get_cm_emit_stmt_def(), cm_stmt_heights_def);
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  return cm_shape_codegen_goal(branch, rules);
}

PROOF static thm cm_prove_stmt_local_codegen(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt).
         !(p:cm_program) (f:cm_function_d) (loop:bool)
           fid pc temp (target:int->int) breakpc continuepc
           (tail:(tvm_inst)list) (annotations:(int)list).
         cm_stmt_wf p f loop stmt ==>
         cm_function_target_heights p target ==>
         cm_height_stream target pc
           (cm_stmt_heights p fid stmt ++ annotations) ==>
         target breakpc == 0i ==>
         target continuepc == 0i ==>
         cm_local_next annotations 0i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_stmt p fid pc temp breakpc continuepc stmt ++
            tail)
           (cm_stmt_heights p fid stmt ++ annotations)`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode leaf = AUTO_ASMP_DESTRUCT_TAC(constructor)[0];
    leaf = AUTO_INTROS_TAC(leaf);
    if (i == 1 || i == 3 || i == 4 || i == 5 ||
        i == 6 || i == 7 || i == 10) {
      thm wf = cm_predicate_assumption(leaf, "cm_stmt_wf");
      thm parts = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_cm_stmt_wf_def())), wf);
      size_t wf_part = 0;
      leaf = cm_assume_conjunct_leaves(
          leaf, parts, &wf_part);
    }
    thm outer_boundary = cm_matching_assumption(leaf,
        `cm_local_next (annotations:(int)list) 0i`);
    thm outer_tail = cm_codegen_tail(leaf);
    thm break_target = cm_matching_assumption(leaf,
        `(target:int->int) (breakpc:int) == 0i`);
    thm continue_target = cm_matching_assumption(leaf,
        `(target:int->int) (continuepc:int) == 0i`);
    term constructor_stmts[11] = {
      `CMSkipS:cm_stmt`,
      `CMExprS (a:cm_expr)`,
      `CMDeclS (a:int)`,
      `CMInitS (a0:int) (a1:cm_expr)`,
      `CMSeqS (a0:cm_stmt) (a1:cm_stmt)`,
      `CMBlockS (a:cm_stmt)`,
      `CMIfS (a0:cm_expr) (a1:cm_stmt) (a2:cm_stmt)`,
      `CMWhileS (a0:cm_expr) (a1:cm_stmt)`,
      `CMBreakS:cm_stmt`,
      `CMContinueS:cm_stmt`,
      `CMReturnS (a:cm_expr)`
    };
    term current_stmt = constructor_stmts[i];
    thm whole_stream = cm_matching_assumption(leaf,
        `cm_height_stream (target:int->int) (pc:int)
           (cm_stmt_heights (p:cm_program) (fid:int)
              ${current_stmt:cm_stmt} ++
            (annotations:(int)list))`);
    thm result;
    if (i == 0 || i == 2) {
      result = outer_tail;
    } else if (i == 1) {
      term pop_heights =
          `([1i] ++ (annotations:(int)list))`;
      term pop_code =
          `([TVMInst TVMPopOp 0i] ++
            (tail:(tvm_inst)list))`;
      thm popped = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMPopOp 0i]`, `[1i]`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`,
          outer_tail, outer_boundary, THM_LIST());
      popped = cm_local_ok_transport(
          popped, pop_code, pop_heights);
      thm expr_boundary = cm_fixed_local_next(
          pop_heights, `1i`, THM_LIST());
      thm direct_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      direct_stream = cm_stream_expected(
          direct_stream, `pc:int`,
          `(cm_rvalue_heights (p:cm_program) (fid:int)
              (a:cm_expr) ++ ${pop_heights:(int)list})`);
      result = cm_expr_local_apply(
          leaf, `a:cm_expr`, `pc:int`, `temp:int`,
          pop_code, pop_heights, direct_stream,
          expr_boundary, popped);
    } else if (i == 3) {
      term ty =
          `cm_slot_ty
             (inth (a0:int)
               (cm_function_locals
                 (inth (fid:int)
                   (cm_program_functions (p:cm_program)))))`;
      term store_heights =
          `([2i] ++ (annotations:(int)list))`;
      term store_code =
          `(cm_store_code ${ty:cm_type} ++
            (tail:(tvm_inst)list))`;
      thm store_boundary = eq_mp_rule(
          sym_rule(beta_norm(ap_term_rule(
            `\height:int.
               cm_local_next (annotations:(int)list) height`,
            int_arith_rule(`2i - 2i == 0i`)))),
          outer_boundary);
      thm stored = specl_rule(TERM_LIST(
          `p:cm_program`, `target:int->int`, ty, `2i`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`), cm_local_store);
      stored = mp_rule(mp_rule(mp_rule(
          stored, int_arith_rule(`2i <= 2i`)),
          store_boundary), outer_tail);
      stored = cm_local_ok_transport(
          stored, store_code, store_heights);
      term address_heights =
          `(cm_fp_address_heights 1i ++
            ${store_heights:(int)list})`;
      term address_code =
          `(cm_fp_relative_address_code
              (cm_local_offset (p:cm_program) (fid:int)
                (a0:int)) ++
            ${store_code:(tvm_inst)list})`;
      thm address_boundary = cm_fixed_local_next(
          store_heights, `2i`, THM_LIST());
      thm address_required = eq_mp_rule(
          sym_rule(beta_norm(ap_term_rule(
            `\height:int.
               cm_local_next ${store_heights:(int)list} height`,
            int_arith_rule(`1i + 1i == 2i`)))),
          address_boundary);
      thm addressed = specl_rule(TERM_LIST(
          `p:cm_program`, `target:int->int`,
          `cm_local_offset (p:cm_program) (fid:int) (a0:int)`,
          `1i`, store_code, store_heights),
          cm_local_fp_address);
      addressed = mp_rule(mp_rule(mp_rule(
          addressed, int_arith_rule(`0i <= 1i`)),
          address_required), stored);
      addressed = cm_local_ok_transport(
          addressed, address_code, address_heights);
      thm normalize_boundary = cm_fixed_local_next(
          address_heights, `1i`, THM_LIST());
      term normalize_heights =
          `(cm_normalize_heights ${ty:cm_type} 1i ++
            ${address_heights:(int)list})`;
      term normalize_code =
          `(cm_char_normalize_code ${ty:cm_type} ++
            ${address_code:(tvm_inst)list})`;
      thm normalized_value = specl_rule(TERM_LIST(
          `p:cm_program`, `target:int->int`, ty, `1i`,
          address_code, address_heights),
          cm_local_char_normalize);
      normalized_value = mp_rule(mp_rule(mp_rule(
          normalized_value, int_arith_rule(`1i <= 1i`)),
          normalize_boundary), addressed);
      normalized_value = cm_local_ok_transport(
          normalized_value, normalize_code, normalize_heights);
      thm expr_boundary = mp_rule(specl_rule(TERM_LIST(
          ty, `1i`, address_heights),
          cm_normalize_heights_start), normalize_boundary);
      thm direct_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      direct_stream = cm_stream_expected(
          direct_stream, `pc:int`,
          `(cm_rvalue_heights (p:cm_program) (fid:int)
              (a1:cm_expr) ++
            ${normalize_heights:(int)list})`);
      result = cm_expr_local_apply(
          leaf, `a1:cm_expr`, `pc:int`, `temp:int`,
          normalize_code, normalize_heights, direct_stream,
          expr_boundary, normalized_value);
    } else if (i == 4) {
      term first = `a0:cm_stmt`;
      term second = `a1:cm_stmt`;
      term second_heights =
          `(cm_stmt_heights (p:cm_program) (fid:int)
              ${second:cm_stmt} ++
            (annotations:(int)list))`;
      term second_pc =
          `(pc:int) +
           cm_stmt_code_count (p:cm_program) (fid:int)
             ${first:cm_stmt}`;
      term second_code =
          `(cm_emit_stmt (p:cm_program) (fid:int)
              ${second_pc:int} (temp:int) (breakpc:int)
              (continuepc:int) ${second:cm_stmt} ++
            (tail:(tvm_inst)list))`;
      thm direct_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      term first_heights =
          `cm_stmt_heights (p:cm_program) (fid:int)
             ${first:cm_stmt}`;
      term split_annotations =
          `(${first_heights:(int)list} ++
            ${second_heights:(int)list})`;
      thm split_stream = cm_stream_expected(
          direct_stream, `pc:int`, split_annotations);
      thm second_stream = cm_drop_stream_to(
          split_stream, first_heights, second_heights,
          `pc:int`, second_pc,
          THM_LIST(cm_stmt_height_length_fact(first)));
      thm second_ok = cm_stmt_codegen_ih(
          leaf, second, `loop:bool`, second_pc, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`, second_stream,
          break_target, continue_target,
          outer_boundary, outer_tail);
      thm second_start = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `loop:bool`,
          `fid:int`, `annotations:(int)list`),
          spec_rule(second, cm_stmt_height_starts)),
          cm_matching_assumption(leaf,
            `cm_stmt_wf (p:cm_program) (f:cm_function_d)
               (loop:bool) ${second:cm_stmt}`)),
          outer_boundary);
      result = cm_stmt_codegen_ih(
          leaf, first, `loop:bool`, `pc:int`, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          second_code, second_heights, split_stream,
          break_target, continue_target,
          second_start, second_ok);
    } else if (i == 5) {
      thm body_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      result = cm_stmt_codegen_ih(
          leaf, `a:cm_stmt`, `loop:bool`, `pc:int`,
          `temp:int`, `breakpc:int`, `continuepc:int`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`, body_stream,
          break_target, continue_target,
          outer_boundary, outer_tail);
    } else if (i == 6) {
      term guard = `a0:cm_expr`;
      term yes = `a1:cm_stmt`;
      term no = `a2:cm_stmt`;
      term guard_heights =
          `cm_rvalue_heights (p:cm_program) (fid:int)
             ${guard:cm_expr}`;
      term yes_fragment =
          `cm_stmt_heights (p:cm_program) (fid:int)
             ${yes:cm_stmt}`;
      term no_heights =
          `(cm_stmt_heights (p:cm_program) (fid:int)
              ${no:cm_stmt} ++
            (annotations:(int)list))`;
      term jump_heights =
          `([0i] ++ ${no_heights:(int)list})`;
      term yes_heights =
          `(${yes_fragment:(int)list} ++
            ${jump_heights:(int)list})`;
      term branch_heights =
          `([1i] ++ ${yes_heights:(int)list})`;
      term full_heights =
          `(${guard_heights:(int)list} ++
            ${branch_heights:(int)list})`;
      term yes_pc =
          `(pc:int) +
           cm_rvalue_code_count (p:cm_program) (fid:int)
             ${guard:cm_expr} + 1i`;
      term no_pc =
          `(pc:int) +
           cm_rvalue_code_count (p:cm_program) (fid:int)
             ${guard:cm_expr} + 1i +
           cm_stmt_code_count p fid ${yes:cm_stmt} + 1i`;
      term end_pc =
          `(pc:int) +
           cm_stmt_code_count (p:cm_program) (fid:int)
             (CMIfS ${guard:cm_expr} ${yes:cm_stmt}
               ${no:cm_stmt})`;
      term no_code =
          `(cm_emit_stmt (p:cm_program) (fid:int)
              ${no_pc:int} (temp:int) (breakpc:int)
              (continuepc:int) ${no:cm_stmt} ++
            (tail:(tvm_inst)list))`;
      term jump_code =
          `([TVMInst TVMJmpOp ${end_pc:int}] ++
            ${no_code:(tvm_inst)list})`;
      term yes_code =
          `(cm_emit_stmt (p:cm_program) (fid:int)
              ${yes_pc:int} (temp:int) (breakpc:int)
              (continuepc:int) ${yes:cm_stmt} ++
            ${jump_code:(tvm_inst)list})`;
      term branch_code =
          `([TVMInst TVMJzOp ${no_pc:int}] ++
            ${yes_code:(tvm_inst)list})`;
      thm direct_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      direct_stream = cm_stream_expected(
          direct_stream, `pc:int`, full_heights);
      term yes_prefix =
          `(${guard_heights:(int)list} ++ [1i])`;
      thm yes_split_stream = cm_stream_expected(
          direct_stream, `pc:int`,
          `(${yes_prefix:(int)list} ++
            ${yes_heights:(int)list})`);
      thm yes_stream = cm_drop_stream_to(
          yes_split_stream, yes_prefix, yes_heights,
          `pc:int`, yes_pc,
          THM_LIST(cm_expr_height_length_fact(
            guard, false)));
      term no_prefix =
          `(${guard_heights:(int)list} ++ [1i] ++
            ${yes_fragment:(int)list} ++ [0i])`;
      thm no_split_stream = cm_stream_expected(
          direct_stream, `pc:int`,
          `(${no_prefix:(int)list} ++
            ${no_heights:(int)list})`);
      thm no_stream = cm_drop_stream_to(
          no_split_stream, no_prefix, no_heights,
          `pc:int`, no_pc,
          THM_LIST(cm_expr_height_length_fact(
              guard, false),
            cm_stmt_height_length_fact(yes)));
      thm end_stream = cm_drop_stream_to(
          whole_stream,
          `cm_stmt_heights (p:cm_program) (fid:int)
             (CMIfS ${guard:cm_expr} ${yes:cm_stmt}
               ${no:cm_stmt})`,
          `annotations:(int)list`, `pc:int`, end_pc,
          THM_LIST(cm_stmt_height_length_fact(
            `CMIfS ${guard:cm_expr} ${yes:cm_stmt}
               ${no:cm_stmt}`)));
      thm end_target = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `target:int->int`, end_pc,
          `annotations:(int)list`, `0i`),
          cm_stream_local_next), end_stream), outer_boundary);
      thm no_start = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `loop:bool`,
          `fid:int`, `annotations:(int)list`),
          spec_rule(no, cm_stmt_height_starts)),
          cm_matching_assumption(leaf,
            `cm_stmt_wf (p:cm_program) (f:cm_function_d)
               (loop:bool) ${no:cm_stmt}`)),
          outer_boundary);
      thm no_target = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `target:int->int`, no_pc, no_heights, `0i`),
          cm_stream_local_next), no_stream), no_start);
      thm no_ok = cm_stmt_codegen_ih(
          leaf, no, `loop:bool`, no_pc, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`, no_stream,
          break_target, continue_target,
          outer_boundary, outer_tail);
      thm jumped = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMJmpOp ${end_pc:int}]`, `[0i]`,
          no_code, no_heights, no_ok, no_start,
          THM_LIST(end_target));
      jumped = cm_local_ok_transport(
          jumped, jump_code, jump_heights);
      thm jump_start = cm_fixed_local_next(
          jump_heights, `0i`, THM_LIST());
      thm yes_start = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `loop:bool`,
          `fid:int`, jump_heights),
          spec_rule(yes, cm_stmt_height_starts)),
          cm_matching_assumption(leaf,
            `cm_stmt_wf (p:cm_program) (f:cm_function_d)
               (loop:bool) ${yes:cm_stmt}`)),
          jump_start);
      thm yes_ok = cm_stmt_codegen_ih(
          leaf, yes, `loop:bool`, yes_pc, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          jump_code, jump_heights, yes_stream,
          break_target, continue_target,
          jump_start, jumped);
      thm branched = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMJzOp ${no_pc:int}]`, `[1i]`,
          yes_code, yes_heights, yes_ok, yes_start,
          THM_LIST(no_target));
      branched = cm_local_ok_transport(
          branched, branch_code, branch_heights);
      thm guard_boundary = cm_fixed_local_next(
          branch_heights, `1i`, THM_LIST());
      result = cm_expr_local_apply(
          leaf, guard, `pc:int`, `temp:int`,
          branch_code, branch_heights, direct_stream,
          guard_boundary, branched);
    } else if (i == 7) {
      term guard = `a0:cm_expr`;
      term body = `a1:cm_stmt`;
      term guard_heights =
          `cm_rvalue_heights (p:cm_program) (fid:int)
             ${guard:cm_expr}`;
      term body_fragment =
          `cm_stmt_heights (p:cm_program) (fid:int)
             ${body:cm_stmt}`;
      term jump_heights =
          `([0i] ++ (annotations:(int)list))`;
      term body_heights =
          `(${body_fragment:(int)list} ++
            ${jump_heights:(int)list})`;
      term branch_heights =
          `([1i] ++ ${body_heights:(int)list})`;
      term full_heights =
          `(${guard_heights:(int)list} ++
            ${branch_heights:(int)list})`;
      term body_pc =
          `(pc:int) +
           cm_rvalue_code_count (p:cm_program) (fid:int)
             ${guard:cm_expr} + 1i`;
      term end_pc =
          `(pc:int) +
           cm_stmt_code_count (p:cm_program) (fid:int)
             (CMWhileS ${guard:cm_expr} ${body:cm_stmt})`;
      term jump_code =
          `([TVMInst TVMJmpOp (pc:int)] ++
            (tail:(tvm_inst)list))`;
      term body_code =
          `(cm_emit_stmt (p:cm_program) (fid:int)
              ${body_pc:int} (temp:int) ${end_pc:int}
              (pc:int) ${body:cm_stmt} ++
            ${jump_code:(tvm_inst)list})`;
      term branch_code =
          `([TVMInst TVMJzOp ${end_pc:int}] ++
            ${body_code:(tvm_inst)list})`;
      thm direct_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      direct_stream = cm_stream_expected(
          direct_stream, `pc:int`, full_heights);
      term body_prefix =
          `(${guard_heights:(int)list} ++ [1i])`;
      thm body_split_stream = cm_stream_expected(
          direct_stream, `pc:int`,
          `(${body_prefix:(int)list} ++
            ${body_heights:(int)list})`);
      thm body_stream = cm_drop_stream_to(
          body_split_stream, body_prefix, body_heights,
          `pc:int`, body_pc,
          THM_LIST(cm_expr_height_length_fact(
            guard, false)));
      thm end_stream = cm_drop_stream_to(
          whole_stream,
          `cm_stmt_heights (p:cm_program) (fid:int)
             (CMWhileS ${guard:cm_expr} ${body:cm_stmt})`,
          `annotations:(int)list`, `pc:int`, end_pc,
          THM_LIST(cm_stmt_height_length_fact(
            `CMWhileS ${guard:cm_expr} ${body:cm_stmt}`)));
      thm end_target = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `target:int->int`, end_pc,
          `annotations:(int)list`, `0i`),
          cm_stream_local_next), end_stream), outer_boundary);
      thm loop_start = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `loop:bool`,
          `fid:int`, `annotations:(int)list`),
          spec_rule(
            `CMWhileS ${guard:cm_expr} ${body:cm_stmt}`,
            cm_stmt_height_starts)),
          cm_matching_assumption(leaf,
            `cm_stmt_wf (p:cm_program) (f:cm_function_d)
               (loop:bool)
               (CMWhileS ${guard:cm_expr} ${body:cm_stmt})`)),
          outer_boundary);
      thm loop_target = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `target:int->int`, `pc:int`,
          `cm_stmt_heights (p:cm_program) (fid:int)
             (CMWhileS ${guard:cm_expr} ${body:cm_stmt}) ++
           (annotations:(int)list)`,
          `0i`), cm_stream_local_next),
          whole_stream), loop_start);
      thm jumped = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMJmpOp (pc:int)]`, `[0i]`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`,
          outer_tail, outer_boundary,
          THM_LIST(loop_target));
      jumped = cm_local_ok_transport(
          jumped, jump_code, jump_heights);
      thm jump_start = cm_fixed_local_next(
          jump_heights, `0i`, THM_LIST());
      thm body_start = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `T`,
          `fid:int`, jump_heights),
          spec_rule(body, cm_stmt_height_starts)),
          cm_matching_assumption(leaf,
            `cm_stmt_wf (p:cm_program) (f:cm_function_d)
               T ${body:cm_stmt}`)),
          jump_start);
      thm body_ok = cm_stmt_codegen_ih(
          leaf, body, `T`, body_pc, `temp:int`,
          end_pc, `pc:int`, jump_code, jump_heights,
          body_stream, end_target, loop_target,
          jump_start, jumped);
      thm branched = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMJzOp ${end_pc:int}]`, `[1i]`,
          body_code, body_heights, body_ok, body_start,
          THM_LIST(end_target));
      branched = cm_local_ok_transport(
          branched, branch_code, branch_heights);
      thm guard_boundary = cm_fixed_local_next(
          branch_heights, `1i`, THM_LIST());
      result = cm_expr_local_apply(
          leaf, guard, `pc:int`, `temp:int`,
          branch_code, branch_heights, direct_stream,
          guard_boundary, branched);
    } else if (i == 8) {
      result = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMJmpOp (breakpc:int)]`, `[0i]`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`,
          outer_tail, outer_boundary,
          THM_LIST(break_target));
    } else if (i == 9) {
      result = cm_local_fixed(
          `p:cm_program`, `target:int->int`,
          `[TVMInst TVMJmpOp (continuepc:int)]`, `[0i]`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`,
          outer_tail, outer_boundary,
          THM_LIST(continue_target));
    } else if (i == 10) {
      term expr = `a:cm_expr`;
      term ty =
          `cm_function_ret
             (inth (fid:int)
               (cm_program_functions (p:cm_program)))`;
      term return_code =
          `(cm_return_epilogue ++ (tail:(tvm_inst)list))`;
      term return_heights =
          `(cm_return_heights ++
            (annotations:(int)list))`;
      term normalize_code =
          `(cm_char_normalize_code ${ty:cm_type} ++
            ${return_code:(tvm_inst)list})`;
      term normalize_heights =
          `(cm_normalize_heights ${ty:cm_type} 1i ++
            ${return_heights:(int)list})`;
      thm returned = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `target:int->int`,
          `tail:(tvm_inst)list`,
          `annotations:(int)list`),
          cm_local_return_epilogue), outer_tail);
      thm return_start = cm_fixed_local_next(
          return_heights, `1i`,
          THM_LIST(cm_return_heights_def));
      thm normalized = mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `target:int->int`,
            ty, `1i`, return_code, return_heights),
            cm_local_char_normalize),
          int_arith_rule(`1i <= 1i`)),
          return_start), returned);
      thm normalize_start = mp_rule(specl_rule(
          TERM_LIST(ty, `1i`, return_heights),
          cm_normalize_heights_start), return_start);
      thm direct_stream = conv_rule(
          rewrite_conv(THM_LIST(cm_stmt_heights_def)),
          whole_stream);
      direct_stream = cm_stream_expected(
          direct_stream, `pc:int`,
          `(cm_rvalue_heights (p:cm_program) (fid:int)
              ${expr:cm_expr} ++
            ${normalize_heights:(int)list})`);
      result = cm_expr_local_apply(
          leaf, expr, `pc:int`, `temp:int`,
          normalize_code, normalize_heights,
          direct_stream, normalize_start, normalized);
    } else {
      ENSURE_COND(false,
          "unfinished statement checker constructor %zu", i);
    }
    gnode shaped = cm_shape_stmt_goal(
        leaf, THM_LIST());
    gnode normalized = CONV_TAC(shaped,
        rewrite_conv(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
          get_theorem_by_name("APPEND"))));
    dest_comb_results desired_height =
        dest_comb(goal_ccl(normalized->g));
    term desired_heights = desired_height.tm2;
    term desired_code =
        dest_comb(desired_height.tm1).tm2;
    result = cm_local_ok_transport(
        result, desired_code, desired_heights);
    ACCEPT_TAC(normalized, result);
  }
  return gnode_prove(root);
err:
  ERR_FUN_PUTS("cm_prove_stmt_local_codegen");
  return empty_theorem;
}
PROOF thm cm_stmt_local_codegen =
    cm_prove_stmt_local_codegen();

PROOF static thm cm_prove_local_param_stores(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list).
         !(p:cm_program) (target:int->int) fid slot height
           (tail:(tvm_inst)list) (annotations:(int)list).
         ilength params <= height ==>
         cm_local_next annotations
           (height - ilength params) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_param_stores p fid slot params ++ tail)
           (cm_param_store_heights params height ++ annotations)`);
  gnode_list cases =
      INDUCT_TAC(root, `params:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm tail_ok = cm_matching_assumption(leaf,
        `cm_local_codegen_ok (p:cm_program) (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list)`);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_param_stores_def(),
          cm_param_store_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, tail_ok);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bound = cm_matching_assumption(leaf,
        `ilength ((a0:cm_slot_d) ::
           (a1:(cm_slot_d)list)) <= (height:int)`);
    thm outer_boundary = cm_matching_assumption(leaf,
        `cm_local_next (annotations:(int)list)
           ((height:int) -
             ilength ((a0:cm_slot_d) ::
               (a1:(cm_slot_d)list)))`);
    thm outer_tail = cm_matching_assumption(leaf,
        `cm_local_codegen_ok (p:cm_program) (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list)`);
    thm ih = cm_matching_assumption(leaf,
        `!(p:cm_program) (target:int->int) fid slot height
           (tail:(tvm_inst)list) (annotations:(int)list).
           ilength (a1:(cm_slot_d)list) <= height ==>
           cm_local_next annotations
             (height - ilength a1) ==>
           cm_local_codegen_ok p target tail annotations ==>
           cm_local_codegen_ok p target
             (cm_emit_param_stores p fid slot a1 ++ tail)
             (cm_param_store_heights a1 height ++ annotations)`);
    thm cons_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_slot_d) ::
          (a1:(cm_slot_d)list))`);
    thm facts = conj_rule(bound, cons_length);
    term current =
        `(height:int) - ilength (a1:(cm_slot_d)list)`;
    thm current_lower = mp_rule(int_arith_rule(mk_imp(
        concl(facts), `1i <= ${current:int}`)), facts);
    thm current_nonnegative = mp_rule(
        int_arith_rule(mk_imp(
          concl(current_lower), `0i <= ${current:int}`)),
        current_lower);
    thm rest_bound = mp_rule(int_arith_rule(mk_imp(
        concl(facts),
        `ilength (a1:(cm_slot_d)list) <= (height:int)`)),
        facts);
    thm end_height = mp_rule(int_arith_rule(mk_imp(
        concl(cons_length),
        `(${current:int} + 1i) - 2i ==
         (height:int) -
           ilength ((a0:cm_slot_d) ::
             (a1:(cm_slot_d)list))`)),
        cons_length);
    thm store_boundary = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
        `\next_height:int.
           cm_local_next (annotations:(int)list) next_height`,
        end_height))), outer_boundary);
    term ty = `cm_slot_ty (a0:cm_slot_d)`;
    term store_code =
        `(cm_store_code ${ty:cm_type} ++
          (tail:(tvm_inst)list))`;
    term store_heights =
        `([${current:int} + 1i] ++
          (annotations:(int)list))`;
    thm stored = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `target:int->int`, ty,
          `${current:int} + 1i`, `tail:(tvm_inst)list`,
          `annotations:(int)list`),
        cm_local_store),
        mp_rule(int_arith_rule(mk_imp(
          concl(current_lower),
          `2i <= (${current:int} + 1i)`)),
          current_lower)), store_boundary), outer_tail);
    stored = cm_local_ok_transport(
        stored, store_code, store_heights);
    thm store_start = cm_fixed_local_next(
        store_heights, `${current:int} + 1i`, THM_LIST());
    term address_code =
        `(cm_fp_relative_address_code
            (cm_param_offset (p:cm_program) (fid:int) (slot:int)) ++
          ${store_code:(tvm_inst)list})`;
    term address_heights =
        `(cm_fp_address_heights ${current:int} ++
          ${store_heights:(int)list})`;
    thm addressed = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `target:int->int`,
          `cm_param_offset (p:cm_program) (fid:int) (slot:int)`,
          current, store_code, store_heights),
        cm_local_fp_address), current_nonnegative),
        store_start), stored);
    thm address_start = cm_fixed_local_next(
        address_heights, current,
        THM_LIST(cm_fp_address_heights_def));
    term current_code =
        `(cm_char_normalize_code ${ty:cm_type} ++
          ${address_code:(tvm_inst)list})`;
    term current_heights =
        `(cm_normalize_heights ${ty:cm_type} ${current:int} ++
          ${address_heights:(int)list})`;
    thm normalized = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `target:int->int`, ty,
          current, address_code, address_heights),
        cm_local_char_normalize), current_lower),
        address_start), addressed);
    thm current_start = mp_rule(specl_rule(
        TERM_LIST(ty, current, address_heights),
        cm_normalize_heights_start), address_start);
    thm recursive = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `target:int->int`,
          `fid:int`, `(slot:int) + 1i`, `height:int`,
          current_code, current_heights), ih),
        rest_bound), current_start), normalized);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_param_stores_def(),
          cm_param_store_heights_def,
          get_theorem_by_name("APPEND_ASSOC"))));
    ACCEPT_TAC(reduced, conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"))), recursive));
  }
  return gnode_prove(root);
}
PROOF thm cm_local_param_stores =
    cm_prove_local_param_stores();

PROOF static thm cm_prove_param_store_heights_start(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list). !height
         (annotations:(int)list).
         ilength params <= height ==>
         cm_local_next annotations
           (height - ilength params) ==>
         cm_local_next
           (cm_param_store_heights params height ++ annotations)
           height`);
  gnode_list cases =
      INDUCT_TAC(root, `params:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm boundary = cm_matching_assumption(leaf,
        `cm_local_next (annotations:(int)list)
           ((height:int) -
             ilength ([]:(cm_slot_d)list))`);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          cm_param_store_heights_def,
          get_theorem_by_name("ILENGTH_DEF"),
          get_theorem_by_name("APPEND"))));
    thm nil_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ([]:(cm_slot_d)list)`);
    thm index = mp_rule(int_arith_rule(mk_imp(
        concl(nil_length),
        `(height:int) - ilength ([]:(cm_slot_d)list) ==
         height`)), nil_length);
    thm exact = eq_mp_rule(beta_norm(ap_term_rule(
        `\next_height:int.
           cm_local_next (annotations:(int)list) next_height`,
        index)), boundary);
    ACCEPT_TAC(reduced, exact);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bound = cm_matching_assumption(leaf,
        `ilength ((a0:cm_slot_d) ::
           (a1:(cm_slot_d)list)) <= (height:int)`);
    thm ih = cm_matching_assumption(leaf,
        `!height (annotations:(int)list).
           ilength (a1:(cm_slot_d)list) <= height ==>
           cm_local_next annotations
             (height - ilength a1) ==>
           cm_local_next
             (cm_param_store_heights a1 height ++ annotations)
             height`);
    thm cons_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_slot_d) ::
          (a1:(cm_slot_d)list))`);
    thm facts = conj_rule(bound, cons_length);
    term current =
        `(height:int) - ilength (a1:(cm_slot_d)list)`;
    thm rest_bound = mp_rule(int_arith_rule(mk_imp(
        concl(facts),
        `ilength (a1:(cm_slot_d)list) <= (height:int)`)),
        facts);
    term store_heights =
        `([${current:int} + 1i] ++
          (annotations:(int)list))`;
    term address_heights =
        `(cm_fp_address_heights ${current:int} ++
          ${store_heights:(int)list})`;
    thm address_start = cm_fixed_local_next(
        address_heights, current,
        THM_LIST(cm_fp_address_heights_def));
    term current_heights =
        `(cm_normalize_heights (cm_slot_ty (a0:cm_slot_d))
            ${current:int} ++
          ${address_heights:(int)list})`;
    thm current_start = mp_rule(specl_rule(
        TERM_LIST(`cm_slot_ty (a0:cm_slot_d)`,
          current, address_heights),
        cm_normalize_heights_start), address_start);
    thm recursive = mp_rule(mp_rule(specl_rule(
        TERM_LIST(`height:int`, current_heights), ih),
        rest_bound), current_start);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          cm_param_store_heights_def,
          get_theorem_by_name("APPEND_ASSOC"))));
    ACCEPT_TAC(reduced, conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"))), recursive));
  }
  return gnode_prove(root);
}
PROOF thm cm_param_store_heights_start =
    cm_prove_param_store_heights_start();

PROOF static thm cm_prove_local_prologue(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) fid
         (tail:(tvm_inst)list) (annotations:(int)list).
         cm_local_next annotations 0i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_prologue p fid ++ tail)
           (cm_prologue_heights
              (inth fid (cm_program_functions p)) ++
            annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm outer_boundary = cm_matching_assumption(leaf,
      `cm_local_next (annotations:(int)list) 0i`);
  thm outer_tail = cm_matching_assumption(leaf,
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  term actual =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term params = `cm_function_params ${actual:cm_function_d}`;
  term arity = `ilength ${params:(cm_slot_d)list}`;
  term param_code =
      `(cm_emit_param_stores (p:cm_program) (fid:int) 0i
          ${params:(cm_slot_d)list} ++
        (tail:(tvm_inst)list))`;
  term param_heights =
      `(cm_param_store_heights ${params:(cm_slot_d)list}
          ${arity:int} ++
        (annotations:(int)list))`;
  thm arity_nonnegative = ispec_rule(
      params, get_theorem_by_name("ILENGTH_NONNEG"));
  thm arity_end = int_arith_rule(
      `(${arity:int}) - ${arity:int} == 0i`);
  thm param_boundary = eq_mp_rule(sym_rule(beta_norm(
      ap_term_rule(
        `\next_height:int.
           cm_local_next (annotations:(int)list) next_height`,
        arity_end))), outer_boundary);
  thm params_ok = mp_rule(mp_rule(mp_rule(specl_rule(
      TERM_LIST(params, `p:cm_program`, `target:int->int`,
        `fid:int`, `0i`, arity, `tail:(tvm_inst)list`,
        `annotations:(int)list`),
      cm_local_param_stores),
      int_arith_rule(`(${arity:int}) <= ${arity:int}`)),
      param_boundary), outer_tail);
  thm param_start = mp_rule(mp_rule(specl_rule(
      TERM_LIST(params, arity, `annotations:(int)list`),
      cm_param_store_heights_start),
      int_arith_rule(`(${arity:int}) <= ${arity:int}`)),
      param_boundary);
  term fixed_code =
      `([TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
         TVMInst TVMDupOp 0i;
         TVMInst TVMPushOp
           (cm_frame_size (cm_program_structs (p:cm_program))
             ${actual:cm_function_d});
         TVMInst TVMSubOp 0i; TVMInst TVMStoreOp 0i;
         TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
         TVMInst TVMPushOp
           (cm_frame_size (cm_program_structs p)
             ${actual:cm_function_d});
         TVMInst TVMSubOp 0i; TVMInst TVMDupOp 0i;
         TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
         TVMInst TVMPopOp 0i] ++
        ${param_code:(tvm_inst)list})`;
  term fixed_heights =
      `([${arity:int}; ${arity:int} + 1i;
          ${arity:int} + 1i; ${arity:int} + 2i;
          ${arity:int} + 3i; ${arity:int} + 2i;
          ${arity:int}; ${arity:int} + 1i;
          ${arity:int} + 1i; ${arity:int} + 2i;
          ${arity:int} + 1i; ${arity:int} + 2i;
          ${arity:int} + 3i; ${arity:int} + 1i] ++
        ${param_heights:(int)list})`;
  thm result = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMDupOp 0i;
        TVMInst TVMPushOp
          (cm_frame_size (cm_program_structs (p:cm_program))
            ${actual:cm_function_d});
        TVMInst TVMSubOp 0i; TVMInst TVMStoreOp 0i;
        TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp
          (cm_frame_size (cm_program_structs p)
            ${actual:cm_function_d});
        TVMInst TVMSubOp 0i; TVMInst TVMDupOp 0i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMPopOp 0i]`,
      `[${arity:int}; ${arity:int} + 1i;
        ${arity:int} + 1i; ${arity:int} + 2i;
        ${arity:int} + 3i; ${arity:int} + 2i;
        ${arity:int}; ${arity:int} + 1i;
        ${arity:int} + 1i; ${arity:int} + 2i;
        ${arity:int} + 1i; ${arity:int} + 2i;
        ${arity:int} + 3i; ${arity:int} + 1i]`,
      param_code, param_heights, params_ok, param_start,
      THM_LIST(arity_nonnegative,
        cm_fixed_prologue_heights_def));
  result = cm_local_ok_transport(
      result, fixed_code, fixed_heights);
  result = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(cm_fixed_prologue_heights_def),
      gsym_rule(get_cm_emit_prologue_def()),
      get_theorem_by_name("APPEND_ASSOC"))), result);
  thm prologue_equal = beta_norm(inst_rule(TERM_PAIR_LIST(
      (term_pair){actual, `f:cm_function_d`}),
      cm_prologue_heights_def));
  thm fold_heights = beta_norm(ap_term_rule(
      `\prefix:(int)list.
         cm_local_codegen_ok (p:cm_program) (target:int->int)
           (cm_emit_prologue p (fid:int) ++
             (tail:(tvm_inst)list))
           (prefix ++ (annotations:(int)list))`,
      prologue_equal));
  result = eq_mp_rule(sym_rule(fold_heights), result);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_local_prologue =
    cm_prove_local_prologue();

PROOF static thm cm_prove_local_function(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_function_target_heights p target ==>
         cm_height_stream target (cm_function_pc p fid)
           (cm_function_heights p fid
              (inth fid (cm_program_functions p)) ++
            annotations) ==>
         target 0i == 0i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_function p fid ++ tail)
           (cm_function_heights p fid
              (inth fid (cm_program_functions p)) ++
            annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm function_wf = cm_matching_assumption(leaf,
      `cm_function_wf (p:cm_program)
         (inth (fid:int) (cm_program_functions p))`);
  thm target_heights = cm_matching_assumption(leaf,
      `cm_function_target_heights
         (p:cm_program) (target:int->int)`);
  thm whole_stream = cm_matching_assumption(leaf,
      `cm_height_stream (target:int->int)
         (cm_function_pc (p:cm_program) (fid:int))
         (cm_function_heights p fid
            (inth fid (cm_program_functions p)) ++
          (annotations:(int)list))`);
  thm target_zero = cm_matching_assumption(leaf,
      `(target:int->int) 0i == 0i`);
  thm outer_tail = cm_matching_assumption(leaf,
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  term actual =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term body = `cm_function_body ${actual:cm_function_d}`;
  term stmt_pc =
      `cm_function_pc (p:cm_program) (fid:int) +
       cm_function_prologue_count ${actual:cm_function_d}`;
  term return_code =
      `(cm_return_epilogue ++ (tail:(tvm_inst)list))`;
  term return_heights =
      `(cm_return_heights ++ (annotations:(int)list))`;
  thm returned = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `target:int->int`,
      `tail:(tvm_inst)list`, `annotations:(int)list`),
      cm_local_return_epilogue), outer_tail);
  thm return_start = cm_fixed_local_next(
      return_heights, `1i`, THM_LIST(cm_return_heights_def));
  term fallback_code =
      `([TVMInst TVMPushOp 0i] ++
        ${return_code:(tvm_inst)list})`;
  term fallback_heights =
      `([0i] ++ ${return_heights:(int)list})`;
  thm fallback = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[TVMInst TVMPushOp 0i]`, `[0i]`,
      return_code, return_heights, returned, return_start,
      THM_LIST());
  fallback = cm_local_ok_transport(
      fallback, fallback_code, fallback_heights);
  thm fallback_start = cm_fixed_local_next(
      fallback_heights, `0i`, THM_LIST());
  term body_code =
      `(cm_emit_stmt (p:cm_program) (fid:int)
          ${stmt_pc:int} 0i 0i 0i ${body:cm_stmt} ++
        ${fallback_code:(tvm_inst)list})`;
  term body_heights =
      `(cm_stmt_heights (p:cm_program) (fid:int)
          ${body:cm_stmt} ++
        ${fallback_heights:(int)list})`;
  thm direct_stream = conv_rule(
      rewrite_conv(THM_LIST(cm_function_heights_def)),
      whole_stream);
  direct_stream = cm_stream_expected(
      direct_stream,
      `cm_function_pc (p:cm_program) (fid:int)`,
      `(cm_prologue_heights ${actual:cm_function_d} ++
        ${body_heights:(int)list})`);
  thm body_stream = cm_drop_stream_to(
      direct_stream,
      `cm_prologue_heights ${actual:cm_function_d}`,
      body_heights,
      `cm_function_pc (p:cm_program) (fid:int)`,
      stmt_pc, THM_LIST(cm_prologue_height_length));
  thm function_parts = conv_rule(
      rewrite_conv(THM_LIST(get_cm_function_wf_def())),
      function_wf);
  thm stmt_wf = cm_pick_conjunct(function_parts,
      `cm_stmt_wf (p:cm_program) ${actual:cm_function_d}
         F ${body:cm_stmt}`);
  thm body_start = mp_rule(mp_rule(specl_rule(TERM_LIST(
      body, `p:cm_program`, actual, `F`, `fid:int`,
      fallback_heights), cm_stmt_height_starts),
      stmt_wf), fallback_start);
  thm body_ok = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      mp_rule(mp_rule(specl_rule(TERM_LIST(
        body, `p:cm_program`, actual, `F`, `fid:int`,
        stmt_pc, `0i`, `target:int->int`, `0i`, `0i`,
        fallback_code, fallback_heights),
        cm_stmt_local_codegen), stmt_wf),
      target_heights), body_stream), target_zero),
      target_zero), fallback_start), fallback);
  thm prologue_ok = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `target:int->int`, `fid:int`,
      body_code, body_heights), cm_local_prologue),
      body_start), body_ok);
  thm emit_equal = beta_norm(inst_rule(TERM_PAIR_LIST(
      (term_pair){`p:cm_program`, `p:cm_program`},
      (term_pair){`fid:int`, `fid:int`}),
      get_cm_emit_function_def()));
  thm function_equal = beta_norm(inst_rule(TERM_PAIR_LIST(
      (term_pair){`p:cm_program`, `p:cm_program`},
      (term_pair){`fid:int`, `fid:int`},
      (term_pair){actual, `f:cm_function_d`}),
      cm_function_heights_def));
  term raw_code = rhs_of(emit_equal);
  term raw_heights = rhs_of(function_equal);
  term expanded_code =
      `(${raw_code:(tvm_inst)list} ++
        (tail:(tvm_inst)list))`;
  term expanded_heights =
      `(${raw_heights:(int)list} ++
        (annotations:(int)list))`;
  dest_comb_results height_app = dest_comb(concl(prologue_ok));
  term actual_heights = height_app.tm2;
  dest_comb_results code_app = dest_comb(height_app.tm1);
  term actual_code = code_app.tm2;
  thm expanded_code_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      expanded_code);
  thm actual_code_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      actual_code);
  thm code_assoc = trans_rule(
      expanded_code_normal, sym_rule(actual_code_normal));
  thm emit_appended = beta_norm(ap_term_rule(
      `\prefix:(tvm_inst)list.
         prefix ++ (tail:(tvm_inst)list)`,
      emit_equal));
  thm code_equal = trans_rule(emit_appended, code_assoc);
  thm result = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         cm_local_codegen_ok (p:cm_program) (target:int->int)
           code ${actual_heights:(int)list}`,
      code_equal))), prologue_ok);
  thm expanded_height_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      expanded_heights);
  thm actual_height_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      actual_heights);
  thm height_assoc = trans_rule(
      expanded_height_normal, sym_rule(actual_height_normal));
  thm function_appended = beta_norm(ap_term_rule(
      `\prefix:(int)list.
         prefix ++ (annotations:(int)list)`,
      function_equal));
  thm height_equal = trans_rule(
      function_appended, height_assoc);
  result = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\heights:(int)list.
         cm_local_codegen_ok (p:cm_program) (target:int->int)
           (cm_emit_function p (fid:int) ++
             (tail:(tvm_inst)list))
           heights`,
      height_equal))), result);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_local_function =
    cm_prove_local_function();

PROOF static thm cm_prove_function_prefix_zero(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program).
         cm_function_prefix p functions 0i == 0i`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_function_prefix_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_function_prefix_zero =
    cm_prove_function_prefix_zero();

PROOF static thm cm_prove_function_prefix_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         !(p:cm_program) index.
         0i <= index && index < ilength functions ==>
         cm_function_prefix p functions (index + 1i) ==
           cm_function_prefix p functions index +
           cm_function_code_count p
             (ilength (cm_program_functions p) -
                ilength functions + index)`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm bounds = cm_matching_assumption(leaf,
        `0i <= (index:int) &&
         index < ilength ([]:(cm_function_d)list)`);
    thm empty_bounds = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        bounds);
    thm impossible = mp_rule(int_arith_rule(mk_imp(
        concl(empty_bounds), `F`)), empty_bounds);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bounds = cm_matching_assumption(leaf,
        `0i <= (index:int) &&
         index <
           ilength ((a0:cm_function_d) ::
             (a1:(cm_function_d)list))`);
    thm lower = conjunct1_rule(bounds);
    thm upper = conjunct2_rule(bounds);
    thm ih = cm_matching_assumption(leaf,
        `!(p:cm_program) index.
           0i <= index &&
           index < ilength (a1:(cm_function_d)list) ==>
           cm_function_prefix p a1 (index + 1i) ==
             cm_function_prefix p a1 index +
             cm_function_code_count p
               (ilength (cm_program_functions p) -
                  ilength a1 + index)`);
    gnode_list index_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "hindex");
    {
      gnode reduced = CONV_WITH_ASMP_TAC(index_cases[0],
          reduce_rewrite_conv, THM_LIST(
            get_cm_function_prefix_def(),
            cm_function_prefix_zero,
            get_theorem_by_name("ILENGTH_DEF")));
      if (IS_NULL(reduced->solved)) {
        thm zero_index = int_arith_rule(
            `ilength (cm_program_functions (p:cm_program)) -
               (1i + ilength (a1:(cm_function_d)list)) + 0i ==
             ilength (cm_program_functions p) -
               (1i + ilength a1)`);
        gnode normalized = CONV_TAC(reduced,
            reduce_rewrite_conv(THM_LIST(
              cm_function_prefix_zero, zero_index)));
        if (IS_NULL(normalized->solved)) {
          ACCEPT_TAC(normalized,
              int_arith_rule(goal_ccl(normalized->g)));
        }
      }
    }
    {
      gnode branch = index_cases[1];
      thm nonzero = cm_matching_assumption(
          branch, `~((index:int) == 0i)`);
      thm cons_length = apply_conversion(
          rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          `ilength ((a0:cm_function_d) ::
            (a1:(cm_function_d)list))`);
      thm tail_facts = conj_rule(
          conj_rule(bounds, nonzero), cons_length);
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          concl(tail_facts),
          `0i <= (index:int) - 1i &&
           index - 1i <
             ilength (a1:(cm_function_d)list)`)),
          tail_facts);
      thm ih_at = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `(index:int) - 1i`), ih),
          tail_bounds);
      thm recover = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(lower), concl(nonzero)),
          `((index:int) - 1i) + 1i == index`)),
          conj_rule(lower, nonzero));
      thm shifted_index = mp_rule(int_arith_rule(mk_imp(
          concl(cons_length),
          `ilength (cm_program_functions (p:cm_program)) -
             ilength (a1:(cm_function_d)list) +
             ((index:int) - 1i) ==
           ilength (cm_program_functions p) -
             ilength ((a0:cm_function_d) ::
               (a1:(cm_function_d)list)) + index`)),
          cons_length);
      thm ih_exact = conv_rule(rewrite_conv(THM_LIST(
          recover, shifted_index, cons_length)), ih_at);
      thm successor_nonzero = mp_rule(
          int_arith_rule(mk_imp(concl(lower),
            `~(((index:int) + 1i) == 0i)`)),
          lower);
      thm successor_reduce = int_arith_rule(
          `((index:int) + 1i) - 1i == index`);
      gnode reduced = CONV_TAC(branch,
          reduce_rewrite_conv(THM_LIST(
            get_cm_function_prefix_def(),
            nonzero, successor_nonzero, successor_reduce,
            cons_length, get_theorem_by_name("ILENGTH_DEF"))));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
            concl(ih_exact), goal_ccl(reduced->g))), ih_exact));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_prefix_step =
    cm_prove_function_prefix_step();

PROOF static thm cm_prove_function_pc_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         cm_function_pc p (fid + 1i) ==
           cm_function_pc p fid +
           cm_function_code_count p fid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = cm_matching_assumption(leaf,
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`);
  thm step = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`,
      `p:cm_program`, `fid:int`),
      cm_function_prefix_step), bounds);
  thm selected_index = int_arith_rule(
      `ilength (cm_program_functions (p:cm_program)) -
         ilength (cm_program_functions p) + (fid:int) ==
       fid`);
  thm exact = conv_rule(rewrite_conv(
      THM_LIST(selected_index)), step);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_cm_function_pc_def())));
  ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
      concl(exact), goal_ccl(reduced->g))), exact));
  return gnode_prove(root);
}
PROOF thm cm_function_pc_step =
    cm_prove_function_pc_step();

PROOF static thm cm_prove_local_functions(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         !(p:cm_program) fid (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list).
         cm_typed_program p ==>
         0i <= fid ==>
         fid + ilength functions ==
           ilength (cm_program_functions p) ==>
         cm_function_target_heights p target ==>
         target 0i == 0i ==>
         cm_height_stream target (cm_function_pc p fid)
           (cm_functions_heights p fid functions ++ annotations) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_functions p fid functions ++ tail)
           (cm_functions_heights p fid functions ++ annotations)`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm outer_tail = cm_matching_assumption(leaf,
        `cm_local_codegen_ok (p:cm_program) (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list)`);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_functions_def(),
          cm_functions_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, outer_tail);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm typed = cm_matching_assumption(
        leaf, `cm_typed_program (p:cm_program)`);
    thm fid_lower = cm_matching_assumption(
        leaf, `0i <= (fid:int)`);
    thm alignment = cm_matching_assumption(leaf,
        `(fid:int) +
           ilength ((a0:cm_function_d) ::
             (a1:(cm_function_d)list)) ==
         ilength (cm_program_functions (p:cm_program))`);
    thm target_heights = cm_matching_assumption(leaf,
        `cm_function_target_heights
           (p:cm_program) (target:int->int)`);
    thm target_zero = cm_matching_assumption(
        leaf, `(target:int->int) 0i == 0i`);
    thm whole_stream = cm_matching_assumption(leaf,
        `cm_height_stream (target:int->int)
           (cm_function_pc (p:cm_program) (fid:int))
           (cm_functions_heights p fid
              ((a0:cm_function_d) ::
                (a1:(cm_function_d)list)) ++
            (annotations:(int)list))`);
    thm outer_tail = cm_matching_assumption(leaf,
        `cm_local_codegen_ok (p:cm_program) (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list)`);
    thm ih = cm_matching_assumption(leaf,
        `!(p:cm_program) fid (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list).
           cm_typed_program p ==>
           0i <= fid ==>
           fid + ilength (a1:(cm_function_d)list) ==
             ilength (cm_program_functions p) ==>
           cm_function_target_heights p target ==>
           target 0i == 0i ==>
           cm_height_stream target (cm_function_pc p fid)
             (cm_functions_heights p fid a1 ++ annotations) ==>
           cm_local_codegen_ok p target tail annotations ==>
           cm_local_codegen_ok p target
             (cm_emit_functions p fid a1 ++ tail)
             (cm_functions_heights p fid a1 ++ annotations)`);
    thm cons_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_function_d) ::
          (a1:(cm_function_d)list))`);
    thm rest_nonnegative = ispec_rule(
        `a1:(cm_function_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm numeric = conj_rule(conj_rule(
        fid_lower, alignment),
        conj_rule(cons_length, rest_nonnegative));
    thm fid_upper = mp_rule(int_arith_rule(mk_imp(
        concl(numeric),
        `(fid:int) <
         ilength (cm_program_functions (p:cm_program))`)),
        numeric);
    thm fid_bounds = conj_rule(fid_lower, fid_upper);
    thm typed_parts = conv_rule(rewrite_conv(THM_LIST(
        get_cm_typed_program_def())), typed);
    thm all_functions = cm_pick_conjunct(typed_parts,
        `!(i:int).
           0i <= i ==>
           i < ilength (cm_program_functions (p:cm_program)) ==>
           cm_function_wf p
             (inth i (cm_program_functions p))`);
    thm function_wf = mp_rule(mp_rule(
        spec_rule(`fid:int`, all_functions),
        fid_lower), fid_upper);
    thm next_lower = mp_rule(int_arith_rule(mk_imp(
        concl(fid_lower), `0i <= (fid:int) + 1i`)),
        fid_lower);
    thm tail_alignment = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(alignment), concl(cons_length)),
        `((fid:int) + 1i) +
           ilength (a1:(cm_function_d)list) ==
         ilength (cm_program_functions (p:cm_program))`)),
        conj_rule(alignment, cons_length));
    term tail_heights =
        `(cm_functions_heights (p:cm_program)
            ((fid:int) + 1i) (a1:(cm_function_d)list) ++
          (annotations:(int)list))`;
    thm direct_stream = conv_rule(rewrite_conv(
        THM_LIST(cm_functions_heights_def)), whole_stream);
    direct_stream = cm_stream_expected(
        direct_stream,
        `cm_function_pc (p:cm_program) (fid:int)`,
        `(cm_function_heights (p:cm_program) (fid:int)
            (a0:cm_function_d) ++
          ${tail_heights:(int)list})`);
    term next_sequential =
        `cm_function_pc (p:cm_program) (fid:int) +
         cm_function_code_count p fid`;
    thm tail_stream = cm_drop_stream_to(
        direct_stream,
        `cm_function_heights (p:cm_program) (fid:int)
           (a0:cm_function_d)`,
        tail_heights,
        `cm_function_pc (p:cm_program) (fid:int)`,
        next_sequential,
        THM_LIST(cm_function_height_length));
    thm pc_step = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`),
        cm_function_pc_step), fid_bounds);
    thm stream_address = beta_norm(ap_term_rule(
        `\address:int.
           cm_height_stream (target:int->int) address
             ${tail_heights:(int)list}`,
        pc_step));
    tail_stream = eq_mp_rule(
        sym_rule(stream_address), tail_stream);
    thm recursive = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `(fid:int) + 1i`,
          `target:int->int`, `tail:(tvm_inst)list`,
          `annotations:(int)list`), ih),
        typed), next_lower), tail_alignment),
        target_heights), target_zero), tail_stream), outer_tail);
    term recursive_code =
        `(cm_emit_functions (p:cm_program) ((fid:int) + 1i)
            (a1:(cm_function_d)list) ++
          (tail:(tvm_inst)list))`;
    thm function_rule = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `target:int->int`,
        recursive_code, tail_heights),
        cm_local_function);
    function_rule = conv_rule(rewrite_conv(
        THM_LIST(cm_function_heights_def)), function_rule);
    thm expanded_stream = conv_rule(rewrite_conv(
        THM_LIST(cm_function_heights_def)), direct_stream);
    thm result = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        function_rule, function_wf), target_heights),
        expanded_stream), target_zero), recursive);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_functions_def(),
          cm_functions_heights_def,
          cm_function_heights_def,
          get_theorem_by_name("APPEND_ASSOC"))));
    ACCEPT_TAC(reduced, conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"))), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_local_functions =
    cm_prove_local_functions();

PROOF static thm cm_prove_identity_height_stream(void) {
  gnode root = gnode_new_with_ccl(
      `!(heights:(int)list).
         cm_height_stream
           (\address:int. inth address heights)
           0i heights`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_height_stream_def)));
  gnode body = AUTO_INTROS_TAC(opened);
  thm index_zero = int_arith_rule(
      `0i + (i:int) == i`);
  ACCEPT_TAC(body, beta_norm(ap_term_rule(
      `\index:int.
         inth index (heights:(int)list)`,
      index_zero)));
  return gnode_prove(root);
}
PROOF thm cm_identity_height_stream =
    cm_prove_identity_height_stream();

PROOF static thm cm_prove_direct_target_heights(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_function_target_heights p
           (\address:int.
              inth address (cm_codegen_direct_heights p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_function_target_heights_def)));
  gnode body = AUTO_INTROS_TAC(opened);
  thm lower = cm_matching_assumption(
      body, `0i <= (fid:int)`);
  thm upper = cm_matching_assumption(body,
      `(fid:int) <
       ilength (cm_program_functions (p:cm_program))`);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`),
      cm_function_entry_height),
      conj_rule(lower, upper));
  ACCEPT_TAC(body, result);
  return gnode_prove(root);
}
PROOF thm cm_direct_target_heights =
    cm_prove_direct_target_heights();

PROOF static thm cm_prove_direct_target_zero(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         (\address:int.
            inth address (cm_codegen_direct_heights p)) 0i == 0i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_codegen_direct_heights_def,
      cm_prelude_heights_def,
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("INTH_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("NTH_DEF"))));
  return gnode_prove(root);
}
PROOF thm cm_direct_target_zero =
    cm_prove_direct_target_zero();

PROOF static thm cm_prove_function_pc_zero(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program). cm_function_pc p 0i == 11i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_function_pc_def(),
      cm_function_prefix_zero)));
  return gnode_prove(root);
}
PROOF thm cm_function_pc_zero =
    cm_prove_function_pc_zero();

PROOF static thm cm_prove_direct_functions_stream(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_height_stream
           (\address:int.
              inth address (cm_codegen_direct_heights p))
           (cm_function_pc p 0i)
           (cm_functions_heights p 0i
             (cm_program_functions p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm identity = spec_rule(
      `cm_codegen_direct_heights (p:cm_program)`,
      cm_identity_height_stream);
  thm direct = conv_rule(rewrite_conv(THM_LIST(
      cm_codegen_direct_heights_def)), identity);
  thm dropped = mp_rule(specl_rule(TERM_LIST(
      `\address:int.
         inth address
           (cm_prelude_heights ++
            cm_functions_heights (p:cm_program) 0i
              (cm_program_functions p))`,
      `0i`, `cm_prelude_heights`,
      `cm_functions_heights (p:cm_program) 0i
         (cm_program_functions p)`),
      cm_height_stream_drop), direct);
  thm prelude_address = mp_rule(int_arith_rule(mk_imp(
      concl(cm_prelude_height_length),
      `0i + ilength cm_prelude_heights == 11i`)),
      cm_prelude_height_length);
  thm suffix = eq_mp_rule(beta_norm(ap_term_rule(
      `\address:int.
         cm_height_stream
           (\address:int.
              inth address
                (cm_prelude_heights ++
                 cm_functions_heights (p:cm_program) 0i
                   (cm_program_functions p)))
           address
           (cm_functions_heights p 0i
             (cm_program_functions p))`,
      prelude_address)), dropped);
  suffix = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(cm_codegen_direct_heights_def))), suffix);
  thm pc_zero = spec_rule(
      `p:cm_program`, cm_function_pc_zero);
  thm address_equal = beta_norm(ap_term_rule(
      `\address:int.
         cm_height_stream
           (\address:int.
              inth address (cm_codegen_direct_heights
                (p:cm_program)))
           address
           (cm_functions_heights p 0i
             (cm_program_functions p))`,
      pc_zero));
  ACCEPT_TAC(leaf,
      eq_mp_rule(sym_rule(address_equal), suffix));
  return gnode_prove(root);
}
PROOF thm cm_direct_functions_stream =
    cm_prove_direct_functions_stream();

PROOF static thm cm_prove_direct_functions_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_local_codegen_ok p
           (\address:int.
              inth address (cm_codegen_direct_heights p))
           (cm_emit_functions p 0i (cm_program_functions p))
           (cm_functions_heights p 0i
             (cm_program_functions p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = cm_matching_assumption(
      leaf, `cm_wf_program (p:cm_program)`);
  thm wf_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(),
      get_cm_codegen_admissible_def())), wf);
  thm typed = cm_pick_conjunct(
      wf_parts, `cm_typed_program (p:cm_program)`);
  thm target_heights = spec_rule(
      `p:cm_program`, cm_direct_target_heights);
  thm target_zero = beta_norm(spec_rule(
      `p:cm_program`, cm_direct_target_zero));
  thm stream = spec_rule(
      `p:cm_program`, cm_direct_functions_stream);
  thm empty_local = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_local_codegen_ok_def)),
      `cm_local_codegen_ok (p:cm_program)
         (\address:int.
            inth address (cm_codegen_direct_heights p))
         ([]:(tvm_inst)list) ([]:(int)list)`));
  thm functions_rule = specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`,
      `p:cm_program`, `0i`,
      `\address:int.
         inth address (cm_codegen_direct_heights p)`,
      `[]:(tvm_inst)list`, `[]:(int)list`),
      cm_local_functions);
  functions_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"))), functions_rule);
  thm result = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      mp_rule(functions_rule, typed),
      int_arith_rule(
        `0i + ilength (cm_program_functions (p:cm_program)) ==
         ilength (cm_program_functions p)`)),
      target_heights), target_zero), stream), empty_local);
  ACCEPT_TAC(leaf, conv_rule(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))), result));
  return gnode_prove(root);
}
PROOF thm cm_direct_functions_local =
    cm_prove_direct_functions_local();

PROOF static thm cm_prove_direct_codegen_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_local_codegen_ok p
           (\address:int.
              inth address (cm_codegen_direct_heights p))
           (cm_model_code p)
           (cm_codegen_direct_heights p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = cm_matching_assumption(
      leaf, `cm_wf_program (p:cm_program)`);
  thm wf_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(),
      get_cm_codegen_admissible_def())), wf);
  thm typed = cm_pick_conjunct(
      wf_parts, `cm_typed_program (p:cm_program)`);
  thm typed_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm main_lower = cm_pick_conjunct(typed_parts,
      `0i <= cm_program_main (p:cm_program)`);
  thm main_upper = cm_pick_conjunct(typed_parts,
      `cm_program_main (p:cm_program) <
       ilength (cm_program_functions p)`);
  thm main_params = cm_pick_conjunct(typed_parts,
      `cm_function_params
         (inth (cm_program_main (p:cm_program))
           (cm_program_functions p)) ==
       ([]:(cm_slot_d)list)`);
  thm target_heights = spec_rule(
      `p:cm_program`, cm_direct_target_heights);
  thm target_rule = conv_rule(rewrite_conv(THM_LIST(
      cm_function_target_heights_def)), target_heights);
  thm main_target = mp_rule(mp_rule(spec_rule(
      `cm_program_main (p:cm_program)`, target_rule),
      main_lower), main_upper);
  main_target = conv_rule(reduce_rewrite_conv(THM_LIST(
      main_params, get_theorem_by_name("ILENGTH_DEF"))),
      main_target);
  thm main_arity = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))),
      ap_term_rule(`ilength:(cm_slot_d)list->int`,
        main_params));
  term call_inst =
      `TVMInst TVMCallOp
         (cm_function_pc (p:cm_program)
           (cm_program_main p))`;
  term call_exists =
      `?fid.
         0i <= fid &&
         fid < ilength (cm_program_functions (p:cm_program)) &&
         tvm_inst_imm ${call_inst:tvm_inst} ==
           cm_function_pc p fid &&
         0i ==
           ilength (cm_function_params
             (inth fid (cm_program_functions p)))`;
  thm call_imm = by_rewrite(
      `tvm_inst_imm ${call_inst:tvm_inst} ==
       cm_function_pc (p:cm_program)
         (cm_program_main p)`,
      THM_LIST(get_tvm_inst_imm_def()));
  thm call_body = conj_rule(main_lower,
      conj_rule(main_upper,
        conj_rule(call_imm,
          sym_rule(main_arity))));
  thm call_witness = exists_rule(
      call_exists, `cm_program_main (p:cm_program)`,
      call_body);
  term call_condition =
      `tvm_inst_op ${call_inst:tvm_inst} == TVMCallOp`;
  thm call_fact = disch_rule(
      call_condition, call_witness);
  thm functions_local = mp_rule(
      spec_rule(`p:cm_program`,
        cm_direct_functions_local), wf);
  term functions_code =
      `cm_emit_functions (p:cm_program) 0i
         (cm_program_functions p)`;
  term functions_heights =
      `cm_functions_heights (p:cm_program) 0i
         (cm_program_functions p)`;
  thm result = cm_local_fixed(
      `p:cm_program`,
      `\address:int.
         inth address (cm_codegen_direct_heights p)`,
      `[TVMInst TVMPushOp 1048576i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc p (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]`,
      `[0i; 1i; 2i; 0i; 1i; 2i; 1i; 2i; 1i; 2i; 1i]`,
      functions_code, functions_heights,
      functions_local, empty_theorem,
      THM_LIST(main_target, call_fact));
  dest_comb_results height_app = dest_comb(concl(result));
  term actual_heights = height_app.tm2;
  dest_comb_results code_app = dest_comb(height_app.tm1);
  term actual_code = code_app.tm2;
  thm prelude_equal = beta_norm(inst_rule(TERM_PAIR_LIST(
      (term_pair){`p:cm_program`, `p:cm_program`}),
      get_cm_emit_prelude_def()));
  thm model_equal = beta_norm(inst_rule(TERM_PAIR_LIST(
      (term_pair){`p:cm_program`, `p:cm_program`}),
      get_cm_model_code_def()));
  thm prelude_appended = beta_norm(ap_term_rule(
      `\prefix:(tvm_inst)list.
         prefix ++ ${functions_code:(tvm_inst)list}`,
      prelude_equal));
  thm model_expanded = trans_rule(
      model_equal, prelude_appended);
  term expanded_code = rhs_of(model_expanded);
  thm expanded_code_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      expanded_code);
  thm actual_code_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      actual_code);
  thm code_equal = trans_rule(model_expanded,
      trans_rule(expanded_code_normal,
        sym_rule(actual_code_normal)));
  result = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         cm_local_codegen_ok (p:cm_program)
           (\address:int.
              inth address (cm_codegen_direct_heights p))
           code ${actual_heights:(int)list}`,
      code_equal))), result);
  thm direct_equal = beta_norm(inst_rule(TERM_PAIR_LIST(
      (term_pair){`p:cm_program`, `p:cm_program`}),
      cm_codegen_direct_heights_def));
  thm prelude_height_appended = beta_norm(ap_term_rule(
      `\prefix:(int)list.
         prefix ++ ${functions_heights:(int)list}`,
      cm_prelude_heights_def));
  thm direct_expanded = trans_rule(
      direct_equal, prelude_height_appended);
  term expanded_heights = rhs_of(direct_expanded);
  thm expanded_height_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      expanded_heights);
  thm actual_height_normal = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND_ASSOC"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      actual_heights);
  thm height_equal = trans_rule(direct_expanded,
      trans_rule(expanded_height_normal,
        sym_rule(actual_height_normal)));
  result = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\heights:(int)list.
         cm_local_codegen_ok (p:cm_program)
           (\address:int.
              inth address (cm_codegen_direct_heights p))
           (cm_model_code p) heights`,
      height_equal))), result);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_direct_codegen_local =
    cm_prove_direct_codegen_local();
