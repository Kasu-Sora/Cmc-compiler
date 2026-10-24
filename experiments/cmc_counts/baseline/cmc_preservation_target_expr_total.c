#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_target_expr_total.h"
#include "cmc_preservation_target_ready.h"
#include "cmc_preservation_tagged_task.h"
#include "cmc_preservation_code_task.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_target_expr.c"
#require "cmc_preservation_target_ready.c"
#require "cmc_preservation_static_bases.c"
#require "cmc_preservation_tagged_task.c"
#require "cmc_preservation_code_task.c"

PROOF static size_t _cmc_preservation_target_expr_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_expr_total_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_target_binding_ready(void) {
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term offset =
      `if (scope:int) == 1i
       then cm_local_offset (p:cm_program) (fid:int) (slot:int)
       else cm_param_offset p fid slot`;
  term address =
      `if (scope:int) == 0i
       then cm_global_address (p:cm_program) (slot:int)
       else cm_state_fp (st:cm_src_state) + ${offset:int}`;
  term address_value =
      `if (scope:int) == 0i
       then cm_global_pointer (p:cm_program) (slot:int)
       else cm_state_env (st:cm_src_state) scope slot`;
  term conclusion = list_mk_conj(TERM_LIST(
      `(scope:int) == 0i ||
       (tower_signed64 (cm_state_fp (st:cm_src_state)) &&
        tower_signed64 ${offset:int})`,
      `${address:int} == ${address:int}`,
      `tower_signed64 ${address:int}`,
      `tower_wrap64 ${address:int} ==
       cm_value_number (st:cm_src_state) ${address_value:cm_value}`));
  term body = imp_chain(TERM_LIST(
      `cm_function_wf (p:cm_program) ${function:cm_function_d}`,
      `cm_binding_valid p ${function:cm_function_d}
        (scope:int) (slot:int)`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `cm_binding_address_ok p fid scope slot st`), conclusion);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm function_wf = assume_rule(
      `cm_function_wf (p:cm_program) ${function:cm_function_d}`);
  thm binding_valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binding_valid_def())), assume_rule(
        `cm_binding_valid (p:cm_program) ${function:cm_function_d}
          (scope:int) (slot:int)`));
  thm fp_signed = assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`);
  thm binding_ok = assume_rule(
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`);
  gnode_list binding_cases = DISJ_CASES_TAC(leaf, binding_valid, "Hbinding");
  for (size_t i = 0; i < vector_size(binding_cases); ++i) {
    gnode branch = binding_cases[i];
    thm selected = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hbinding")].tm);
    thm scope_shape = conjunct1_rule(selected);
    thm numeric;
    if (i == 0) {
      numeric = disj1_rule(scope_shape,
          `tower_signed64 (cm_state_fp (st:cm_src_state)) &&
           tower_signed64 ${offset:int}`);
    } else {
      thm slot_nonnegative = conjunct1_rule(conjunct2_rule(selected));
      thm slot_upper = conjunct2_rule(conjunct2_rule(selected));
      thm offset_signed = match_mp_rule(
          match_mp_rule(
            match_mp_rule(i == 1 ? cm_local_offset_signed
                                 : cm_param_offset_signed,
              function_wf),
            slot_nonnegative),
          slot_upper);
      numeric = disj2_rule(`(scope:int) == 0i`,
          conj_rule(fp_signed, offset_signed));
    }
    thm opened_binding = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binding_address_ok_def(), scope_shape,
        get_cm_local_base_def(), get_cm_param_base_def(),
        get_cm_local_offset_def(), get_cm_param_offset_def())), binding_ok);
    thm signed_address = conjunct1_rule(opened_binding);
    thm wrapped_address = conjunct1_rule(conjunct2_rule(opened_binding));
    thm result = list_conj_rule(THM_LIST(
        numeric, refl_rule(address), signed_address, wrapped_address));
    thm_list rules = THM_LIST(
        scope_shape, get_cm_local_base_def(), get_cm_param_base_def(),
        get_cm_local_offset_def(), get_cm_param_offset_def());
    thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
  }
  return gnode_prove(root);
}
PROOF static thm cm_target_binding_ready =
    cm_prove_target_binding_ready();

PROOF static void cm_target_expr_total_accept(
    const gnode branch, const thm_list rules, const thm result) {
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view =
      apply_conversion(reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_target_r_step(void) {
  term task =
      `CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term target_sim =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_task_static_valid ${task:cm_task}`,
      `cm_task_static_bases p ${task:cm_task}`,
      `0i <= (fid:int)`,
      `cm_task_layout_ready p ${task:cm_task} (ann:cm_annotation)`,
      `cm_task_runtime_invariant p ${task:cm_task} ann`,
      `cm_task_generation_safe p ${task:cm_task} ann`,
      `cm_task_tagged_valid ${task:cm_task}`,
      `cm_annotation_erases ${task:cm_task} ann`,
      `cm_task_layout p ${task:cm_task} ann`,
      `cm_task_target_sim p ${task:cm_task}
        (target:tvm_task) ann`), target_sim);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm wf_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_target_expr_total_consequence(
      wf_opened, `cm_typed_program (p:cm_program)`);
  thm typed_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())), typed);
  thm static_valid = assume_rule(
      `cm_task_static_valid ${task:cm_task}`);
  thm expr_static = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_static_valid_def)), static_valid));
  thm static_bases = assume_rule(
      `cm_task_static_bases (p:cm_program) ${task:cm_task}`);
  thm ready = assume_rule(
      `cm_task_layout_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm ready_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_layout_ready_def)), ready);
  thm r_ready = ready_opened;
  thm runtime = assume_rule(
      `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm runtime_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def)), runtime);
  thm regions_before = conjunct1_rule(runtime_opened);
  thm stack = conjunct2_rule(runtime_opened);
  thm generation_safe = assume_rule(
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm generation_opened = conv_rule(rewrite_conv(THM_LIST(
      cm_task_generation_safe_def)), generation_safe);
  thm task_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_below_def)), conjunct1_rule(generation_opened));
  thm state_generation = conjunct1_rule(task_generation);
  thm annotation_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_generation_below_def)),
      conjunct2_rule(generation_opened));
  thm tagged = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_tagged_valid_def)), assume_rule(
        `cm_task_tagged_valid ${task:cm_task}`));
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} (ann:cm_annotation)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`);
  thm fid_valid = match_mp_rule(cm_runtime_stack_fid_valid, stack);
  thm fid_nonnegative = assume_rule(`0i <= (fid:int)`);
  thm fid_facts = conj_rule(fid_nonnegative, fid_valid);
  thm fid_bounds = mp_rule(int_arith_rule(mk_imp(
      concl(fid_facts),
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`)),
      fid_facts);
  thm function_rule = spec_rule(`fid:int`,
      cm_target_expr_total_consequence(typed_opened,
        `!(i:int). 0i <= i ==>
          i < ilength (cm_program_functions (p:cm_program)) ==>
          cm_function_wf p (inth i (cm_program_functions p))`));
  thm function_wf = match_mp_rule(
      match_mp_rule(function_rule, conjunct1_rule(fid_bounds)),
      conjunct2_rule(fid_bounds));
  thm fp_bounds = match_mp_rule(cm_runtime_stack_fp_bounds, stack);
  thm fp_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds),
      `--9223372036854775808i <= cm_state_fp (st:cm_src_state) &&
       cm_state_fp st <= 9223372036854775807i`)), fp_bounds);
  thm fp_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (cm_state_fp (st:cm_src_state))`)),
      fp_signed_raw);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hex")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hex")].tm);
    thm_list shape_rules = THM_LIST(shape);
    thm shaped_layout =
        conv_rule(rewrite_conv(shape_rules), layout);
    thm shaped_sim = conv_rule(rewrite_conv(shape_rules), sim);
    if (i == 0) {
      thm result = match_mp_rule(
          match_mp_rule(get_cm_target_r_const_step(), shaped_layout),
          shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 1) {
      thm bridge = match_mp_rule(
          match_mp_rule(get_cm_task_static_bases_string_number(),
            conv_rule(rewrite_conv(shape_rules), static_valid)),
          conv_rule(rewrite_conv(shape_rules), static_bases));
      thm result = match_mp_rule(
          match_mp_rule(
            match_mp_rule(get_cm_target_r_string_step(), shaped_layout),
            shaped_sim),
          bridge);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 2) {
      term array_term =
          `cm_binding_array (p:cm_program) (fid:int)
            (a0:int) (a1:int)`;
      gnode_list array_cases =
          BOOL_CASES_TAC(branch, array_term, "Harray");
      {
        thm array = assume_rule(array_term);
        thm array_rule = specl_rule(TERM_LIST(
            `a0:int`, `a1:int`, `a2:cm_type`),
            conjunct2_rule(conjunct2_rule(conv_rule(
              rewrite_conv(THM_LIST(cm_r_layout_ready_def)), r_ready))));
        thm binding =
            mp_rule(mp_rule(array_rule, shape), array);
        thm binding_valid = conv_rule(reduce_rewrite_conv(THM_LIST(
            shape, cm_expr_static_valid_def)), expr_static);
        thm numeric = match_mp_rule(
            match_mp_rule(
              match_mp_rule(
                match_mp_rule(cm_target_binding_ready, function_wf),
                binding_valid),
              fp_signed),
            binding);
        term address =
            `if (a0:int) == 0i
             then cm_global_address (p:cm_program) (a1:int)
             else cm_state_fp (st:cm_src_state) +
               (if a0 == 1i then cm_local_offset p fid a1
                else cm_param_offset p fid a1)`;
        thm result = get_cm_target_r_array_step();
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(shape_rules), layout));
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(shape_rules), sim));
        result = match_mp_rule(result, array);
        result = match_mp_rule(result, binding);
        result = match_mp_rule(result, conjunct1_rule(numeric));
        result = match_mp_rule(result,
            conjunct1_rule(conjunct2_rule(numeric)));
        result = match_mp_rule(result,
            conjunct1_rule(conjunct2_rule(conjunct2_rule(numeric))));
        result = match_mp_rule(result,
            conjunct2_rule(conjunct2_rule(conjunct2_rule(numeric))));
        cm_target_expr_total_accept(array_cases[0],
            THM_LIST(shape, array), result);
      }
      {
        thm not_array = assume_rule(mk_not(array_term));
        thm result = match_mp_rule(
            match_mp_rule(get_cm_target_r_var_scalar_step(), not_array),
            conv_rule(rewrite_conv(shape_rules), sim));
        cm_target_expr_total_accept(array_cases[1],
            THM_LIST(shape, not_array), result);
      }
    } else if (i == 3) {
      thm result =
          match_mp_rule(get_cm_target_r_assign_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 4) {
      thm result =
          match_mp_rule(get_cm_target_r_binary_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 5) {
      gnode_list load_cases =
          BOOL_CASES_TAC(branch, `(a0:int) == 2i`, "Hload");
      {
        thm load = assume_rule(`(a0:int) == 2i`);
        thm result = match_mp_rule(
            match_mp_rule(get_cm_target_r_unary_load_start_step(), load),
            conv_rule(rewrite_conv(shape_rules), sim));
        cm_target_expr_total_accept(load_cases[0],
            THM_LIST(shape, load), result);
      }
      gnode_list address_cases = BOOL_CASES_TAC(
          load_cases[1], `(a0:int) == 3i`, "Haddress");
      {
        thm not_load = assume_rule(`~((a0:int) == 2i)`);
        thm address = assume_rule(`(a0:int) == 3i`);
        thm result = get_cm_target_r_unary_address_start_step();
        result = match_mp_rule(result, not_load);
        result = match_mp_rule(result, address);
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(shape_rules), sim));
        cm_target_expr_total_accept(address_cases[0],
            THM_LIST(shape, not_load, address), result);
      }
      {
        thm not_load = assume_rule(`~((a0:int) == 2i)`);
        thm not_address = assume_rule(`~((a0:int) == 3i)`);
        thm result = get_cm_target_r_unary_value_start_step();
        result = match_mp_rule(result, not_load);
        result = match_mp_rule(result, not_address);
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(shape_rules), sim));
        cm_target_expr_total_accept(address_cases[1],
            THM_LIST(shape, not_load, not_address), result);
      }
    } else if (i == 6) {
      thm result =
          match_mp_rule(get_cm_target_r_index_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 7) {
      term member_array =
          `cm_member_array (p:cm_program)
            (cm_expr_type (a0:cm_expr)) (a1:int)`;
      gnode_list member_cases =
          BOOL_CASES_TAC(branch, member_array, "Hmember_array");
      for (size_t j = 0; j < vector_size(member_cases); ++j) {
        thm member_fact = assume_rule(j == 0
            ? member_array : mk_not(member_array));
        thm result = j == 0
            ? get_cm_target_r_member_array_start_step()
            : get_cm_target_r_member_scalar_start_step();
        result = match_mp_rule(result, member_fact);
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(shape_rules), sim));
        cm_target_expr_total_accept(member_cases[j],
            THM_LIST(shape, member_fact), result);
      }
    } else if (i == 8) {
      term args = `a1:(cm_expr)list`;
      gnode_list args_cases = DISJ_CASES_TAC(branch,
          ispec_rule(args, get_theorem_by_name("list_CASES")),
          "Hargs");
      {
        thm args_nil = assume_rule(goal_lasmps(args_cases[0]->g)[
            labeled_term_list_index(goal_lasmps(args_cases[0]->g),
              "Hargs")].tm);
        thm_list call_rules = THM_LIST(shape, args_nil);
        thm call_ready_open = conv_rule(reduce_rewrite_conv(THM_LIST(
            shape, args_nil, cm_r_layout_ready_def)), r_ready);
        thm call_rule = specl_rule(TERM_LIST(
            `a0:int`, `a2:cm_type`),
            conjunct1_rule(call_ready_open));
        thm call_fields = match_mp_rule(call_rule,
            refl_rule(`CMCallE (a0:int) [] (a2:cm_type)`));
        thm call_ok = conjunct1_rule(call_fields);
        thm source_depth =
            conjunct1_rule(conjunct2_rule(call_fields));
        thm cursor_depth =
            conjunct2_rule(conjunct2_rule(call_fields));
        thm call_ready = cm_target_call_ready;
        call_ready = match_mp_rule(call_ready, wf);
        call_ready = match_mp_rule(call_ready, state_generation);
        call_ready = match_mp_rule(call_ready, call_ok);
        call_ready = match_mp_rule(call_ready, cursor_depth);
        call_ready = match_mp_rule(call_ready, regions_before);
        call_ready = match_mp_rule(call_ready, stack);
        call_ready = spec_rule(`a2:cm_type`, call_ready);
        call_ready = spec_rule(`cm_ann_pc (ann:cm_annotation) + 1i`,
            call_ready);
        call_ready = spec_rule(`cm_ann_temp (ann:cm_annotation)`,
            call_ready);
        call_ready = spec_rule(`cm_ann_break (ann:cm_annotation)`,
            call_ready);
        call_ready = spec_rule(`cm_ann_continue (ann:cm_annotation)`,
            call_ready);
        thm call_ready_opened = conv_rule(rewrite_conv(THM_LIST(
            cm_call_target_ready_def)), call_ready);
        thm state_opened = conv_rule(rewrite_conv(THM_LIST(
            cm_state_generation_below_def)), state_generation);
        thm state_tags = match_mp_rule(specl_rule(TERM_LIST(
            `st:cm_src_state`, `cm_state_nextgen (st:cm_src_state)`),
            cm_state_tags_generation_from_all),
            conjunct2_rule(conjunct2_rule(state_opened)));
        thm result = get_cm_target_r_empty_call_step();
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(call_rules), layout));
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(call_rules), erases));
        result = match_mp_rule(result,
            conv_rule(rewrite_conv(call_rules), sim));
        result = match_mp_rule(result, typed);
        result = match_mp_rule(result, call_ok);
        result = match_mp_rule(result, source_depth);
        term_list ready_terms = TERM_LIST(
            `tvm_target_valid (cm_model_code (p:cm_program))
              (cm_function_pc p (a0:int))`,
            `cm_function_wf (p:cm_program)
              (inth (a0:int) (cm_program_functions p))`,
            `cm_frame_segment (p:cm_program) (a0:int)
              (cm_state_fp (st:cm_src_state) -
                cm_frame_size (cm_program_structs p)
                  (inth (a0:int) (cm_program_functions p)))
              (cm_state_fp st)`);
        for (size_t j = 0; j < vector_size(ready_terms); ++j) {
          result = match_mp_rule(result,
              find_conjunct_rule(call_ready_opened, ready_terms[j]));
        }
        result = match_mp_rule(result, regions_before);
        result = match_mp_rule(result,
            find_conjunct_rule(call_ready_opened,
              `0i <= cm_state_nextgen (st:cm_src_state)`));
        result = match_mp_rule(result,
            find_conjunct_rule(call_ready_opened,
              `ilength (cm_ann_calls (ann:cm_annotation)) < 65536i`));
        result = match_mp_rule(result, state_tags);
        result = match_mp_rule(result, annotation_generation);
        result = match_mp_rule(result, tagged);
        term frame_base =
            `cm_state_fp (st:cm_src_state) -
              cm_frame_size (cm_program_structs (p:cm_program))
                (inth (a0:int) (cm_program_functions p))`;
        term active =
            `cm_active_spill_frames (fid:int)
              (st:cm_src_state) (ann:cm_annotation)`;
        term entered =
            `cm_ann_enter_call (p:cm_program) (fid:int) (a0:int)
              (st:cm_src_state) (a2:cm_type)
              (cm_ann_pc (ann:cm_annotation) + 1i)
              (cm_ann_temp ann) (cm_ann_break ann)
              (cm_ann_continue ann) (cm_ann_cursors ann)
              (cm_ann_spills ann) (cm_ann_saved ann)
              (cm_ann_calls ann)`;
        term pending =
            `cm_call_pending_base (p:cm_program) (a0:int)
              (st:cm_src_state)`;
        term_list remaining = TERM_LIST(
            `!addr. cm_live_address (st:cm_src_state) addr ==>
              ~(${frame_base:int} <= addr &&
                addr < ${frame_base:int} + 8i)`,
            `!addr. cm_live_address (st:cm_src_state) addr ==>
              ~(8i <= addr && addr < 16i)`,
            `cm_range_disjoint ${frame_base:int} 8i 8i 8i`,
            `cm_range_disjoint 8i 8i ${frame_base:int} 8i`,
            `cm_call_frames_store_safe CMIntTy ${frame_base:int}
              (cm_ann_calls (ann:cm_annotation))`,
            `cm_spill_frames_store_safe (p:cm_program) CMIntTy
              ${frame_base:int}
              (CMSpillFrame (fid:int) (cm_state_fp st)
                (cm_ann_spills ann) :: cm_ann_saved ann)`,
            `cm_call_frames_store_safe CMIntTy 8i
              (cm_ann_calls (ann:cm_annotation))`,
            `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
              (CMSpillFrame (fid:int) (cm_state_fp st)
                (cm_ann_spills ann) :: cm_ann_saved ann)`,
            `tower_signed64 (cm_state_fp (st:cm_src_state))`,
            `tower_signed64
              (cm_frame_size (cm_program_structs (p:cm_program))
                (inth (a0:int) (cm_program_functions p)))`,
            `tower_signed64 ${frame_base:int}`,
            `tower_word_valid ${frame_base:int}`,
            `cm_runtime_memory_layout (p:cm_program)
              ${pending:cm_src_state}
              (cm_ann_calls ${entered:cm_annotation})
              (cm_active_spill_frames (a0:int)
                ${pending:cm_src_state} ${entered:cm_annotation})`);
        for (size_t j = 0; j < vector_size(remaining); ++j) {
          thm fact =
              find_conjunct_rule(call_ready_opened, remaining[j]);
          if (j == 1) {
            fact = conv_rule(rewrite_conv(THM_LIST(gsym_rule(
                int_arith_rule(`8i + 8i == 16i`)))), fact);
          } else if (j == 5 || j == 7) {
            term desired = j == 5
                ? `cm_spill_frames_store_safe (p:cm_program) CMIntTy
                    ${frame_base:int} ${active:(cm_spill_frame)list}`
                : `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
                    ${active:(cm_spill_frame)list}`;
            thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
                cm_active_spill_frames_def, cm_spill_frame_fp_def)),
                desired);
            fact = eq_mp_rule(sym_rule(view), fact);
          }
          result = match_mp_rule(result, fact);
        }
        cm_target_expr_total_accept(args_cases[0], call_rules, result);
      }
      {
        gnode cons_branch = ASMP_EXISTS_TAC(
            args_cases[1], "Hargs", NULL);
        cons_branch = ASMP_EXISTS_TAC(cons_branch, "Hargs", NULL);
        thm args_cons = assume_rule(goal_lasmps(cons_branch->g)[
            labeled_term_list_index(goal_lasmps(cons_branch->g),
              "Hargs")].tm);
        thm_list call_rules = THM_LIST(shape, args_cons);
        thm result = match_mp_rule(
            get_cm_target_r_call_args_start_step(),
            conv_rule(rewrite_conv(call_rules), sim));
        cm_target_expr_total_accept(cons_branch, call_rules, result);
      }
    } else if (i == 9) {
      thm result = match_mp_rule(
          match_mp_rule(get_cm_target_r_sizeof_step(), shaped_layout),
          shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 10) {
      thm input_rule = spec_rule(`a0:cm_type`,
          conjunct1_rule(conjunct2_rule(conv_rule(
            rewrite_conv(THM_LIST(cm_r_layout_ready_def)), r_ready))));
      thm input_ready = match_mp_rule(input_rule, shape);
      thm result = get_cm_target_r_getc_step();
      result = match_mp_rule(result, shaped_layout);
      result = match_mp_rule(result, shaped_sim);
      result = match_mp_rule(result, input_ready);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 11) {
      thm result =
          match_mp_rule(get_cm_target_r_putc_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 12) {
      thm result =
          match_mp_rule(get_cm_target_r_puti_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else {
      thm result =
          match_mp_rule(get_cm_target_r_exit_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_target_r_step = cm_prove_target_r_step();

PROOF static thm cm_prove_target_l_step(void) {
  term task =
      `CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term target_sim =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_task_static_valid ${task:cm_task}`,
      `0i <= (fid:int)`,
      `cm_task_layout_ready p ${task:cm_task} (ann:cm_annotation)`,
      `cm_task_runtime_invariant p ${task:cm_task} ann`,
      `cm_task_layout p ${task:cm_task} ann`,
      `cm_task_target_sim p ${task:cm_task}
        (target:tvm_task) ann`), target_sim);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm wf_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_target_expr_total_consequence(
      wf_opened, `cm_typed_program (p:cm_program)`);
  thm typed_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())), typed);
  thm static_valid = assume_rule(
      `cm_task_static_valid ${task:cm_task}`);
  thm expr_static = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_static_valid_def)), static_valid));
  thm ready_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_layout_ready_def)), assume_rule(
        `cm_task_layout_ready (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm l_ready = ready_opened;
  thm l_ready_opened = conv_rule(
      rewrite_conv(THM_LIST(cm_l_layout_ready_def)), l_ready);
  thm lvalue = conjunct1_rule(l_ready_opened);
  thm runtime_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def)), assume_rule(
        `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm stack = conjunct2_rule(runtime_opened);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`);
  thm fid_valid = match_mp_rule(cm_runtime_stack_fid_valid, stack);
  thm fid_nonnegative = assume_rule(`0i <= (fid:int)`);
  thm fid_facts = conj_rule(fid_nonnegative, fid_valid);
  thm fid_bounds = mp_rule(int_arith_rule(mk_imp(
      concl(fid_facts),
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`)),
      fid_facts);
  thm function_rule = spec_rule(`fid:int`,
      cm_target_expr_total_consequence(typed_opened,
        `!(i:int). 0i <= i ==>
          i < ilength (cm_program_functions (p:cm_program)) ==>
          cm_function_wf p (inth i (cm_program_functions p))`));
  thm function_wf = match_mp_rule(
      match_mp_rule(function_rule, conjunct1_rule(fid_bounds)),
      conjunct2_rule(fid_bounds));
  thm fp_bounds = match_mp_rule(cm_runtime_stack_fp_bounds, stack);
  thm fp_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds),
      `--9223372036854775808i <= cm_state_fp (st:cm_src_state) &&
       cm_state_fp st <= 9223372036854775807i`)), fp_bounds);
  thm fp_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (cm_state_fp (st:cm_src_state))`)),
      fp_signed_raw);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hex")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hex")].tm);
    thm_list shape_rules = THM_LIST(shape);
    thm shaped_sim = conv_rule(rewrite_conv(shape_rules), sim);
    if (i == 2) {
      thm binding_rule = specl_rule(TERM_LIST(
          `a0:int`, `a1:int`, `a2:cm_type`),
          conjunct2_rule(l_ready_opened));
      thm binding = match_mp_rule(binding_rule, shape);
      thm binding_valid = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_expr_static_valid_def)), expr_static);
      thm numeric = match_mp_rule(
          match_mp_rule(
            match_mp_rule(
              match_mp_rule(cm_target_binding_ready, function_wf),
              binding_valid),
            fp_signed),
          binding);
      thm result = get_cm_target_l_var_step();
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(shape_rules), layout));
      result = match_mp_rule(result, shaped_sim);
      result = match_mp_rule(result, binding);
      result = match_mp_rule(result, conjunct1_rule(numeric));
      result = match_mp_rule(result,
          conjunct1_rule(conjunct2_rule(numeric)));
      result = match_mp_rule(result,
          conjunct1_rule(conjunct2_rule(conjunct2_rule(numeric))));
      result = match_mp_rule(result,
          conjunct2_rule(conjunct2_rule(conjunct2_rule(numeric))));
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 5) {
      thm load = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_lvalue_def())), lvalue);
      thm result = match_mp_rule(
          match_mp_rule(get_cm_target_l_unary_address_step(), load),
          shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 6) {
      thm result =
          match_mp_rule(get_cm_target_l_index_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else if (i == 7) {
      thm result =
          match_mp_rule(get_cm_target_l_member_start_step(), shaped_sim);
      cm_target_expr_total_accept(branch, shape_rules, result);
    } else {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_lvalue_def())), lvalue);
      CONTR_TAC(branch, impossible);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_target_l_step = cm_prove_target_l_step();

PROOF thm get_cm_target_r_step(void) {
  return cm_target_r_step;
}
PROOF thm get_cm_target_l_step(void) {
  return cm_target_l_step;
}

PROOF static int cmc_preservation_target_expr_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_expr_total_axioms_before,
      "cmc_preservation_target_expr_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_r_step)) == 0,
      "total r-expression theorem has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_target_l_step)) == 0,
      "total l-expression theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_expr_total_checks =
    cmc_preservation_target_expr_total_final_checks();
