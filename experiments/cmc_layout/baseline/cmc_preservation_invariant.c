#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_runtime.h"
#require "cmc_preservation_runtime.c"
#include "cmc_preservation_code.h"
#require "cmc_preservation_code.c"
#include "cmc_preservation_invariant.h"

PROOF static size_t _cmc_preservation_invariant_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_static_regions_def = new_fun_definition(
    `cm_static_regions (p:cm_program) : (cm_region)list =
       APPEND
         (cm_global_regions p (cm_program_globals p) 0i)
         (cm_string_regions p (cm_program_strings p) 0i)`);


PROOF thm cm_phase_is_halt_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_is_halt CAHaltP = T) &&
     (!ty. cm_phase_is_halt (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_is_halt (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_is_halt (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_is_halt
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_is_halt
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_is_halt (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_is_halt
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_is_halt
        (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid ty. cm_phase_is_halt (CAMemberP (mid:int) (ty:cm_type)) = F) &&
     (cm_phase_is_halt CAPutcP = F) &&
     (cm_phase_is_halt CAPutiP = F) &&
     (cm_phase_is_halt CAExitP = F) &&
     (cm_phase_is_halt CAExprStmtP = F) &&
     (!slot. cm_phase_is_halt (CAInitP (slot:int)) = F) &&
     (!env regions jump target. cm_phase_is_halt
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = F) &&
     (!second. cm_phase_is_halt (CASeqP (second:cm_stmt)) = F) &&
     (!yes no. cm_phase_is_halt
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body loop_start loop_end. cm_phase_is_halt
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end. cm_phase_is_halt
        (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)
          (loop_start:int) (loop_end:int)) = F) &&
     (cm_phase_is_halt CAReturnP = F) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_is_halt
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_is_halt
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = F)`);

PROOF thm cm_phase_is_scope_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_is_scope CAHaltP = F) &&
     (!ty. cm_phase_is_scope (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_is_scope
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_is_scope
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_is_scope
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_is_scope
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_is_scope (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_is_scope
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_is_scope
        (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid ty. cm_phase_is_scope
        (CAMemberP (mid:int) (ty:cm_type)) = F) &&
     (cm_phase_is_scope CAPutcP = F) &&
     (cm_phase_is_scope CAPutiP = F) &&
     (cm_phase_is_scope CAExitP = F) &&
     (cm_phase_is_scope CAExprStmtP = F) &&
     (!slot. cm_phase_is_scope (CAInitP (slot:int)) = F) &&
     (!env regions jump target. cm_phase_is_scope
        (CABlockP (env:int->int->cm_value)
          (regions:(cm_region)list) (jump:bool) (target:int)) = T) &&
     (!second. cm_phase_is_scope
        (CASeqP (second:cm_stmt)) = F) &&
     (!yes no. cm_phase_is_scope
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body loop_start loop_end. cm_phase_is_scope
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end.
        cm_phase_is_scope
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) = T) &&
     (cm_phase_is_scope CAReturnP = F) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_is_scope
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_is_scope
        (CACallP (caller:int) (env:int->int->cm_value)
          (fp:int) (regions:(cm_region)list) (ret:cm_type)) = F)`);


PROOF thm cm_phase_oldfp_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_oldfp CAHaltP = 0i) &&
     (!ty. cm_phase_oldfp (CALoadP (ty:cm_type)) = 0i) &&
     (!src ty. cm_phase_oldfp (CAAssignLP (src:cm_expr) (ty:cm_type)) = 0i) &&
     (!ptr ty. cm_phase_oldfp (CAAssignRP (ptr:cm_value) (ty:cm_type)) = 0i) &&
     (!op left right ty. cm_phase_oldfp
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = 0i) &&
     (!op left right value ty. cm_phase_oldfp
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = 0i) &&
     (!op. cm_phase_oldfp (CAUnaryP (op:int)) = 0i) &&
     (!index ty. cm_phase_oldfp
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = 0i) &&
     (!base ty. cm_phase_oldfp
        (CAIndexRP (base:cm_value) (ty:cm_type)) = 0i) &&
     (!mid ty. cm_phase_oldfp (CAMemberP (mid:int) (ty:cm_type)) = 0i) &&
     (cm_phase_oldfp CAPutcP = 0i) &&
     (cm_phase_oldfp CAPutiP = 0i) &&
     (cm_phase_oldfp CAExitP = 0i) &&
     (cm_phase_oldfp CAExprStmtP = 0i) &&
     (!slot. cm_phase_oldfp (CAInitP (slot:int)) = 0i) &&
     (!env regions jump target. cm_phase_oldfp
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = 0i) &&
     (!second. cm_phase_oldfp (CASeqP (second:cm_stmt)) = 0i) &&
     (!yes no. cm_phase_oldfp
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = 0i) &&
     (!guard body loop_start loop_end. cm_phase_oldfp
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = 0i) &&
     (!guard body env regions loop_start loop_end. cm_phase_oldfp
        (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)
          (loop_start:int) (loop_end:int)) = 0i) &&
     (cm_phase_oldfp CAReturnP = 0i) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_oldfp
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = 0i) &&
     (!caller env fp regions ret. cm_phase_oldfp
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = fp)`);

PROOF thm cm_phase_oldregions_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_oldregions CAHaltP = ([]:(cm_region)list)) &&
     (!ty. cm_phase_oldregions (CALoadP (ty:cm_type)) = []) &&
     (!src ty. cm_phase_oldregions (CAAssignLP (src:cm_expr) (ty:cm_type)) = []) &&
     (!ptr ty. cm_phase_oldregions (CAAssignRP (ptr:cm_value) (ty:cm_type)) = []) &&
     (!op left right ty. cm_phase_oldregions
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = []) &&
     (!op left right value ty. cm_phase_oldregions
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = []) &&
     (!op. cm_phase_oldregions (CAUnaryP (op:int)) = []) &&
     (!index ty. cm_phase_oldregions
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = []) &&
     (!base ty. cm_phase_oldregions
        (CAIndexRP (base:cm_value) (ty:cm_type)) = []) &&
     (!mid ty. cm_phase_oldregions (CAMemberP (mid:int) (ty:cm_type)) = []) &&
     (cm_phase_oldregions CAPutcP = []) &&
     (cm_phase_oldregions CAPutiP = []) &&
     (cm_phase_oldregions CAExitP = []) &&
     (cm_phase_oldregions CAExprStmtP = []) &&
     (!slot. cm_phase_oldregions (CAInitP (slot:int)) = []) &&
     (!env regions jump target. cm_phase_oldregions
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = regions) &&
     (!second. cm_phase_oldregions (CASeqP (second:cm_stmt)) = []) &&
     (!yes no. cm_phase_oldregions
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = []) &&
     (!guard body loop_start loop_end. cm_phase_oldregions
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = []) &&
     (!guard body env regions loop_start loop_end. cm_phase_oldregions
        (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)
          (loop_start:int) (loop_end:int)) = regions) &&
     (cm_phase_oldregions CAReturnP = []) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_oldregions
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = []) &&
     (!caller env fp regions ret. cm_phase_oldregions
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = regions)`);

PROOF thm cm_regions_before_def = new_fun_definition(
    `cm_regions_before (regions:(cm_region)list) (limit:int) : bool =
       !region. MEM region regions ==> cm_region_gen region < limit`);

PROOF thm cm_region_frame_safe_def = new_fun_definition(
    `cm_region_frame_safe (p:cm_program) (all_regions:(cm_region)list)
       (fid:int) (fp:int) (region:cm_region) : bool =
       (~cm_region_live region ||
        (0i <= cm_region_lo region &&
         cm_region_lo region <= cm_region_hi region &&
        (fp + 8i <=
           cm_region_base all_regions (cm_region_gen region) +
             cm_region_lo region &&
         cm_region_base all_regions (cm_region_gen region) +
             cm_region_hi region <=
           fp + cm_temp_offset p fid 0i)))`);

PROOF thm cm_region_prefix_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p all_regions fid fp old.
        cm_region_prefix_safe (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          ([]:(cm_region)list) (old:(cm_region)list) <=> old == []) &&
     (!p all_regions fid fp region rest old.
        cm_region_prefix_safe p all_regions fid fp
          ((region:cm_region) :: (rest:(cm_region)list)) old <=>
        (if region :: rest == old then T
         else cm_region_frame_safe p all_regions fid fp region &&
              cm_region_prefix_safe p all_regions fid fp rest old))`);

PROOF thm cm_region_dead_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!old.
        cm_region_dead_prefix ([]:(cm_region)list)
          (old:(cm_region)list) <=> old == []) &&
     (!region rest old.
        cm_region_dead_prefix
          ((region:cm_region) :: (rest:(cm_region)list)) old <=>
        (if region :: rest == old then T
         else ~cm_region_live region &&
              cm_region_dead_prefix rest old))`);

PROOF thm cm_static_regions_layout_def = new_fun_definition(
    `cm_static_regions_layout (p:cm_program)
       (all_regions:(cm_region)list) : bool =
       !region.
         MEM region (cm_static_regions p) &&
         cm_region_live region ==>
         0i <= cm_region_lo region &&
         cm_region_lo region <= cm_region_hi region &&
         16i <= cm_region_base all_regions (cm_region_gen region) +
                  cm_region_lo region &&
         cm_region_base all_regions (cm_region_gen region) +
                  cm_region_hi region <= cm_static_size p`);

PROOF thm cm_frame_segment_def = new_fun_definition(
    `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
       (oldfp:int) : bool =
       (0i <= fid && fid < ilength (cm_program_functions p) &&
        16i <= cm_static_size p && cm_static_size p <= fp &&
        fp + cm_frame_size (cm_program_structs p)
          (inth fid (cm_program_functions p)) == oldfp &&
        fp + 8i <= fp + cm_temp_offset p fid 0i &&
        fp + cm_temp_offset p fid 0i <= oldfp &&
        oldfp <= 1048576i)`);

PROOF thm cm_spills_within_frame_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid fp oldfp.
        cm_spills_within_frame (p:cm_program) (fid:int) (fp:int)
          (oldfp:int) ([]:(cm_spill)list) <=> T) &&
     (!p fid fp oldfp spill rest.
        cm_spills_within_frame p fid fp oldfp
          ((spill:cm_spill) :: (rest:(cm_spill)list)) <=>
        fp + cm_temp_offset p fid 0i <=
          fp + cm_temp_offset p fid (cm_spill_slot spill) &&
        fp + cm_temp_offset p fid (cm_spill_slot spill) + 8i <= oldfp &&
        cm_spills_within_frame p fid fp oldfp rest)`);


PROOF thm cm_call_frames_lower_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!lower. cm_call_frames_lower (lower:int)
        ([]:(cm_call_sim_frame)list) <=> T) &&
     (!lower frame rest.
        cm_call_frames_lower (lower:int)
          ((frame:cm_call_sim_frame) :: rest) <=>
        lower <= cm_call_sim_base frame &&
        cm_call_frames_lower lower rest)`);

PROOF thm cm_spill_list_lower_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p lower fid fp.
        cm_spill_list_lower (p:cm_program) (lower:int)
          (fid:int) (fp:int) ([]:(cm_spill)list) <=> T) &&
     (!p lower fid fp spill rest.
        cm_spill_list_lower p lower fid fp
          ((spill:cm_spill) :: rest) <=>
        lower <= fp + cm_temp_offset p fid (cm_spill_slot spill) &&
        cm_spill_list_lower p lower fid fp rest)`);

PROOF thm cm_spill_frames_lower_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p lower. cm_spill_frames_lower (p:cm_program) (lower:int)
        ([]:(cm_spill_frame)list) <=> T) &&
     (!p lower frame rest.
        cm_spill_frames_lower p lower
          ((frame:cm_spill_frame) :: rest) <=>
        cm_spill_list_lower p lower
          (cm_spill_frame_fid frame) (cm_spill_frame_fp frame)
          (cm_spill_frame_spills frame) &&
        cm_spill_frames_lower p lower rest)`);
PROOF thm cm_runtime_stack_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p all_regions fid fp active spills saved calls.
        cm_runtime_stack (p:cm_program) (all_regions:(cm_region)list)
          (fid:int) (fp:int) (active:(cm_region)list)
          ([]:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list) <=> F) &&
     (!p all_regions fid fp active cursor rest spills saved calls.
        cm_runtime_stack p all_regions fid fp active
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list))
          spills saved calls <=>
        (if cm_phase_is_call (cm_cursor_phase cursor)
         then
           cm_region_prefix_safe p all_regions fid fp active
             (cm_phase_oldregions (cm_cursor_phase cursor)) &&
           cm_frame_segment p fid fp
             (cm_phase_oldfp (cm_cursor_phase cursor)) &&
           cm_spills_within_frame p fid fp
             (cm_phase_oldfp (cm_cursor_phase cursor)) spills &&
           ~(saved == []) && ~(calls == []) &&
           cm_call_sim_base (HD calls) == fp &&
           cm_call_sim_saved (HD calls) ==
             cm_phase_oldfp (cm_cursor_phase cursor) &&
           cm_spill_frame_fid (HD saved) ==
             cm_phase_caller (cm_cursor_phase cursor) &&
           cm_spill_frame_fp (HD saved) ==
             cm_phase_oldfp (cm_cursor_phase cursor) &&
           cm_runtime_stack p all_regions
             (cm_phase_caller (cm_cursor_phase cursor))
             (cm_phase_oldfp (cm_cursor_phase cursor))
             (cm_phase_oldregions (cm_cursor_phase cursor)) rest
             (cm_spill_frame_spills (HD saved))
             (TL saved) (TL calls)
         else if cm_phase_is_scope (cm_cursor_phase cursor)
              then
                0i <= fid &&
                cm_region_prefix_safe p all_regions fid fp active
                  (cm_phase_oldregions (cm_cursor_phase cursor)) &&
                cm_runtime_stack p all_regions fid fp
                  (cm_phase_oldregions (cm_cursor_phase cursor)) rest
                  spills saved calls
              else if cm_phase_is_halt (cm_cursor_phase cursor)
                   then fid == --1i && fp == 1048576i &&
                        cm_region_dead_prefix active
                          (cm_static_regions p) &&
                        16i <= cm_static_size p &&
                        cm_static_size p <= 1048576i &&
                        rest == [] && spills == [] &&
                        saved == [] && calls == [] &&
                        cm_static_regions_layout p all_regions
                   else cm_runtime_stack p all_regions fid fp active rest
                          spills saved calls))`);

PROOF thm cm_task_runtime_invariant_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p0 input p ann.
        cm_task_runtime_invariant (p:cm_program)
          (CMStartTask (p0:cm_program) (input:(int)list))
          (ann:cm_annotation) <=>
        p0 == p && ann == cm_initial_annotation) &&
     (!p0 fid expr st ks p ann.
        cm_task_runtime_invariant p
          (CMRTask (p0:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann <=>
        p0 == p &&
        cm_regions_before (cm_state_regions st) (cm_state_nextgen st) &&
        cm_runtime_stack p (cm_state_regions st) fid (cm_state_fp st)
          (cm_state_regions st) (cm_ann_cursors ann)
          (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)) &&
     (!p0 fid expr st ks p ann.
        cm_task_runtime_invariant p
          (CMLTask (p0:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann <=>
        p0 == p &&
        cm_regions_before (cm_state_regions st) (cm_state_nextgen st) &&
        cm_runtime_stack p (cm_state_regions st) fid (cm_state_fp st)
          (cm_state_regions st) (cm_ann_cursors ann)
          (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)) &&
     (!p0 fid stmt st ks p ann.
        cm_task_runtime_invariant p
          (CMSTask (p0:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) ann <=>
        p0 == p &&
        cm_regions_before (cm_state_regions st) (cm_state_nextgen st) &&
        cm_runtime_stack p (cm_state_regions st) fid (cm_state_fp st)
          (cm_state_regions st) (cm_ann_cursors ann)
          (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)) &&
     (!p0 fid value st ks p ann.
        cm_task_runtime_invariant p
          (CMVTask (p0:cm_program) (fid:int) (value:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) ann <=>
        p0 == p &&
        cm_regions_before (cm_state_regions st) (cm_state_nextgen st) &&
        cm_runtime_stack p (cm_state_regions st) fid (cm_state_fp st)
          (cm_state_regions st) (cm_ann_cursors ann)
          (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)) &&
     (!p0 fid control st ks p ann.
        cm_task_runtime_invariant p
          (CMCTask (p0:cm_program) (fid:int) (control:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) ann <=>
        p0 == p &&
        cm_regions_before (cm_state_regions st) (cm_state_nextgen st) &&
        cm_runtime_stack p (cm_state_regions st) fid (cm_state_fp st)
          (cm_state_regions st) (cm_ann_cursors ann)
          (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)) &&
     (!st control status p ann.
        cm_task_runtime_invariant (p:cm_program)
          (CMDoneTask (st:cm_src_state) (control:cm_control) (status:int))
          (ann:cm_annotation) <=>
        cm_regions_before
          (cm_state_regions st) (cm_state_nextgen st))`);


PROOF static thm cm_prove_region_prefix_member(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list) (fid:int) (fp:int)
         (active:(cm_region)list) (old:(cm_region)list)
         (region:cm_region).
         cm_region_prefix_safe p all_regions fid fp active old ==>
         MEM region active ==>
         cm_region_live region ==>
         MEM region old ||
         cm_region_frame_safe p all_regions fid fp region`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_theorem_by_name("MEM"))),
        assume_rule(goal_lasmps(leaf->g)[1].tm));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list equal_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (old:(cm_region)list)`);
      thm member = assume_rule(
          `MEM (region:cm_region)
             ((a0:cm_region) :: (a1:(cm_region)list))`);
      ACCEPT_TAC(equal_cases[0],
          disj1_rule(conv_rule(rewrite_conv(THM_LIST(boundary)), member),
            `cm_region_frame_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (region:cm_region)`));
    }
    {
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def,
          assume_rule(
            `~((a0:cm_region) :: (a1:(cm_region)list) ==
                (old:(cm_region)list))`))),
          assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm head_safe = conjunct1_rule(opened);
      thm tail_safe = conjunct2_rule(opened);
      thm member = conv_rule(rewrite_conv(THM_LIST(
          get_theorem_by_name("MEM"))), assume_rule(
            `MEM (region:cm_region)
              ((a0:cm_region) :: (a1:(cm_region)list))`));
      gnode_list member_cases =
          DISJ_CASES_TAC(equal_cases[1], member, "Hmember");
      {
        thm head = assume_rule(
            `(region:cm_region) == (a0:cm_region)`);
        ACCEPT_TAC(member_cases[0], disj2_rule(
            `MEM (region:cm_region) (old:(cm_region)list)`,
            conv_rule(rewrite_conv(THM_LIST(sym_rule(head))),
              head_safe)));
      }
      {
        thm ih = specl_rule(TERM_LIST(
            `old:(cm_region)list`, `region:cm_region`),
            assume_rule(goal_lasmps(member_cases[1]->g)[0].tm));
        thm result = match_mp_rule(
            match_mp_rule(match_mp_rule(ih, tail_safe),
              assume_rule(
                `MEM (region:cm_region) (a1:(cm_region)list)`)),
            assume_rule(`cm_region_live (region:cm_region)`));
        ACCEPT_TAC(member_cases[1], result);
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_member =
    cm_prove_region_prefix_member();

PROOF static thm cm_prove_region_dead_prefix_live_member(void) {
  gnode root = gnode_new_with_ccl(
      `!(active:(cm_region)list) (old:(cm_region)list)
         (region:cm_region).
         cm_region_dead_prefix active old ==>
         MEM region active ==>
         cm_region_live region ==>
         MEM region old`);
  gnode with_active = GEN_TAC(root, "active");
  gnode_list cases =
      INDUCT_TAC(with_active, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_theorem_by_name("MEM"))),
        assume_rule(goal_lasmps(leaf->g)[1].tm));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list equal_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (old:(cm_region)list)`);
      thm member = assume_rule(
          `MEM (region:cm_region)
             ((a0:cm_region) :: (a1:(cm_region)list))`);
      ACCEPT_TAC(equal_cases[0],
          conv_rule(rewrite_conv(THM_LIST(boundary)), member));
    }
    {
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_dead_prefix_def,
          assume_rule(
            `~((a0:cm_region) :: (a1:(cm_region)list) ==
                (old:(cm_region)list))`))),
          assume_rule(
            `cm_region_dead_prefix
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm member = conv_rule(rewrite_conv(THM_LIST(
          get_theorem_by_name("MEM"))), assume_rule(
            `MEM (region:cm_region)
              ((a0:cm_region) :: (a1:(cm_region)list))`));
      gnode_list member_cases =
          DISJ_CASES_TAC(equal_cases[1], member, "Hmember");
      {
        thm head = assume_rule(
            `(region:cm_region) == (a0:cm_region)`);
        thm live_head = conv_rule(rewrite_conv(THM_LIST(head)),
            assume_rule(`cm_region_live (region:cm_region)`));
        CONTR_TAC(member_cases[0],
            contra(conjunct1_rule(opened), live_head));
      }
      {
        thm ih = specl_rule(TERM_LIST(
            `old:(cm_region)list`, `region:cm_region`),
            assume_rule(goal_lasmps(member_cases[1]->g)[0].tm));
        thm result = match_mp_rule(
            match_mp_rule(match_mp_rule(ih, conjunct2_rule(opened)),
              assume_rule(
                `MEM (region:cm_region) (a1:(cm_region)list)`)),
            assume_rule(`cm_region_live (region:cm_region)`));
        ACCEPT_TAC(member_cases[1], result);
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_dead_prefix_live_member =
    cm_prove_region_dead_prefix_live_member();


PROOF static thm cm_invariant_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)),
      premise);
}
PROOF static thm cm_prove_call_frames_lower_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(lower:int) upper (frames:(cm_call_sim_frame)list).
         lower <= upper ==>
         cm_call_frames_lower upper frames ==>
         cm_call_frames_lower lower frames`);
  gnode with_lower = GEN_TAC(root, "lower");
  gnode with_upper = GEN_TAC(with_lower, "upper");
  gnode_list cases = INDUCT_TAC(
      with_upper, `frames:(cm_call_sim_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_call_frames_lower_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_call_frames_lower_def)), assume_rule(
          `cm_call_frames_lower (upper:int)
            ((a0:cm_call_sim_frame) ::
             (a1:(cm_call_sim_frame)list))`));
    thm head = mp_rule(mp_rule(int_arith_rule(
        `(lower:int) <= (upper:int) ==>
         upper <= cm_call_sim_base (a0:cm_call_sim_frame) ==>
         lower <= cm_call_sim_base a0`),
        assume_rule(`(lower:int) <= (upper:int)`)),
        conjunct1_rule(opened));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `(lower:int) <= (upper:int) ==>
           cm_call_frames_lower upper
             (a1:(cm_call_sim_frame)list) ==>
           cm_call_frames_lower lower a1`),
          assume_rule(`(lower:int) <= (upper:int)`)),
        conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_call_frames_lower_def)));
    ACCEPT_TAC(reduced, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_call_frames_lower_mono =
    cm_prove_call_frames_lower_mono();

PROOF static thm cm_prove_spill_list_lower_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (lower:int) upper fid fp
         (spills:(cm_spill)list).
         lower <= upper ==>
         cm_spill_list_lower p upper fid fp spills ==>
         cm_spill_list_lower p lower fid fp spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_lower = GEN_TAC(with_program, "lower");
  gnode with_upper = GEN_TAC(with_lower, "upper");
  gnode with_fid = GEN_TAC(with_upper, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)), assume_rule(
          `cm_spill_list_lower (p:cm_program) (upper:int)
            (fid:int) (fp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm head = mp_rule(mp_rule(int_arith_rule(
        `(lower:int) <= (upper:int) ==>
         upper <= (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
           (cm_spill_slot (a0:cm_spill)) ==>
         lower <= fp + cm_temp_offset p fid (cm_spill_slot a0)`),
        assume_rule(`(lower:int) <= (upper:int)`)),
        conjunct1_rule(opened));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `(lower:int) <= (upper:int) ==>
           cm_spill_list_lower (p:cm_program) upper
             (fid:int) (fp:int) (a1:(cm_spill)list) ==>
           cm_spill_list_lower p lower fid fp a1`),
          assume_rule(`(lower:int) <= (upper:int)`)),
        conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)));
    ACCEPT_TAC(reduced, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_list_lower_mono =
    cm_prove_spill_list_lower_mono();

PROOF static thm cm_prove_spill_frames_lower_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (lower:int) upper
         (frames:(cm_spill_frame)list).
         lower <= upper ==>
         cm_spill_frames_lower p upper frames ==>
         cm_spill_frames_lower p lower frames`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_lower = GEN_TAC(with_program, "lower");
  gnode with_upper = GEN_TAC(with_lower, "upper");
  gnode_list cases =
      INDUCT_TAC(with_upper, `frames:(cm_spill_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_frames_lower_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_spill_frames_lower_def)), assume_rule(
          `cm_spill_frames_lower (p:cm_program) (upper:int)
            ((a0:cm_spill_frame) ::
             (a1:(cm_spill_frame)list))`));
    thm head = match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `lower:int`, `upper:int`,
          `cm_spill_frame_fid (a0:cm_spill_frame)`,
          `cm_spill_frame_fp (a0:cm_spill_frame)`,
          `cm_spill_frame_spills (a0:cm_spill_frame)`),
          cm_spill_list_lower_mono),
          assume_rule(`(lower:int) <= (upper:int)`)),
        conjunct1_rule(opened));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `(lower:int) <= (upper:int) ==>
           cm_spill_frames_lower (p:cm_program) upper
             (a1:(cm_spill_frame)list) ==>
           cm_spill_frames_lower p lower a1`),
          assume_rule(`(lower:int) <= (upper:int)`)),
        conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_frames_lower_def)));
    ACCEPT_TAC(reduced, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_frames_lower_mono =
    cm_prove_spill_frames_lower_mono();

PROOF static thm cm_prove_spills_within_lower(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid fp oldfp (spills:(cm_spill)list).
         cm_frame_segment p fid fp oldfp ==>
         cm_spills_within_frame p fid fp oldfp spills ==>
         cm_spill_list_lower p fp fid fp spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_fid = GEN_TAC(with_program, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_oldfp = GEN_TAC(with_fp, "oldfp");
  gnode_list cases =
      INDUCT_TAC(with_oldfp, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm segment = conv_rule(rewrite_conv(
        THM_LIST(cm_frame_segment_def)), assume_rule(
          `cm_frame_segment (p:cm_program) (fid:int)
            (fp:int) (oldfp:int)`));
    thm within = conv_rule(rewrite_conv(
        THM_LIST(cm_spills_within_frame_def)), assume_rule(
          `cm_spills_within_frame (p:cm_program) (fid:int)
            (fp:int) (oldfp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm head = mp_rule(mp_rule(int_arith_rule(
        `(fp:int) + 8i <= fp +
             cm_temp_offset (p:cm_program) (fid:int) 0i ==>
         fp + cm_temp_offset p fid 0i <=
             fp + cm_temp_offset p fid (cm_spill_slot (a0:cm_spill)) ==>
         fp <= fp + cm_temp_offset p fid (cm_spill_slot a0)`),
        cm_invariant_consequence(segment,
          `(fp:int) + 8i <= fp +
            cm_temp_offset (p:cm_program) (fid:int) 0i`)),
        conjunct1_rule(within));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `cm_frame_segment (p:cm_program) (fid:int)
             (fp:int) (oldfp:int) ==>
           cm_spills_within_frame p fid fp oldfp
             (a1:(cm_spill)list) ==>
           cm_spill_list_lower p fp fid fp a1`),
          assume_rule(
            `cm_frame_segment (p:cm_program) (fid:int)
              (fp:int) (oldfp:int)`)),
        conjunct2_rule(conjunct2_rule(within)));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)));
    ACCEPT_TAC(reduced, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_within_lower =
    cm_prove_spills_within_lower();


PROOF static thm cm_prove_runtime_stack_lower(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) fid fp
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         cm_call_frames_lower fp calls &&
         cm_spill_list_lower p fp fid fp spills &&
         cm_spill_frames_lower p fp saved`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm stack = assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            ((a0:cm_acursor) :: (a1:(cm_acursor)list))
            (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm segment = cm_invariant_consequence(opened,
          `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
            (cm_phase_oldfp ${phase:cm_aphase})`);
      thm within = cm_invariant_consequence(opened,
          `cm_spills_within_frame (p:cm_program) (fid:int) (fp:int)
            (cm_phase_oldfp ${phase:cm_aphase})
            (spills:(cm_spill)list)`);
      thm saved_nonempty = cm_invariant_consequence(opened,
          `~((saved:(cm_spill_frame)list) == [])`);
      thm calls_nonempty = cm_invariant_consequence(opened,
          `~((calls:(cm_call_sim_frame)list) == [])`);
      thm recursive = cm_invariant_consequence(opened,
          `cm_runtime_stack (p:cm_program)
             (all_regions:(cm_region)list)
             (cm_phase_caller ${phase:cm_aphase})
             (cm_phase_oldfp ${phase:cm_aphase})
             (cm_phase_oldregions ${phase:cm_aphase})
             (a1:(cm_acursor)list)
             (cm_spill_frame_spills
               (HD (saved:(cm_spill_frame)list)))
             (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
      thm ih = specl_rule(TERM_LIST(
          `cm_phase_caller ${phase:cm_aphase}`,
          `cm_phase_oldfp ${phase:cm_aphase}`,
          `cm_phase_oldregions ${phase:cm_aphase}`,
          `cm_spill_frame_spills
            (HD (saved:(cm_spill_frame)list))`,
          `TL (saved:(cm_spill_frame)list)`,
          `TL (calls:(cm_call_sim_frame)list)`),
          assume_rule(goal_lasmps(call_cases[0]->g)[0].tm));
      thm outer = match_mp_rule(ih, recursive);
      thm frame_parts = conv_rule(rewrite_conv(
          THM_LIST(cm_frame_segment_def)), segment);
      thm fp_oldfp = int_arith_rule(
          `(fp:int) + 8i <=
               fp + cm_temp_offset (p:cm_program) (fid:int) 0i ==>
           fp + cm_temp_offset p fid 0i <=
               cm_phase_oldfp (${phase:cm_aphase}) ==>
           fp <= cm_phase_oldfp ${phase:cm_aphase}`);
      fp_oldfp = mp_rule(fp_oldfp, cm_invariant_consequence(
          frame_parts,
          `(fp:int) + 8i <=
             fp + cm_temp_offset (p:cm_program) (fid:int) 0i`));
      fp_oldfp = mp_rule(fp_oldfp, cm_invariant_consequence(
          frame_parts,
          `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
             cm_phase_oldfp ${phase:cm_aphase}`));

      thm call_base = cm_invariant_consequence(opened,
          `cm_call_sim_base
             (HD (calls:(cm_call_sim_frame)list)) == (fp:int)`);
      thm call_head = mp_rule(int_arith_rule(
          `cm_call_sim_base
             (HD (calls:(cm_call_sim_frame)list)) == (fp:int) ==>
           fp <= cm_call_sim_base (HD calls)`), call_base);
      thm call_tail = match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `fp:int`, `cm_phase_oldfp ${phase:cm_aphase}`,
            `TL (calls:(cm_call_sim_frame)list)`),
            cm_call_frames_lower_mono), fp_oldfp),
          cm_invariant_consequence(outer,
            `cm_call_frames_lower
              (cm_phase_oldfp ${phase:cm_aphase})
              (TL (calls:(cm_call_sim_frame)list))`));
      thm calls_unfolded = apply_conversion(rewrite_conv(
          THM_LIST(cm_call_frames_lower_def)),
          `cm_call_frames_lower (fp:int)
             (HD (calls:(cm_call_sim_frame)list) :: TL calls)`);
      thm calls_cons = eq_mp_rule(sym_rule(calls_unfolded),
          conj_rule(call_head, call_tail));
      thm calls_shape = mp_rule(
          ispec_rule(`calls:(cm_call_sim_frame)list`,
            get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
      thm calls_lower = eq_mp_rule(sym_rule(ap_term_rule(
          `cm_call_frames_lower (fp:int)`, calls_shape)), calls_cons);

      thm current_spills = match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `fp:int`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `spills:(cm_spill)list`), cm_spills_within_lower),
            segment), within);

      thm saved_head_outer = cm_invariant_consequence(outer,
          `cm_spill_list_lower (p:cm_program)
             (cm_phase_oldfp ${phase:cm_aphase})
             (cm_phase_caller ${phase:cm_aphase})
             (cm_phase_oldfp ${phase:cm_aphase})
             (cm_spill_frame_spills
               (HD (saved:(cm_spill_frame)list)))`);
      thm saved_head_lower = match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fp:int`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `cm_phase_caller ${phase:cm_aphase}`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list))`),
            cm_spill_list_lower_mono), fp_oldfp),
          saved_head_outer);
      thm saved_fid = cm_invariant_consequence(opened,
          `cm_spill_frame_fid
             (HD (saved:(cm_spill_frame)list)) ==
           cm_phase_caller ${phase:cm_aphase}`);
      thm saved_fp = cm_invariant_consequence(opened,
          `cm_spill_frame_fp
             (HD (saved:(cm_spill_frame)list)) ==
           cm_phase_oldfp ${phase:cm_aphase}`);
      saved_head_lower = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(saved_fid), sym_rule(saved_fp))),
          saved_head_lower);
      thm saved_tail_lower = match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fp:int`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `TL (saved:(cm_spill_frame)list)`),
            cm_spill_frames_lower_mono), fp_oldfp),
          cm_invariant_consequence(outer,
            `cm_spill_frames_lower (p:cm_program)
              (cm_phase_oldfp ${phase:cm_aphase})
              (TL (saved:(cm_spill_frame)list))`));
      thm saved_unfolded = apply_conversion(rewrite_conv(
          THM_LIST(cm_spill_frames_lower_def)),
          `cm_spill_frames_lower (p:cm_program) (fp:int)
             (HD (saved:(cm_spill_frame)list) :: TL saved)`);
      thm saved_cons = eq_mp_rule(sym_rule(saved_unfolded),
          conj_rule(saved_head_lower, saved_tail_lower));
      thm saved_shape = mp_rule(
          ispec_rule(`saved:(cm_spill_frame)list`,
            get_theorem_by_name("CONS_HD_TL")), saved_nonempty);
      thm saved_lower = eq_mp_rule(sym_rule(ap_term_rule(
          `cm_spill_frames_lower (p:cm_program) (fp:int)`,
          saved_shape)), saved_cons);
      ACCEPT_TAC(call_cases[0], conj_rule(calls_lower,
          conj_rule(current_spills, saved_lower)));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm stack = assume_rule(
            `cm_runtime_stack (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              ((a0:cm_acursor) :: (a1:(cm_acursor)list))
              (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        ACCEPT_TAC(scope_cases[0], match_mp_rule(ih, recursive));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          gnode reduced = CONV_TAC(halt_cases[0],
              reduce_rewrite_conv(THM_LIST(
                cm_call_frames_lower_def,
                cm_spill_list_lower_def,
                cm_spill_frames_lower_def,
                cm_invariant_consequence(opened,
                  `(spills:(cm_spill)list) == []`),
                cm_invariant_consequence(opened,
                  `(saved:(cm_spill_frame)list) == []`),
                cm_invariant_consequence(opened,
                  `(calls:(cm_call_sim_frame)list) == []`))));
          (void)reduced;
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          ACCEPT_TAC(halt_cases[1], match_mp_rule(ih, recursive));
        }
      }
    }
  }

  return gnode_prove(root);
}
PROOF static thm cm_prove_call_lower_range_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) width lower
         (frames:(cm_call_sim_frame)list).
         base + width <= lower ==>
         cm_call_frames_lower lower frames ==>
         cm_call_frames_range_safe base width frames`);
  gnode with_base = GEN_TAC(root, "base");
  gnode with_width = GEN_TAC(with_base, "width");
  gnode with_lower = GEN_TAC(with_width, "lower");
  gnode_list cases = INDUCT_TAC(
      with_lower, `frames:(cm_call_sim_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_call_frames_range_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_call_frames_lower_def)), assume_rule(
          `cm_call_frames_lower (lower:int)
            ((a0:cm_call_sim_frame) ::
             (a1:(cm_call_sim_frame)list))`));
    thm head = mp_rule(mp_rule(int_arith_rule(
        `(base:int) + (width:int) <= (lower:int) ==>
         lower <= cm_call_sim_base (a0:cm_call_sim_frame) ==>
         base + width <= cm_call_sim_base a0 ||
         cm_call_sim_base a0 + 8i <= base`),
        assume_rule(
          `(base:int) + (width:int) <= (lower:int)`)),
        conjunct1_rule(opened));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `(base:int) + (width:int) <= (lower:int) ==>
           cm_call_frames_lower lower
             (a1:(cm_call_sim_frame)list) ==>
           cm_call_frames_range_safe base width a1`),
          assume_rule(
            `(base:int) + (width:int) <= (lower:int)`)),
        conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_call_frames_range_safe_def, cm_range_disjoint_def)));
    ACCEPT_TAC(reduced, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_call_lower_range_safe =
    cm_prove_call_lower_range_safe();

PROOF static thm cm_prove_spill_list_lower_range_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (base:int) width lower fid fp
         (spills:(cm_spill)list).
         base + width <= lower ==>
         cm_spill_list_lower p lower fid fp spills ==>
         cm_spill_list_range_safe p fid fp base width spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_base = GEN_TAC(with_program, "base");
  gnode with_width = GEN_TAC(with_base, "width");
  gnode with_lower = GEN_TAC(with_width, "lower");
  gnode with_fid = GEN_TAC(with_lower, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_list_range_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)), assume_rule(
          `cm_spill_list_lower (p:cm_program) (lower:int)
            (fid:int) (fp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm head = mp_rule(mp_rule(int_arith_rule(
        `(base:int) + (width:int) <= (lower:int) ==>
         lower <=
           (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
             (cm_spill_slot (a0:cm_spill)) ==>
         base + width <=
             fp + cm_temp_offset p fid (cm_spill_slot a0) ||
         (fp + cm_temp_offset p fid (cm_spill_slot a0)) + 8i <=
             base`),
        assume_rule(
          `(base:int) + (width:int) <= (lower:int)`)),
        conjunct1_rule(opened));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `(base:int) + (width:int) <= (lower:int) ==>
           cm_spill_list_lower (p:cm_program) lower
             (fid:int) (fp:int) (a1:(cm_spill)list) ==>
           cm_spill_list_range_safe p fid fp base width a1`),
          assume_rule(
            `(base:int) + (width:int) <= (lower:int)`)),
        conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_list_range_safe_def)));
    gnode_list parts = CONJ_TAC(reduced);
    gnode disjoint = CONV_TAC(parts[0], rewrite_conv(
        THM_LIST(cm_range_disjoint_def)));
    ACCEPT_TAC(disjoint, head);
    ACCEPT_TAC(parts[1], tail);
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_list_lower_range_safe =
    cm_prove_spill_list_lower_range_safe();

PROOF static thm cm_prove_spill_frames_lower_range_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (base:int) width lower
         (frames:(cm_spill_frame)list).
         base + width <= lower ==>
         cm_spill_frames_lower p lower frames ==>
         cm_spill_frames_range_safe p base width frames`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_base = GEN_TAC(with_program, "base");
  gnode with_width = GEN_TAC(with_base, "width");
  gnode with_lower = GEN_TAC(with_width, "lower");
  gnode_list cases = INDUCT_TAC(
      with_lower, `frames:(cm_spill_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_frames_range_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_spill_frames_lower_def)), assume_rule(
          `cm_spill_frames_lower (p:cm_program) (lower:int)
            ((a0:cm_spill_frame) ::
             (a1:(cm_spill_frame)list))`));
    thm head = match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `base:int`, `width:int`, `lower:int`,
          `cm_spill_frame_fid (a0:cm_spill_frame)`,
          `cm_spill_frame_fp (a0:cm_spill_frame)`,
          `cm_spill_frame_spills (a0:cm_spill_frame)`),
          cm_spill_list_lower_range_safe),
          assume_rule(
            `(base:int) + (width:int) <= (lower:int)`)),
        conjunct1_rule(opened));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `(base:int) + (width:int) <= (lower:int) ==>
           cm_spill_frames_lower (p:cm_program) lower
             (a1:(cm_spill_frame)list) ==>
           cm_spill_frames_range_safe p base width a1`),
          assume_rule(
            `(base:int) + (width:int) <= (lower:int)`)),
        conjunct2_rule(opened));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_frames_range_safe_def)));
    ACCEPT_TAC(reduced, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_frames_lower_range_safe =
    cm_prove_spill_frames_lower_range_safe();
PROOF thm cm_runtime_stack_lower =
    cm_prove_runtime_stack_lower();
PROOF static thm cm_prove_runtime_stack_fp_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) fid fp
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         16i <= cm_static_size p &&
         cm_static_size p <= fp && fp <= 1048576i`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm stack = assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            ((a0:cm_acursor) :: (a1:(cm_acursor)list))
            (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm segment = conv_rule(rewrite_conv(
          THM_LIST(cm_frame_segment_def)),
          cm_invariant_consequence(opened,
            `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
              (cm_phase_oldfp ${phase:cm_aphase})`));
      thm result = mp_rule(mp_rule(mp_rule(mp_rule(
          int_arith_rule(
            `16i <= cm_static_size (p:cm_program) ==>
             cm_static_size p <= (fp:int) ==>
             fp + 8i <= fp + cm_temp_offset p (fid:int) 0i ==>
             fp + cm_temp_offset p fid 0i <=
               cm_phase_oldfp (${phase:cm_aphase}) ==>
             cm_phase_oldfp ${phase:cm_aphase} <= 1048576i ==>
             16i <= cm_static_size p &&
             cm_static_size p <= fp && fp <= 1048576i`),
          cm_invariant_consequence(segment,
            `16i <= cm_static_size (p:cm_program)`)),
          cm_invariant_consequence(segment,
            `cm_static_size (p:cm_program) <= (fp:int)`)),
          cm_invariant_consequence(segment,
            `(fp:int) + 8i <=
              fp + cm_temp_offset (p:cm_program) (fid:int) 0i`)),
          cm_invariant_consequence(segment,
            `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
              cm_phase_oldfp ${phase:cm_aphase}`));
      result = mp_rule(result, cm_invariant_consequence(segment,
          `cm_phase_oldfp (${phase:cm_aphase}) <= 1048576i`));
      ACCEPT_TAC(call_cases[0], result);
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm stack = assume_rule(
            `cm_runtime_stack (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              ((a0:cm_acursor) :: (a1:(cm_acursor)list))
              (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        ACCEPT_TAC(scope_cases[0], match_mp_rule(ih, recursive));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm result = mp_rule(mp_rule(mp_rule(int_arith_rule(
              `16i <= cm_static_size (p:cm_program) ==>
               cm_static_size p <= 1048576i ==>
               (fp:int) == 1048576i ==>
               16i <= cm_static_size p &&
               cm_static_size p <= fp && fp <= 1048576i`),
              cm_invariant_consequence(opened,
                `16i <= cm_static_size (p:cm_program)`)),
              cm_invariant_consequence(opened,
                `cm_static_size (p:cm_program) <= 1048576i`)),
              cm_invariant_consequence(opened,
                `(fp:int) == 1048576i`));
          ACCEPT_TAC(halt_cases[0], result);
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          ACCEPT_TAC(halt_cases[1], match_mp_rule(ih, recursive));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_fp_bounds =
    cm_prove_runtime_stack_fp_bounds();

PROOF static thm cm_prove_runtime_stack_frame_ceiling(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) fid fp
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         fid == --1i ||
         fp + cm_temp_offset p fid 0i <= 1048576i`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm stack = assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            ((a0:cm_acursor) :: (a1:(cm_acursor)list))
            (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm segment = conv_rule(rewrite_conv(
          THM_LIST(cm_frame_segment_def)),
          cm_invariant_consequence(opened,
            `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
              (cm_phase_oldfp ${phase:cm_aphase})`));
      thm ceiling = mp_rule(mp_rule(int_arith_rule(
          `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
               cm_phase_oldfp (${phase:cm_aphase}) ==>
           cm_phase_oldfp ${phase:cm_aphase} <= 1048576i ==>
           fp + cm_temp_offset p fid 0i <= 1048576i`),
          cm_invariant_consequence(segment,
            `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
              cm_phase_oldfp ${phase:cm_aphase}`)),
          cm_invariant_consequence(segment,
            `cm_phase_oldfp (${phase:cm_aphase}) <= 1048576i`));
      ACCEPT_TAC(call_cases[0], disj2_rule(
          `(fid:int) == --1i`, ceiling));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm stack = assume_rule(
            `cm_runtime_stack (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              ((a0:cm_acursor) :: (a1:(cm_acursor)list))
              (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        ACCEPT_TAC(scope_cases[0], match_mp_rule(ih, recursive));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          ACCEPT_TAC(halt_cases[0], disj1_rule(
              cm_invariant_consequence(opened, `(fid:int) == --1i`),
              `(fp:int) + cm_temp_offset
                (p:cm_program) (fid:int) 0i <= 1048576i`));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          ACCEPT_TAC(halt_cases[1], match_mp_rule(ih, recursive));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_frame_ceiling =
    cm_prove_runtime_stack_frame_ceiling();
PROOF static thm cm_prove_runtime_stack_region_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) (fid:int) (fp:int)
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (region:cm_region).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         MEM region active ==>
         cm_region_live region ==>
         0i <= cm_region_lo region &&
         cm_region_lo region <= cm_region_hi region &&
         16i <= cm_region_base all_regions (cm_region_gen region) +
                   cm_region_lo region &&
         cm_region_base all_regions (cm_region_gen region) +
                  cm_region_hi region <= 1048576i &&
         (cm_region_base all_regions (cm_region_gen region) +
             cm_region_hi region <= cm_static_size p ||
          fp + 8i <=
            cm_region_base all_regions (cm_region_gen region) +
              cm_region_lo region)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm stack = assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            ((a0:cm_acursor) :: (a1:(cm_acursor)list))
            (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm prefix = cm_invariant_consequence(opened,
          `cm_region_prefix_safe (p:cm_program)
             (all_regions:(cm_region)list) (fid:int) (fp:int)
             (active:(cm_region)list)
             (cm_phase_oldregions ${phase:cm_aphase})`);
      thm segment = cm_invariant_consequence(opened,
          `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
             (cm_phase_oldfp ${phase:cm_aphase})`);
      thm recursive = cm_invariant_consequence(opened,
          `cm_runtime_stack (p:cm_program)
             (all_regions:(cm_region)list)
             (cm_phase_caller ${phase:cm_aphase})
             (cm_phase_oldfp ${phase:cm_aphase})
             (cm_phase_oldregions ${phase:cm_aphase})
             (a1:(cm_acursor)list)
             (cm_spill_frame_spills
               (HD (saved:(cm_spill_frame)list)))
             (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
      thm classified = match_mp_rule(
          match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `all_regions:(cm_region)list`,
            `fid:int`, `fp:int`, `active:(cm_region)list`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `region:cm_region`), cm_region_prefix_member), prefix),
            assume_rule(`MEM (region:cm_region)
              (active:(cm_region)list)`)),
          assume_rule(`cm_region_live (region:cm_region)`));
      gnode_list region_cases =
          DISJ_CASES_TAC(call_cases[0], classified, "Hregion");
      {
        thm ih = specl_rule(TERM_LIST(
            `cm_phase_caller ${phase:cm_aphase}`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list))`,
            `TL (saved:(cm_spill_frame)list)`,
            `TL (calls:(cm_call_sim_frame)list)`,
            `region:cm_region`),
            assume_rule(goal_lasmps(region_cases[0]->g)[0].tm));
        thm outer = match_mp_rule(
            match_mp_rule(match_mp_rule(ih, recursive),
              assume_rule(
                `MEM (region:cm_region)
                  (cm_phase_oldregions ${phase:cm_aphase})`)),
            assume_rule(`cm_region_live (region:cm_region)`));
        thm frame_parts = conv_rule(rewrite_conv(
            THM_LIST(cm_frame_segment_def)), segment);
        thm current_below_outer = int_arith_rule(
            `(fp:int) + 8i <=
               fp + cm_temp_offset (p:cm_program) (fid:int) 0i ==>
             fp + cm_temp_offset p fid 0i <=
               cm_phase_oldfp (${phase:cm_aphase}) ==>
             fp + 8i <= cm_phase_oldfp ${phase:cm_aphase}`);
        current_below_outer = mp_rule(current_below_outer,
            cm_invariant_consequence(frame_parts,
              `(fp:int) + 8i <=
                 fp + cm_temp_offset (p:cm_program) (fid:int) 0i`));
        current_below_outer = mp_rule(current_below_outer,
            cm_invariant_consequence(frame_parts,
              `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
                 cm_phase_oldfp ${phase:cm_aphase}`));
        term base =
            `cm_region_base (all_regions:(cm_region)list)
               (cm_region_gen (region:cm_region))`;
        thm outer_choice = cm_invariant_consequence(outer,
            `${base:int} + cm_region_hi (region:cm_region) <=
                 cm_static_size (p:cm_program) ||
             cm_phase_oldfp (${phase:cm_aphase}) + 8i <=
                 ${base:int} + cm_region_lo region`);
        thm current_choice = mp_rule(mp_rule(int_arith_rule(
            `(fp:int) + 8i <=
                 cm_phase_oldfp (${phase:cm_aphase}) ==>
             (${base:int} + cm_region_hi (region:cm_region) <=
                cm_static_size (p:cm_program) ||
              cm_phase_oldfp ${phase:cm_aphase} + 8i <=
                ${base:int} + cm_region_lo region) ==>
             (${base:int} + cm_region_hi region <= cm_static_size p ||
              fp + 8i <= ${base:int} + cm_region_lo region)`),
            current_below_outer), outer_choice);
        thm result = conj_rule(
            cm_invariant_consequence(outer,
              `0i <= cm_region_lo (region:cm_region)`),
            conj_rule(cm_invariant_consequence(outer,
              `cm_region_lo (region:cm_region) <= cm_region_hi region`),
            conj_rule(cm_invariant_consequence(outer,
              `16i <= ${base:int} + cm_region_lo (region:cm_region)`),
            conj_rule(cm_invariant_consequence(outer,
              `${base:int} + cm_region_hi (region:cm_region) <=
                 1048576i`),
              current_choice))));
        ACCEPT_TAC(region_cases[0], result);
      }
      {
        thm frame_safe = assume_rule(
            `cm_region_frame_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (region:cm_region)`);
        thm live = assume_rule(
            `cm_region_live (region:cm_region)`);
        thm safe_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_region_frame_safe_def, live)), frame_safe);
        thm frame_parts = conv_rule(rewrite_conv(
            THM_LIST(cm_frame_segment_def)), segment);
        term base =
            `cm_region_base (all_regions:(cm_region)list)
               (cm_region_gen (region:cm_region))`;
        thm lower = cm_invariant_consequence(safe_parts,
            `(fp:int) + 8i <=
              ${base:int} + cm_region_lo (region:cm_region)`);
        thm upper_data = cm_invariant_consequence(safe_parts,
            `${base:int} + cm_region_hi (region:cm_region) <=
              (fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i`);
        thm data_end = cm_invariant_consequence(frame_parts,
            `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
              cm_phase_oldfp ${phase:cm_aphase}`);
        thm outer_end = cm_invariant_consequence(frame_parts,
            `cm_phase_oldfp (${phase:cm_aphase}) <= 1048576i`);
        thm address_lower = mp_rule(mp_rule(mp_rule(int_arith_rule(
            `16i <= cm_static_size (p:cm_program) ==>
             cm_static_size p <= (fp:int) ==>
             fp + 8i <= (${base:int}) +
                 cm_region_lo (region:cm_region) ==>
             16i <= ${base:int} + cm_region_lo region`),
            cm_invariant_consequence(frame_parts,
              `16i <= cm_static_size (p:cm_program)`)),
            cm_invariant_consequence(frame_parts,
              `cm_static_size (p:cm_program) <= (fp:int)`)), lower);
        thm address_upper = mp_rule(mp_rule(mp_rule(int_arith_rule(
            `(${base:int}) + cm_region_hi (region:cm_region) <=
                 (fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i ==>
             fp + cm_temp_offset p fid 0i <=
                 cm_phase_oldfp (${phase:cm_aphase}) ==>
             cm_phase_oldfp ${phase:cm_aphase} <= 1048576i ==>
             ${base:int} + cm_region_hi region <= 1048576i`),
            upper_data), data_end), outer_end);
        thm result = conj_rule(
            cm_invariant_consequence(safe_parts,
              `0i <= cm_region_lo (region:cm_region)`),
            conj_rule(cm_invariant_consequence(safe_parts,
              `cm_region_lo (region:cm_region) <= cm_region_hi region`),
            conj_rule(address_lower,
            conj_rule(address_upper,
              disj2_rule(
                `${base:int} + cm_region_hi (region:cm_region) <=
                   cm_static_size (p:cm_program)`,
                lower)))));
        ACCEPT_TAC(region_cases[1], result);
      }
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm stack = assume_rule(
            `cm_runtime_stack (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              ((a0:cm_acursor) :: (a1:(cm_acursor)list))
              (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm fid_nonnegative = conjunct1_rule(opened);
        thm prefix = conjunct1_rule(conjunct2_rule(opened));
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm classified = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `region:cm_region`), cm_region_prefix_member),
            prefix),
            assume_rule(`MEM (region:cm_region)
              (active:(cm_region)list)`)),
            assume_rule(`cm_region_live (region:cm_region)`));
        gnode_list region_cases =
            DISJ_CASES_TAC(scope_cases[0], classified, "Hregion_scope");
        {
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`,
              `region:cm_region`),
              assume_rule(goal_lasmps(region_cases[0]->g)[0].tm));
          thm result = match_mp_rule(
              match_mp_rule(match_mp_rule(ih, recursive),
                assume_rule(
                  `MEM (region:cm_region)
                    (cm_phase_oldregions ${phase:cm_aphase})`)),
              assume_rule(`cm_region_live (region:cm_region)`));
          ACCEPT_TAC(region_cases[0], result);
        }
        {
          thm frame_safe = assume_rule(
              `cm_region_frame_safe (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (region:cm_region)`);
          thm live = assume_rule(
              `cm_region_live (region:cm_region)`);
          thm safe_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_region_frame_safe_def, live)), frame_safe);
          thm fp_parts = match_mp_rule(specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `a1:(cm_acursor)list`, `fid:int`, `fp:int`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              cm_runtime_stack_fp_bounds), recursive);
          thm ceiling_choice = match_mp_rule(specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `a1:(cm_acursor)list`, `fid:int`, `fp:int`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              cm_runtime_stack_frame_ceiling), recursive);
          thm ceiling = mp_rule(mp_rule(int_arith_rule(
              `0i <= (fid:int) ==>
               (fid == --1i ||
                (fp:int) + cm_temp_offset (p:cm_program) fid 0i <=
                  1048576i) ==>
               fp + cm_temp_offset p fid 0i <= 1048576i`),
              fid_nonnegative), ceiling_choice);
          term base =
              `cm_region_base (all_regions:(cm_region)list)
                 (cm_region_gen (region:cm_region))`;
          thm lower = cm_invariant_consequence(safe_parts,
              `(fp:int) + 8i <=
                ${base:int} + cm_region_lo (region:cm_region)`);
          thm upper_data = cm_invariant_consequence(safe_parts,
              `${base:int} + cm_region_hi (region:cm_region) <=
                (fp:int) + cm_temp_offset
                  (p:cm_program) (fid:int) 0i`);
          thm address_lower = mp_rule(mp_rule(mp_rule(int_arith_rule(
              `16i <= cm_static_size (p:cm_program) ==>
               cm_static_size p <= (fp:int) ==>
               fp + 8i <= ${base:int} +
                 cm_region_lo (region:cm_region) ==>
               16i <= ${base:int} + cm_region_lo region`),
              cm_invariant_consequence(fp_parts,
                `16i <= cm_static_size (p:cm_program)`)),
              cm_invariant_consequence(fp_parts,
                `cm_static_size (p:cm_program) <= (fp:int)`)),
              lower);
          thm address_upper = mp_rule(mp_rule(int_arith_rule(
              `${base:int} + cm_region_hi (region:cm_region) <=
                   (fp:int) + cm_temp_offset
                     (p:cm_program) (fid:int) 0i ==>
               fp + cm_temp_offset p fid 0i <= 1048576i ==>
               ${base:int} + cm_region_hi region <= 1048576i`),
              upper_data), ceiling);
          thm result = conj_rule(
              cm_invariant_consequence(safe_parts,
                `0i <= cm_region_lo (region:cm_region)`),
              conj_rule(cm_invariant_consequence(safe_parts,
                `cm_region_lo (region:cm_region) <=
                  cm_region_hi region`),
              conj_rule(address_lower,
              conj_rule(address_upper,
                disj2_rule(
                  `${base:int} + cm_region_hi (region:cm_region) <=
                     cm_static_size (p:cm_program)`,
                  lower)))));
          ACCEPT_TAC(region_cases[1], result);
        }
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm active_static = cm_invariant_consequence(opened,
              `cm_region_dead_prefix (active:(cm_region)list)
                 (cm_static_regions (p:cm_program))`);
          thm static_layout = cm_invariant_consequence(opened,
              `cm_static_regions_layout (p:cm_program)
                 (all_regions:(cm_region)list)`);
          thm static_upper = cm_invariant_consequence(opened,
              `cm_static_size (p:cm_program) <= 1048576i`);
          thm member = match_mp_rule(match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `active:(cm_region)list`,
                `cm_static_regions (p:cm_program)`,
                `region:cm_region`),
                cm_region_dead_prefix_live_member),
              active_static),
              assume_rule(`MEM (region:cm_region)
                (active:(cm_region)list)`)),
              assume_rule(`cm_region_live (region:cm_region)`));
          thm static_parts = match_mp_rule(
              spec_rule(`region:cm_region`,
                conv_rule(rewrite_conv(THM_LIST(
                  cm_static_regions_layout_def)), static_layout)),
              conj_rule(member,
                assume_rule(`cm_region_live (region:cm_region)`)));
          term base =
              `cm_region_base (all_regions:(cm_region)list)
                 (cm_region_gen (region:cm_region))`;
          thm address_lower = cm_invariant_consequence(static_parts,
              `16i <= ${base:int} +
                 cm_region_lo (region:cm_region)`);
          thm address_upper = mp_rule(mp_rule(int_arith_rule(
              `(${base:int}) + cm_region_hi (region:cm_region) <=
                   cm_static_size (p:cm_program) ==>
               cm_static_size p <= 1048576i ==>
               ${base:int} + cm_region_hi region <= 1048576i`),
              cm_invariant_consequence(static_parts,
                `${base:int} + cm_region_hi (region:cm_region) <=
                   cm_static_size (p:cm_program)`)), static_upper);
          thm result = conj_rule(
              cm_invariant_consequence(static_parts,
                `0i <= cm_region_lo (region:cm_region)`),
              conj_rule(cm_invariant_consequence(static_parts,
                `cm_region_lo (region:cm_region) <= cm_region_hi region`),
              conj_rule(address_lower,
              conj_rule(address_upper,
                disj1_rule(
                  cm_invariant_consequence(static_parts,
                    `${base:int} + cm_region_hi (region:cm_region) <=
                       cm_static_size (p:cm_program)`),
                  `(fp:int) + 8i <=
                    ${base:int} + cm_region_lo (region:cm_region)`)))));
          ACCEPT_TAC(halt_cases[0], result);
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`,
              `region:cm_region`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          thm result = match_mp_rule(
              match_mp_rule(match_mp_rule(ih, recursive),
                assume_rule(`MEM (region:cm_region)
                  (active:(cm_region)list)`)),
              assume_rule(`cm_region_live (region:cm_region)`));
          ACCEPT_TAC(halt_cases[1], result);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_region_bounds =
    cm_prove_runtime_stack_region_bounds();

PROOF static thm cm_prove_spill_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_spill_frame).
         CMSpillFrame (cm_spill_frame_fid frame)
           (cm_spill_frame_fp frame)
           (cm_spill_frame_spills frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_spill_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def)));
  return gnode_prove(root);
}
PROOF thm cm_spill_frame_reconstruct =
    cm_prove_spill_frame_reconstruct();


PROOF static thm cm_prove_spills_before_range_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid fp oldfp base width
         (spills:(cm_spill)list).
         cm_spills_within_frame p fid fp oldfp spills ==>
         oldfp <= base ==>
         cm_spill_list_range_safe p fid fp base width spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_fid = GEN_TAC(with_program, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_oldfp = GEN_TAC(with_fp, "oldfp");
  gnode with_base = GEN_TAC(with_oldfp, "base");
  gnode with_width = GEN_TAC(with_base, "width");
  gnode_list cases =
      INDUCT_TAC(with_width, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_list_range_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_spills_within_frame_def)), assume_rule(
          `cm_spills_within_frame (p:cm_program)
            (fid:int) (fp:int) (oldfp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm head = mp_rule(mp_rule(int_arith_rule(
        `(fp:int) +
             (cm_temp_offset (p:cm_program) (fid:int)
                (cm_spill_slot (a0:cm_spill)) + 8i) <=
             (oldfp:int) ==>
         oldfp <= (base:int) ==>
         base + (width:int) <=
             fp + cm_temp_offset p fid (cm_spill_slot a0) ||
         (fp + cm_temp_offset p fid (cm_spill_slot a0)) + 8i <=
             base`),
        cm_invariant_consequence(opened,
          `(fp:int) +
             (cm_temp_offset (p:cm_program) (fid:int)
                (cm_spill_slot (a0:cm_spill)) + 8i) <=
             (oldfp:int)`)),
        assume_rule(`(oldfp:int) <= (base:int)`));
    thm tail = match_mp_rule(
        match_mp_rule(assume_rule(
          `cm_spills_within_frame (p:cm_program)
             (fid:int) (fp:int) (oldfp:int)
             (a1:(cm_spill)list) ==>
           oldfp <= (base:int) ==>
           cm_spill_list_range_safe p fid fp base
             (width:int) a1`),
          conjunct2_rule(conjunct2_rule(opened))),
        assume_rule(`(oldfp:int) <= (base:int)`));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_list_range_safe_def)));
    gnode_list parts = CONJ_TAC(reduced);
    gnode disjoint = CONV_TAC(parts[0], rewrite_conv(
        THM_LIST(cm_range_disjoint_def)));
    ACCEPT_TAC(disjoint, head);
    ACCEPT_TAC(parts[1], tail);
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_before_range_safe =
    cm_prove_spills_before_range_safe();

PROOF static thm cm_prove_spills_within_temp_lower(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid fp oldfp (spills:(cm_spill)list).
         cm_spills_within_frame p fid fp oldfp spills ==>
         cm_spill_list_lower p (fp + cm_temp_offset p fid 0i)
           fid fp spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_fid = GEN_TAC(with_program, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_oldfp = GEN_TAC(with_fp, "oldfp");
  gnode_list cases =
      INDUCT_TAC(with_oldfp, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(
        THM_LIST(cm_spills_within_frame_def)), assume_rule(
          `cm_spills_within_frame (p:cm_program)
            (fid:int) (fp:int) (oldfp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm tail = match_mp_rule(assume_rule(
        `cm_spills_within_frame (p:cm_program)
           (fid:int) (fp:int) (oldfp:int)
           (a1:(cm_spill)list) ==>
         cm_spill_list_lower p (fp + cm_temp_offset p fid 0i)
           fid fp a1`),
        conjunct2_rule(conjunct2_rule(opened)));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(cm_spill_list_lower_def)));
    ACCEPT_TAC(reduced, conj_rule(
        conjunct1_rule(opened), tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_within_temp_lower =
    cm_prove_spills_within_temp_lower();

PROOF static thm cm_prove_runtime_stack_current_machine_lower(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) fid fp
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         0i <= fid ==>
         ~(calls == []) &&
         cm_call_sim_base (HD calls) == fp &&
         cm_call_frames_lower
           (fp + cm_temp_offset p fid 0i) (TL calls) &&
         cm_spill_list_lower p
           (fp + cm_temp_offset p fid 0i) fid fp spills &&
         cm_spill_frames_lower p
           (fp + cm_temp_offset p fid 0i) saved`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    term temp =
        `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i`;
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm stack = assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            ((a0:cm_acursor) :: (a1:(cm_acursor)list))
            (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm segment = cm_invariant_consequence(opened,
          `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
            (cm_phase_oldfp ${phase:cm_aphase})`);
      thm segment_parts = conv_rule(rewrite_conv(
          THM_LIST(cm_frame_segment_def)), segment);
      thm temp_oldfp = cm_invariant_consequence(segment_parts,
          `${temp:int} <= cm_phase_oldfp ${phase:cm_aphase}`);
      thm within = cm_invariant_consequence(opened,
          `cm_spills_within_frame (p:cm_program) (fid:int) (fp:int)
            (cm_phase_oldfp ${phase:cm_aphase})
            (spills:(cm_spill)list)`);
      thm saved_nonempty = cm_invariant_consequence(opened,
          `~((saved:(cm_spill_frame)list) == [])`);
      thm calls_nonempty = cm_invariant_consequence(opened,
          `~((calls:(cm_call_sim_frame)list) == [])`);
      thm head_base = cm_invariant_consequence(opened,
          `cm_call_sim_base
             (HD (calls:(cm_call_sim_frame)list)) == (fp:int)`);
      thm recursive = cm_invariant_consequence(opened,
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list)
            (cm_phase_caller ${phase:cm_aphase})
            (cm_phase_oldfp ${phase:cm_aphase})
            (cm_phase_oldregions ${phase:cm_aphase})
            (a1:(cm_acursor)list)
            (cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list)))
            (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
      thm outer = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `all_regions:(cm_region)list`,
          `a1:(cm_acursor)list`,
          `cm_phase_caller ${phase:cm_aphase}`,
          `cm_phase_oldfp ${phase:cm_aphase}`,
          `cm_phase_oldregions ${phase:cm_aphase}`,
          `cm_spill_frame_spills
            (HD (saved:(cm_spill_frame)list))`,
          `TL (saved:(cm_spill_frame)list)`,
          `TL (calls:(cm_call_sim_frame)list)`),
          cm_runtime_stack_lower), recursive);
      thm calls_tail = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `${temp:int}`, `cm_phase_oldfp ${phase:cm_aphase}`,
            `TL (calls:(cm_call_sim_frame)list)`),
            cm_call_frames_lower_mono),
          temp_oldfp), conjunct1_rule(outer));
      thm current_spills = match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `fp:int`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `spills:(cm_spill)list`),
            cm_spills_within_temp_lower), within);
      thm saved_head_outer = cm_invariant_consequence(outer,
          `cm_spill_list_lower (p:cm_program)
             (cm_phase_oldfp ${phase:cm_aphase})
             (cm_phase_caller ${phase:cm_aphase})
             (cm_phase_oldfp ${phase:cm_aphase})
             (cm_spill_frame_spills
               (HD (saved:(cm_spill_frame)list)))`);
      thm saved_head_lower = match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `${temp:int}`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `cm_phase_caller ${phase:cm_aphase}`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list))`),
            cm_spill_list_lower_mono), temp_oldfp),
          saved_head_outer);
      thm saved_fid = cm_invariant_consequence(opened,
          `cm_spill_frame_fid
             (HD (saved:(cm_spill_frame)list)) ==
           cm_phase_caller ${phase:cm_aphase}`);
      thm saved_fp = cm_invariant_consequence(opened,
          `cm_spill_frame_fp
             (HD (saved:(cm_spill_frame)list)) ==
           cm_phase_oldfp ${phase:cm_aphase}`);
      saved_head_lower = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(saved_fid), sym_rule(saved_fp))),
          saved_head_lower);
      thm saved_tail_lower = match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `${temp:int}`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `TL (saved:(cm_spill_frame)list)`),
            cm_spill_frames_lower_mono), temp_oldfp),
          cm_invariant_consequence(outer,
            `cm_spill_frames_lower (p:cm_program)
              (cm_phase_oldfp ${phase:cm_aphase})
              (TL (saved:(cm_spill_frame)list))`));
      thm saved_unfolded = apply_conversion(rewrite_conv(
          THM_LIST(cm_spill_frames_lower_def)),
          `cm_spill_frames_lower (p:cm_program) ${temp:int}
             (HD (saved:(cm_spill_frame)list) :: TL saved)`);
      thm saved_cons = eq_mp_rule(sym_rule(saved_unfolded),
          conj_rule(saved_head_lower, saved_tail_lower));
      thm saved_shape = mp_rule(
          ispec_rule(`saved:(cm_spill_frame)list`,
            get_theorem_by_name("CONS_HD_TL")), saved_nonempty);
      thm saved_lower = eq_mp_rule(sym_rule(ap_term_rule(
          `cm_spill_frames_lower (p:cm_program) ${temp:int}`,
          saved_shape)), saved_cons);
      thm result = conj_rule(calls_nonempty,
          conj_rule(head_base,
          conj_rule(calls_tail,
          conj_rule(current_spills, saved_lower))));
      ACCEPT_TAC(call_cases[0], result);
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm stack = assume_rule(
            `cm_runtime_stack (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              ((a0:cm_acursor) :: (a1:(cm_acursor)list))
              (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        ACCEPT_TAC(scope_cases[0], match_mp_rule(match_mp_rule(
            ih, recursive),
            assume_rule(`0i <= (fid:int)`)));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm impossible = mp_rule(mp_rule(int_arith_rule(
              `(fid:int) == --1i ==> 0i <= fid ==> F`),
              cm_invariant_consequence(opened,
                `(fid:int) == --1i`)),
              assume_rule(`0i <= (fid:int)`));
          CONTR_TAC(halt_cases[0], impossible);
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm stack = assume_rule(
              `cm_runtime_stack (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (active:(cm_region)list)
                ((a0:cm_acursor) :: (a1:(cm_acursor)list))
                (spills:(cm_spill)list)
                (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list)`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          ACCEPT_TAC(halt_cases[1], match_mp_rule(match_mp_rule(
              ih, recursive),
              assume_rule(`0i <= (fid:int)`)));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_current_machine_lower =
    cm_prove_runtime_stack_current_machine_lower();

PROOF static thm cm_invariant_make_range_disjoint(
    const term target_fact, const thm disjunction) {
  thm unfolded = apply_conversion(rewrite_conv(
      THM_LIST(cm_range_disjoint_def)), target_fact);
  return eq_mp_rule(sym_rule(unfolded), disjunction);
}

PROOF static thm cm_invariant_make_machine_safe(
    const term target_fact, const thm reserved_safe,
    const thm calls_safe, const thm spills_safe) {
  thm unfolded = apply_conversion(rewrite_conv(
      THM_LIST(cm_machine_range_safe_def)), target_fact);
  return eq_mp_rule(sym_rule(unfolded), conj_rule(
      reserved_safe, conj_rule(calls_safe, spills_safe)));
}

PROOF static thm cm_invariant_make_region_safe(
    const term target_fact, const thm live,
    const thm lo_nonnegative, const thm lo_ordered,
    const thm address_nonnegative, const thm address_upper,
    const thm machine_safe) {
  thm unfolded = apply_conversion(reduce_rewrite_conv(
      THM_LIST(cm_region_runtime_safe_def, live)), target_fact);
  thm parts = conj_rule(lo_nonnegative,
      conj_rule(lo_ordered,
      conj_rule(address_nonnegative,
      conj_rule(address_upper, machine_safe))));
  return eq_mp_rule(sym_rule(unfolded), parts);
}

PROOF static thm cm_prove_runtime_stack_region_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) fid fp
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (region:cm_region).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         MEM region active ==>
         cm_region_live region ==>
         cm_region_runtime_safe p calls
           (CMSpillFrame fid fp spills :: saved)
           all_regions region`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    term base =
        `cm_region_base (all_regions:(cm_region)list)
           (cm_region_gen (region:cm_region))`;
    term start =
        `${base:int} + cm_region_lo (region:cm_region)`;
    term finish =
        `${base:int} + cm_region_hi (region:cm_region)`;
    term width =
        `cm_region_hi (region:cm_region) -
           cm_region_lo (region:cm_region)`;
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm member = assume_rule(
        `MEM (region:cm_region) (active:(cm_region)list)`);
    thm live = assume_rule(
        `cm_region_live (region:cm_region)`);
    thm bounds = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `all_regions:(cm_region)list`,
          `(a0:cm_acursor) :: (a1:(cm_acursor)list)`,
          `fid:int`, `fp:int`, `active:(cm_region)list`,
          `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`, `region:cm_region`),
          cm_runtime_stack_region_bounds), stack), member), live);
    thm lo_nonnegative = cm_invariant_consequence(bounds,
        `0i <= cm_region_lo (region:cm_region)`);
    thm lo_ordered = cm_invariant_consequence(bounds,
        `cm_region_lo (region:cm_region) <=
          cm_region_hi region`);
    thm start_lower = cm_invariant_consequence(bounds,
        `16i <= ${start:int}`);
    thm start_nonnegative = mp_rule(int_arith_rule(
        `16i <= ${start:int} ==> 0i <= ${start:int}`),
        start_lower);
    thm finish_upper = cm_invariant_consequence(bounds,
        `${finish:int} <= 1048576i`);
    thm extent = int_ring_rule(
        `${start:int} + ${width:int} == ${finish:int}`);
    thm reserved_disjunction = mp_rule(int_arith_rule(
        `16i <= ${start:int} ==>
         ${start:int} + ${width:int} <= 8i ||
         8i + 8i <= ${start:int}`), start_lower);
    thm reserved_safe = cm_invariant_make_range_disjoint(
        `cm_range_disjoint ${start:int} ${width:int} 8i 8i`,
        reserved_disjunction);

    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      term oldfp = `cm_phase_oldfp ${phase:cm_aphase}`;
      term oldregions =
          `cm_phase_oldregions ${phase:cm_aphase}`;
      term caller = `cm_phase_caller ${phase:cm_aphase}`;
      term temp =
          `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i`;
      thm prefix = cm_invariant_consequence(opened,
          `cm_region_prefix_safe (p:cm_program)
             (all_regions:(cm_region)list) (fid:int) (fp:int)
             (active:(cm_region)list) ${oldregions:(cm_region)list}`);
      thm segment = cm_invariant_consequence(opened,
          `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
             ${oldfp:int}`);
      thm frame_parts = conv_rule(rewrite_conv(
          THM_LIST(cm_frame_segment_def)), segment);
      thm within = cm_invariant_consequence(opened,
          `cm_spills_within_frame (p:cm_program) (fid:int)
             (fp:int) ${oldfp:int} (spills:(cm_spill)list)`);
      thm saved_nonempty = cm_invariant_consequence(opened,
          `~((saved:(cm_spill_frame)list) == [])`);
      thm calls_nonempty = cm_invariant_consequence(opened,
          `~((calls:(cm_call_sim_frame)list) == [])`);
      thm call_base = cm_invariant_consequence(opened,
          `cm_call_sim_base
             (HD (calls:(cm_call_sim_frame)list)) == (fp:int)`);
      thm saved_fid = cm_invariant_consequence(opened,
          `cm_spill_frame_fid
             (HD (saved:(cm_spill_frame)list)) == ${caller:int}`);
      thm saved_fp = cm_invariant_consequence(opened,
          `cm_spill_frame_fp
             (HD (saved:(cm_spill_frame)list)) == ${oldfp:int}`);
      thm recursive = cm_invariant_consequence(opened,
          `cm_runtime_stack (p:cm_program)
             (all_regions:(cm_region)list) ${caller:int}
             ${oldfp:int} ${oldregions:(cm_region)list}
             (a1:(cm_acursor)list)
             (cm_spill_frame_spills
               (HD (saved:(cm_spill_frame)list)))
             (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
      thm classified = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `all_regions:(cm_region)list`,
            `fid:int`, `fp:int`, `active:(cm_region)list`,
            `${oldregions:(cm_region)list}`, `region:cm_region`),
            cm_region_prefix_member), prefix), member), live);
      gnode_list region_cases =
          DISJ_CASES_TAC(call_cases[0], classified, "Hregion");
      {
        thm old_member = assume_rule(
            `MEM (region:cm_region) ${oldregions:(cm_region)list}`);
        thm outer_safe = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `${caller:int}`, `${oldfp:int}`,
              `${oldregions:(cm_region)list}`,
              `cm_spill_frame_spills
                (HD (saved:(cm_spill_frame)list))`,
              `TL (saved:(cm_spill_frame)list)`,
              `TL (calls:(cm_call_sim_frame)list)`,
              `region:cm_region`),
              assume_rule(goal_lasmps(region_cases[0]->g)[0].tm)),
            recursive), old_member), live);
        thm outer_opened = conv_rule(reduce_rewrite_conv(
            THM_LIST(cm_region_runtime_safe_def, live)), outer_safe);
        thm outer_machine = cm_invariant_consequence(outer_opened,
            `cm_machine_range_safe (p:cm_program)
              ${start:int} ${width:int}
              (TL (calls:(cm_call_sim_frame)list))
              (CMSpillFrame ${caller:int} ${oldfp:int}
                 (cm_spill_frame_spills
                   (HD (saved:(cm_spill_frame)list))) ::
               TL (saved:(cm_spill_frame)list))`);
        thm outer_machine_parts = conv_rule(rewrite_conv(
            THM_LIST(cm_machine_range_safe_def)), outer_machine);
        thm tail_calls_safe = cm_invariant_consequence(
            outer_machine_parts,
            `cm_call_frames_range_safe ${start:int} ${width:int}
              (TL (calls:(cm_call_sim_frame)list))`);
        thm outer_spills_safe = cm_invariant_consequence(
            outer_machine_parts,
            `cm_spill_frames_range_safe (p:cm_program)
              ${start:int} ${width:int}
              (CMSpillFrame ${caller:int} ${oldfp:int}
                 (cm_spill_frame_spills
                   (HD (saved:(cm_spill_frame)list))) ::
               TL (saved:(cm_spill_frame)list))`);
        thm reconstructed = spec_rule(
            `HD (saved:(cm_spill_frame)list)`,
            cm_spill_frame_reconstruct);
        reconstructed = conv_rule(rewrite_conv(THM_LIST(
            saved_fid, saved_fp)), reconstructed);
        thm saved_shape = mp_rule(
            ispec_rule(`saved:(cm_spill_frame)list`,
              get_theorem_by_name("CONS_HD_TL")), saved_nonempty);
        thm saved_list_equal = trans_rule(
            mk_comb_rule(mk_comb_rule(refl_rule(
              `CONS:cm_spill_frame->(cm_spill_frame)list->
                (cm_spill_frame)list`), reconstructed),
              refl_rule(`TL (saved:(cm_spill_frame)list)`)),
            sym_rule(saved_shape));
        thm saved_spills_safe = eq_mp_rule(ap_term_rule(
            `cm_spill_frames_range_safe (p:cm_program)
              ${start:int} ${width:int}`, saved_list_equal),
            outer_spills_safe);
        thm outer_bounds = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `a1:(cm_acursor)list`, `${caller:int}`,
              `${oldfp:int}`, `${oldregions:(cm_region)list}`,
              `cm_spill_frame_spills
                (HD (saved:(cm_spill_frame)list))`,
              `TL (saved:(cm_spill_frame)list)`,
              `TL (calls:(cm_call_sim_frame)list)`,
              `region:cm_region`),
              cm_runtime_stack_region_bounds),
            recursive), old_member), live);
        thm outer_choice = cm_invariant_consequence(outer_bounds,
            `${finish:int} <= cm_static_size (p:cm_program) ||
             ${oldfp:int} + 8i <= ${start:int}`);
        thm static_choice = assume_rule(
            `${finish:int} <= cm_static_size (p:cm_program)`);
        thm dynamic_choice = assume_rule(
            `${oldfp:int} + 8i <= ${start:int}`);
        thm temp_lower = cm_invariant_consequence(frame_parts,
            `(fp:int) + 8i <= ${temp:int}`);
        thm temp_upper = cm_invariant_consequence(frame_parts,
            `${temp:int} <= ${oldfp:int}`);
        thm static_fp = cm_invariant_consequence(frame_parts,
            `cm_static_size (p:cm_program) <= (fp:int)`);

        thm head_static_disjunction = mp_rule(mp_rule(mp_rule(
            int_arith_rule(
              `${start:int} + ${width:int} == ${finish:int} ==>
               ${finish:int} <= cm_static_size (p:cm_program) ==>
               cm_static_size p <= (fp:int) ==>
               cm_call_sim_base
                 (HD (calls:(cm_call_sim_frame)list)) == fp ==>
               ${start:int} + ${width:int} <=
                   cm_call_sim_base (HD calls) ||
               cm_call_sim_base (HD calls) + 8i <= ${start:int}`),
            extent), static_choice), static_fp);
        head_static_disjunction =
            mp_rule(head_static_disjunction, call_base);
        thm head_dynamic_disjunction = mp_rule(mp_rule(mp_rule(
            int_arith_rule(
              `(fp:int) + 8i <= ${temp:int} ==>
               ${temp:int} <= ${oldfp:int} ==>
               ${oldfp:int} + 8i <= ${start:int} ==>
               cm_call_sim_base
                 (HD (calls:(cm_call_sim_frame)list)) == fp ==>
               ${start:int} + ${width:int} <=
                   cm_call_sim_base (HD calls) ||
               cm_call_sim_base (HD calls) + 8i <= ${start:int}`),
            temp_lower), temp_upper), dynamic_choice);
        head_dynamic_disjunction =
            mp_rule(head_dynamic_disjunction, call_base);
        thm head_disjunction = disj_cases_rule(outer_choice,
            head_static_disjunction, head_dynamic_disjunction);
        thm head_call_safe = cm_invariant_make_range_disjoint(
            `cm_range_disjoint ${start:int} ${width:int}
              (cm_call_sim_base
                (HD (calls:(cm_call_sim_frame)list))) 8i`,
            head_disjunction);

        thm spills_temp_lower = match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `fp:int`, `${oldfp:int}`,
              `spills:(cm_spill)list`),
              cm_spills_within_temp_lower), within);
        thm static_width_temp = mp_rule(mp_rule(mp_rule(mp_rule(
            int_arith_rule(
              `${start:int} + ${width:int} == ${finish:int} ==>
               ${finish:int} <= cm_static_size (p:cm_program) ==>
               cm_static_size p <= (fp:int) ==>
               fp + 8i <= ${temp:int} ==>
               ${start:int} + ${width:int} <= ${temp:int}`),
            extent), static_choice), static_fp), temp_lower);
        thm current_spills_static = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `${start:int}`, `${width:int}`,
              `${temp:int}`, `fid:int`, `fp:int`,
              `spills:(cm_spill)list`),
              cm_spill_list_lower_range_safe),
            static_width_temp), spills_temp_lower);
        thm dynamic_oldfp_start = mp_rule(int_arith_rule(
            `${oldfp:int} + 8i <= ${start:int} ==>
             ${oldfp:int} <= ${start:int}`), dynamic_choice);
        thm current_spills_dynamic = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `fp:int`, `${oldfp:int}`,
              `${start:int}`, `${width:int}`,
              `spills:(cm_spill)list`),
              cm_spills_before_range_safe), within),
            dynamic_oldfp_start);
        thm current_spills_safe = disj_cases_rule(outer_choice,
            current_spills_static, current_spills_dynamic);

        thm calls_unfolded = apply_conversion(rewrite_conv(
            THM_LIST(cm_call_frames_range_safe_def)),
            `cm_call_frames_range_safe ${start:int} ${width:int}
              (HD (calls:(cm_call_sim_frame)list) :: TL calls)`);
        thm calls_cons = eq_mp_rule(sym_rule(calls_unfolded),
            conj_rule(head_call_safe, tail_calls_safe));
        thm calls_shape = mp_rule(
            ispec_rule(`calls:(cm_call_sim_frame)list`,
              get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
        thm calls_safe = eq_mp_rule(sym_rule(ap_term_rule(
            `cm_call_frames_range_safe ${start:int} ${width:int}`,
            calls_shape)), calls_cons);
        thm spills_unfolded = apply_conversion(rewrite_conv(THM_LIST(
            cm_spill_frames_range_safe_def,
            cm_spill_frame_fid_def, cm_spill_frame_fp_def,
            cm_spill_frame_spills_def)),
            `cm_spill_frames_range_safe (p:cm_program)
              ${start:int} ${width:int}
              (CMSpillFrame (fid:int) (fp:int)
                 (spills:(cm_spill)list) ::
               (saved:(cm_spill_frame)list))`);
        thm spills_safe = eq_mp_rule(sym_rule(spills_unfolded),
            conj_rule(current_spills_safe, saved_spills_safe));
        term machine_fact =
            `cm_machine_range_safe (p:cm_program)
              ${start:int} ${width:int}
              (calls:(cm_call_sim_frame)list)
              (CMSpillFrame (fid:int) (fp:int)
                 (spills:(cm_spill)list) ::
               (saved:(cm_spill_frame)list))`;
        thm machine_safe = cm_invariant_make_machine_safe(
            machine_fact, reserved_safe, calls_safe, spills_safe);
        term region_fact =
            `cm_region_runtime_safe (p:cm_program)
              (calls:(cm_call_sim_frame)list)
              (CMSpillFrame (fid:int) (fp:int)
                 (spills:(cm_spill)list) ::
               (saved:(cm_spill_frame)list))
              (all_regions:(cm_region)list) (region:cm_region)`;
        thm result = cm_invariant_make_region_safe(region_fact,
            live, lo_nonnegative, lo_ordered, start_nonnegative,
            finish_upper, machine_safe);
        ACCEPT_TAC(region_cases[0], result);
      }
      {
        thm frame_safe = assume_rule(
            `cm_region_frame_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (region:cm_region)`);
        thm safe_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_region_frame_safe_def, live)), frame_safe);
        thm start_fp = cm_invariant_consequence(safe_parts,
            `(fp:int) + 8i <= ${start:int}`);
        thm finish_temp = cm_invariant_consequence(safe_parts,
            `${finish:int} <= ${temp:int}`);
        thm temp_oldfp = cm_invariant_consequence(frame_parts,
            `${temp:int} <= ${oldfp:int}`);
        thm width_temp = mp_rule(mp_rule(int_arith_rule(
            `${start:int} + ${width:int} == ${finish:int} ==>
             ${finish:int} <= ${temp:int} ==>
             ${start:int} + ${width:int} <= ${temp:int}`),
            extent), finish_temp);
        thm width_oldfp = mp_rule(mp_rule(int_arith_rule(
            `${start:int} + ${width:int} <= ${temp:int} ==>
             ${temp:int} <= ${oldfp:int} ==>
             ${start:int} + ${width:int} <= ${oldfp:int}`),
            width_temp), temp_oldfp);
        thm outer_lower = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `all_regions:(cm_region)list`,
            `a1:(cm_acursor)list`, `${caller:int}`, `${oldfp:int}`,
            `${oldregions:(cm_region)list}`,
            `cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list))`,
            `TL (saved:(cm_spill_frame)list)`,
            `TL (calls:(cm_call_sim_frame)list)`),
            cm_runtime_stack_lower), recursive);
        thm tail_calls_safe = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `${start:int}`, `${width:int}`, `${oldfp:int}`,
              `TL (calls:(cm_call_sim_frame)list)`),
              cm_call_lower_range_safe), width_oldfp),
            cm_invariant_consequence(outer_lower,
              `cm_call_frames_lower ${oldfp:int}
                 (TL (calls:(cm_call_sim_frame)list))`));
        thm spills_temp_lower = match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `fp:int`, `${oldfp:int}`,
              `spills:(cm_spill)list`),
              cm_spills_within_temp_lower), within);
        thm current_spills_safe = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `${start:int}`, `${width:int}`,
              `${temp:int}`, `fid:int`, `fp:int`,
              `spills:(cm_spill)list`),
              cm_spill_list_lower_range_safe), width_temp),
            spills_temp_lower);

        thm saved_head_lower = cm_invariant_consequence(outer_lower,
            `cm_spill_list_lower (p:cm_program) ${oldfp:int}
              ${caller:int} ${oldfp:int}
              (cm_spill_frame_spills
                (HD (saved:(cm_spill_frame)list)))`);
        thm saved_head_equal = mk_comb_rule(mk_comb_rule(
            mk_comb_rule(refl_rule(
              `cm_spill_list_lower (p:cm_program) ${oldfp:int}`),
              sym_rule(saved_fid)), sym_rule(saved_fp)),
            refl_rule(
              `cm_spill_frame_spills
                (HD (saved:(cm_spill_frame)list))`));
        saved_head_lower =
            eq_mp_rule(saved_head_equal, saved_head_lower);
        thm saved_tail_lower = cm_invariant_consequence(outer_lower,
            `cm_spill_frames_lower (p:cm_program) ${oldfp:int}
              (TL (saved:(cm_spill_frame)list))`);
        thm saved_unfolded = apply_conversion(rewrite_conv(
            THM_LIST(cm_spill_frames_lower_def)),
            `cm_spill_frames_lower (p:cm_program) ${oldfp:int}
              (HD (saved:(cm_spill_frame)list) :: TL saved)`);
        thm saved_cons_lower = eq_mp_rule(sym_rule(saved_unfolded),
            conj_rule(saved_head_lower, saved_tail_lower));
        thm saved_shape = mp_rule(
            ispec_rule(`saved:(cm_spill_frame)list`,
              get_theorem_by_name("CONS_HD_TL")), saved_nonempty);
        thm saved_lower = eq_mp_rule(sym_rule(ap_term_rule(
            `cm_spill_frames_lower (p:cm_program) ${oldfp:int}`,
            saved_shape)), saved_cons_lower);
        thm saved_spills_safe = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `${start:int}`, `${width:int}`,
              `${oldfp:int}`, `saved:(cm_spill_frame)list`),
              cm_spill_frames_lower_range_safe), width_oldfp),
            saved_lower);

        thm head_disjunction = mp_rule(mp_rule(
            int_arith_rule(
              `cm_call_sim_base
                 (HD (calls:(cm_call_sim_frame)list)) == (fp:int) ==>
               fp + 8i <= ${start:int} ==>
               ${start:int} + ${width:int} <=
                   cm_call_sim_base (HD calls) ||
               cm_call_sim_base (HD calls) + 8i <= ${start:int}`),
            call_base), start_fp);
        thm head_call_safe = cm_invariant_make_range_disjoint(
            `cm_range_disjoint ${start:int} ${width:int}
              (cm_call_sim_base
                (HD (calls:(cm_call_sim_frame)list))) 8i`,
            head_disjunction);
        thm calls_unfolded = apply_conversion(rewrite_conv(
            THM_LIST(cm_call_frames_range_safe_def)),
            `cm_call_frames_range_safe ${start:int} ${width:int}
              (HD (calls:(cm_call_sim_frame)list) :: TL calls)`);
        thm calls_cons = eq_mp_rule(sym_rule(calls_unfolded),
            conj_rule(head_call_safe, tail_calls_safe));
        thm calls_shape = mp_rule(
            ispec_rule(`calls:(cm_call_sim_frame)list`,
              get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
        thm calls_safe = eq_mp_rule(sym_rule(ap_term_rule(
            `cm_call_frames_range_safe ${start:int} ${width:int}`,
            calls_shape)), calls_cons);
        thm spills_unfolded = apply_conversion(rewrite_conv(THM_LIST(
            cm_spill_frames_range_safe_def,
            cm_spill_frame_fid_def, cm_spill_frame_fp_def,
            cm_spill_frame_spills_def)),
            `cm_spill_frames_range_safe (p:cm_program)
              ${start:int} ${width:int}
              (CMSpillFrame (fid:int) (fp:int)
                 (spills:(cm_spill)list) ::
               (saved:(cm_spill_frame)list))`);
        thm spills_safe = eq_mp_rule(sym_rule(spills_unfolded),
            conj_rule(current_spills_safe, saved_spills_safe));
        term machine_fact =
            `cm_machine_range_safe (p:cm_program)
              ${start:int} ${width:int}
              (calls:(cm_call_sim_frame)list)
              (CMSpillFrame (fid:int) (fp:int)
                 (spills:(cm_spill)list) ::
               (saved:(cm_spill_frame)list))`;
        thm machine_safe = cm_invariant_make_machine_safe(
            machine_fact, reserved_safe, calls_safe, spills_safe);
        term region_fact =
            `cm_region_runtime_safe (p:cm_program)
              (calls:(cm_call_sim_frame)list)
              (CMSpillFrame (fid:int) (fp:int)
                 (spills:(cm_spill)list) ::
               (saved:(cm_spill_frame)list))
              (all_regions:(cm_region)list) (region:cm_region)`;
        thm result = cm_invariant_make_region_safe(region_fact,
            live, lo_nonnegative, lo_ordered, start_nonnegative,
            finish_upper, machine_safe);
        ACCEPT_TAC(region_cases[1], result);
      }
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        term temp =
            `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i`;
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm fid_nonnegative = conjunct1_rule(opened);
        thm prefix = conjunct1_rule(conjunct2_rule(opened));
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm classified = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `region:cm_region`), cm_region_prefix_member),
            prefix), member), live);
        gnode_list region_cases =
            DISJ_CASES_TAC(scope_cases[0], classified, "Hregion_scope");
        {
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`, `region:cm_region`),
              assume_rule(goal_lasmps(region_cases[0]->g)[0].tm));
          thm result = match_mp_rule(match_mp_rule(match_mp_rule(
              ih, recursive),
              assume_rule(
                `MEM (region:cm_region)
                  (cm_phase_oldregions ${phase:cm_aphase})`)),
              live);
          ACCEPT_TAC(region_cases[0], result);
        }
        {
          thm frame_safe = assume_rule(
              `cm_region_frame_safe (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (region:cm_region)`);
          thm safe_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_region_frame_safe_def, live)), frame_safe);
          thm start_fp = cm_invariant_consequence(safe_parts,
              `(fp:int) + 8i <= ${start:int}`);
          thm finish_temp = cm_invariant_consequence(safe_parts,
              `${finish:int} <= ${temp:int}`);
          thm width_temp = mp_rule(mp_rule(int_arith_rule(
              `${start:int} + ${width:int} == ${finish:int} ==>
               ${finish:int} <= ${temp:int} ==>
               ${start:int} + ${width:int} <= ${temp:int}`),
              extent), finish_temp);
          thm machine_lower = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `all_regions:(cm_region)list`,
                `a1:(cm_acursor)list`, `fid:int`, `fp:int`,
                `cm_phase_oldregions ${phase:cm_aphase}`,
                `spills:(cm_spill)list`,
                `saved:(cm_spill_frame)list`,
                `calls:(cm_call_sim_frame)list`),
                cm_runtime_stack_current_machine_lower),
              recursive), fid_nonnegative);
          thm calls_nonempty = cm_invariant_consequence(machine_lower,
              `~((calls:(cm_call_sim_frame)list) == [])`);
          thm call_base = cm_invariant_consequence(machine_lower,
              `cm_call_sim_base
                 (HD (calls:(cm_call_sim_frame)list)) == (fp:int)`);
          thm tail_calls_safe = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `${start:int}`, `${width:int}`, `${temp:int}`,
                `TL (calls:(cm_call_sim_frame)list)`),
                cm_call_lower_range_safe), width_temp),
              cm_invariant_consequence(machine_lower,
                `cm_call_frames_lower ${temp:int}
                   (TL (calls:(cm_call_sim_frame)list))`));
          thm current_spills_safe = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `${start:int}`, `${width:int}`,
                `${temp:int}`, `fid:int`, `fp:int`,
                `spills:(cm_spill)list`),
                cm_spill_list_lower_range_safe), width_temp),
              cm_invariant_consequence(machine_lower,
                `cm_spill_list_lower (p:cm_program) ${temp:int}
                   (fid:int) (fp:int) (spills:(cm_spill)list)`));
          thm saved_spills_safe = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `${start:int}`, `${width:int}`,
                `${temp:int}`, `saved:(cm_spill_frame)list`),
                cm_spill_frames_lower_range_safe), width_temp),
              cm_invariant_consequence(machine_lower,
                `cm_spill_frames_lower (p:cm_program) ${temp:int}
                   (saved:(cm_spill_frame)list)`));
          thm head_disjunction = mp_rule(mp_rule(
              int_arith_rule(
                `cm_call_sim_base
                   (HD (calls:(cm_call_sim_frame)list)) == (fp:int) ==>
                 fp + 8i <= ${start:int} ==>
                 ${start:int} + ${width:int} <=
                     cm_call_sim_base (HD calls) ||
                 cm_call_sim_base (HD calls) + 8i <= ${start:int}`),
              call_base), start_fp);
          thm head_call_safe = cm_invariant_make_range_disjoint(
              `cm_range_disjoint ${start:int} ${width:int}
                (cm_call_sim_base
                  (HD (calls:(cm_call_sim_frame)list))) 8i`,
              head_disjunction);
          thm calls_unfolded = apply_conversion(rewrite_conv(
              THM_LIST(cm_call_frames_range_safe_def)),
              `cm_call_frames_range_safe ${start:int} ${width:int}
                (HD (calls:(cm_call_sim_frame)list) :: TL calls)`);
          thm calls_cons = eq_mp_rule(sym_rule(calls_unfolded),
              conj_rule(head_call_safe, tail_calls_safe));
          thm calls_shape = mp_rule(
              ispec_rule(`calls:(cm_call_sim_frame)list`,
                get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
          thm calls_safe = eq_mp_rule(sym_rule(ap_term_rule(
              `cm_call_frames_range_safe ${start:int} ${width:int}`,
              calls_shape)), calls_cons);
          thm spills_unfolded = apply_conversion(rewrite_conv(THM_LIST(
              cm_spill_frames_range_safe_def,
              cm_spill_frame_fid_def, cm_spill_frame_fp_def,
              cm_spill_frame_spills_def)),
              `cm_spill_frames_range_safe (p:cm_program)
                ${start:int} ${width:int}
                (CMSpillFrame (fid:int) (fp:int)
                   (spills:(cm_spill)list) ::
                 (saved:(cm_spill_frame)list))`);
          thm spills_safe = eq_mp_rule(sym_rule(spills_unfolded),
              conj_rule(current_spills_safe, saved_spills_safe));
          term machine_fact =
              `cm_machine_range_safe (p:cm_program)
                ${start:int} ${width:int}
                (calls:(cm_call_sim_frame)list)
                (CMSpillFrame (fid:int) (fp:int)
                   (spills:(cm_spill)list) ::
                 (saved:(cm_spill_frame)list))`;
          thm machine_safe = cm_invariant_make_machine_safe(
              machine_fact, reserved_safe, calls_safe, spills_safe);
          term region_fact =
              `cm_region_runtime_safe (p:cm_program)
                (calls:(cm_call_sim_frame)list)
                (CMSpillFrame (fid:int) (fp:int)
                   (spills:(cm_spill)list) ::
                 (saved:(cm_spill_frame)list))
                (all_regions:(cm_region)list) (region:cm_region)`;
          thm result = cm_invariant_make_region_safe(region_fact,
              live, lo_nonnegative, lo_ordered, start_nonnegative,
              finish_upper, machine_safe);
          ACCEPT_TAC(region_cases[1], result);
        }
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm machine_unfolded = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                cm_machine_range_safe_def,
                cm_call_frames_range_safe_def,
                cm_spill_frames_range_safe_def,
                cm_spill_list_range_safe_def,
                cm_spill_frame_fid_def, cm_spill_frame_fp_def,
                cm_spill_frame_spills_def,
                cm_invariant_consequence(opened,
                  `(spills:(cm_spill)list) == []`),
                cm_invariant_consequence(opened,
                  `(saved:(cm_spill_frame)list) == []`),
                cm_invariant_consequence(opened,
                  `(calls:(cm_call_sim_frame)list) == []`))),
              `cm_machine_range_safe (p:cm_program)
                ${start:int} ${width:int}
                (calls:(cm_call_sim_frame)list)
                (CMSpillFrame (fid:int) (fp:int)
                   (spills:(cm_spill)list) ::
                 (saved:(cm_spill_frame)list))`);
          thm machine_safe =
              eq_mp_rule(sym_rule(machine_unfolded), reserved_safe);
          term region_fact =
              `cm_region_runtime_safe (p:cm_program)
                (calls:(cm_call_sim_frame)list)
                (CMSpillFrame (fid:int) (fp:int)
                   (spills:(cm_spill)list) ::
                 (saved:(cm_spill_frame)list))
                (all_regions:(cm_region)list) (region:cm_region)`;
          thm result = cm_invariant_make_region_safe(region_fact,
              live, lo_nonnegative, lo_ordered, start_nonnegative,
              finish_upper, machine_safe);
          ACCEPT_TAC(halt_cases[0], result);
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`, `region:cm_region`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          thm result = match_mp_rule(match_mp_rule(match_mp_rule(
              ih, recursive), member), live);
          ACCEPT_TAC(halt_cases[1], result);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_region_safe =
    cm_prove_runtime_stack_region_safe();

PROOF static thm cm_prove_runtime_stack_memory_layout(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) fid
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) cursors
           spills saved calls ==>
         cm_runtime_memory_layout p st calls
           (CMSpillFrame fid (cm_state_fp st) spills :: saved)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (cursors:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  gnode unfolded = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_runtime_memory_layout_def, cm_regions_runtime_safe_def)));
  gnode with_region = GEN_TAC(unfolded, "region");
  gnode member_leaf = DISCH_TAC(with_region, "Hmember");
  gnode_list live_cases = BOOL_CASES_TAC(member_leaf,
      `cm_region_live (region:cm_region)`, "Hlive");
  {
    thm result = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`,
          `cm_state_regions (st:cm_src_state)`,
          `cursors:(cm_acursor)list`, `fid:int`,
          `cm_state_fp (st:cm_src_state)`,
          `cm_state_regions st`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`, `region:cm_region`),
          cm_runtime_stack_region_safe), stack),
        assume_rule(
          `MEM (region:cm_region)
            (cm_state_regions (st:cm_src_state))`)),
        assume_rule(`cm_region_live (region:cm_region)`));
    ACCEPT_TAC(live_cases[0], result);
  }
  {
    CONV_WITH_ASMP_TAC(live_cases[1], reduce_rewrite_conv,
        THM_LIST(cm_region_runtime_safe_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_memory_layout =
    cm_prove_runtime_stack_memory_layout();
PROOF static int cmc_preservation_invariant_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_axioms_before,
      "cmc_preservation_invariant introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_checks =
    cmc_preservation_invariant_final_checks();
