#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_task.h"

#require "cmc_preservation_tagged_call_enter.c"
#require "cmc_preservation_tagged_restore.c"
#require "cmc_preservation_invariant_task.c"
#require "cmc_preservation_generation_step_apply.c"

PROOF static size_t _cmc_preservation_tagged_task_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_task_tagged_valid_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input.
        cm_task_tagged_valid
          (CMStartTask (p:cm_program) (input:(int)list)) = T) &&
     (!p fid expr st ks.
        cm_task_tagged_valid
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_tagged_span_valid st) &&
     (!p fid expr st ks.
        cm_task_tagged_valid
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_tagged_span_valid st) &&
     (!p fid stmt st ks.
        cm_task_tagged_valid
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_tagged_span_valid st) &&
     (!p fid value st ks.
        cm_task_tagged_valid
          (CMVTask (p:cm_program) (fid:int) (value:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_tagged_span_valid st) &&
     (!p fid control st ks.
        cm_task_tagged_valid
          (CMCTask (p:cm_program) (fid:int) (control:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_tagged_span_valid st) &&
     (!st control status.
        cm_task_tagged_valid
          (CMDoneTask (st:cm_src_state) (control:cm_control)
            (status:int)) = cm_tagged_span_valid st)`);

PROOF static thm cm_prove_task_tagged_initial(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_tagged_valid (CMStartTask p input)`);
  CONV_TAC(AUTO_INTROS_TAC(root_node),
      reduce_rewrite_conv(THM_LIST(cm_task_tagged_valid_def)));
  return gnode_prove(root_node);
}
PROOF thm cm_task_tagged_initial = cm_prove_task_tagged_initial();

PROOF static int cmc_preservation_tagged_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_task_axioms_before,
      "cmc_preservation_tagged_task introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_tagged_initial)) == 0,
      "task tagged-valid initial theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_task_checks =
    cmc_preservation_tagged_task_final_checks();
