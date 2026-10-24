#!/usr/bin/env python3
"""Record reviewed model identities. Read-only with respect to formal targets.
Main must run after reviewing current declarations; not an automatic equivalence proof.
"""
from pathlib import Path
import json,hashlib
from audit_syntax import coq_regions,line_span
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
s=(Q/'Rocq/examples/QCP_demos_human/cmc_counts_migration_lib.v').read_text()
rows=[]
for r in coq_regions(s):
 if r['kind'] not in ['Record','Inductive','Definition','Fixpoint']:continue
 rows.append(dict(name=r['name'],kind=r['kind'],span=line_span(s,r['start'],r['end']),sha256=hashlib.sha256(s[r['start']:r['end']].encode()).hexdigest()))
out={'review_kind':'Manual structural equation/contract review; not a formal HOL-to-Rocq translation theorem','status':'models reviewed; contracts and final verification pending','annotation_stage_model_declarations':rows,'model_checks':['Code counts preserve all AST cases, binary-tail ordering, normalize counts and arithmetic constants.','Representability retains node count/type bounds and recursive subexpression, argument, statement, parameter, function and pc conditions.','Function pc accepts fid equal to function-list length. Prefix model uses full-list length minus remaining-list length, not an arbitrary new index.','One cm_lookup_policy applies uniformly to otherwise total HOL function lookup.','Typing preserves assignment lvalue/array/conversion conditions, argument-list arity and convertibility, break/continue loop flag, while-body flag true.','Function typing retains scope, declaration-count, temporary-slot, frame-size and main-entry requirements.','Data-length remains byte-list length, including negative-size guard, initialization branch and zero padding; not silently replaced by a size formula.','Heap contexts and separated function header/body lists match cmc_concrete_defs.c and cmc_rep.c.'],'parameterized_boundary':{'record':'cm_codegen_obligations','fields':['cm_codegen_code_shape','cm_codegen_targets_valid','cm_codegen_patches_valid','cm_codegen_entry_valid'],'source_instances':['tvm_code_shape (cm_model_code p)','tvm_targets_valid (cm_model_code p)','tvm_patches_valid (cm_model_patches p)','tvm_target_valid (cm_model_code p) 0'],'meaning':'Universal parameters preserve each original conjunct. Their concrete emitter/TVM predicates are not translated in this case; the reflexivity conjunction lemma is not a complete equivalence theorem.'},'out_of_scope_support':['cm_concrete_function_ready','cm_concrete_functions_ready']}
(R/'metrics/model-review.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(len(rows))
