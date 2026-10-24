"""Check original BODY contract mapping after independent source/target review."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c').read_text();lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest();norm=lambda s:re.sub(r'\s+','',s)
pure='''cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)))'''
resources='cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s)'
code='cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)'
params='(policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (loop_ : bool) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)'
rows=[]
source=(R/'baseline/cmc_concrete_emit_stmt.c').read_text();sourcefs=json.loads((R/'metrics/source-functions.json').read_text())
for f in c_functions(c):
 if f['prototype']:continue
 body='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 isif=f['name']=='cmc_emit_if_stmt';facts=('s == CMIfS(guard_, yes_, no_) && 'if isif else '')+pure
 withs=params+(' (guard_ : cm_expr) (yes_ : cm_stmt) (no_ : cm_stmt)'if isif else '')
 expected=f'/*@ With {withs} Require {facts} && {resources} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app({code}, tail)) Ensure {facts} && {resources} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, {code}), tail) */'
 assert norm(body)==norm(expected),'Original BODY contract mapping drift: '+f['name']
 sf=next(x for x in sourcefs if x['name']==f['name']);slines=source.splitlines();ss='\n'.join(slines[i-1] for a,b in sf['specification']for i in range(a,b+1))
 rows.append(dict(function=f['name'],target_contract_sha256=sha(body),source_contract_sha256=sha(ss),status='reviewed',review='All original pure facts, complete program/function/statement resources, original loop context, arbitrary done/tail and exact emission prefix/postfix retained; if constructor condition unchanged. Existing arbitrary policy/cg parameters retained.'))
models=[]
for x in coq_regions(lib):
 if x['kind'] not in ['Definition','Fixpoint','Inductive','Record']:continue
 frag=lib[x['start']:x['end']]
 models.append(dict(name=x['name'],kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip())for l in coq_mask(frag).splitlines())))
assert 'cm_emit_stmt' in [x['name']for x in models]
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps([dict(name=x.get('name'),kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(lib[x['start']:x['end']]),nonblank_lines=sum(bool(l.strip())for l in coq_mask(lib[x['start']:x['end']]).splitlines()))for x in coq_regions(lib)],indent=2)+'\n')
audit=dict(status='contract mapping reviewed; final model/proof review pending',contracts=rows,annotation_stage_model_declarations=models,additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,source_model='baseline/cmc_codegen.c:891',model_review='Initial cm_emit_stmt Fixpoint reviewed constructor by constructor: preserves all 11 HOL cases, ordered code, if jump targets and branch PCs, while break=end and continue=guard PC, init slot lookup/store/normalization and return epilogue. Final declarations must be reviewed separately.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print('Reviewed original contracts for',len(rows),'functions; model declarations',[(x['name'],x['kind'])for x in models])
