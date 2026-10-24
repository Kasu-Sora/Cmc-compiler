"""Freeze independent original-BODY mapping and reviewed model identities."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_function_migration.c').read_text()
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_function_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
norm=lambda s:re.sub(r'\s+','',s)
common='(policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d)'
output='(done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)'
specs={
 'cmc_emit_param_stores_from':dict(
  withs=common+' (fid : Z) (structs : list cm_struct_d) (full : list cm_slot_d) (prefix : list cm_slot_d) (params : list cm_slot_d) '+output,
  facts='''structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) &&
 offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 &&
 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) &&
 cm_rep_members_safe(params) && cm_param_counts_representable(params)''',
  resources='cm_slot_list_rep(param, params)',code='cm_emit_param_stores(policy, p, fid, slot, params)'),
 'cmc_emit_prologue':dict(
  withs=common+' (s : cm_stmt) (body : Z) (next : Z) (structs : list cm_struct_d) '+output,
  facts='''f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) &&
 s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) &&
 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 &&
 cm_param_counts_representable(cm_function_params(f))''',
  resources='cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s)',code='cm_emit_prologue(policy, p, fid)'),
 'cmc_emit_function':dict(
  withs=common+' (cg : cm_codegen_obligations) (s : cm_stmt) (body : Z) (next : Z) (functions_ptr : Z) '+output,
  facts='''cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 s == cm_function_body(f) && function_pc == cm_function_pc(policy, p, fid) && cm_stmt_wf(policy, p, f, false, s) &&
 cm_stmt_counts_representable(policy, p, fid, s) && cm_param_counts_representable(cm_function_params(f)) &&
 cm_i32_code_count(cm_function_prologue_count(f)) && cm_i32_code_count(function_pc) &&
 cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f)) &&
 cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) + Zlength(cm_emit_stmt(policy, p, fid, cm_function_pc(policy, p, fid) + cm_function_prologue_count(f), 0, 0, 0, s))) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 &&
 cm_temp_offset(policy, p, fid, cm_stemps(s)) <= 2147483647''',
  resources='cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s)',code='cm_emit_function(policy, p, fid)')}
rows=[]
source=(R/'baseline/cmc_concrete_emit_function.c').read_text()
sourcefs=json.loads((R/'metrics/source-functions.json').read_text())
for f in c_functions(c):
 if f['prototype']:continue
 x=specs[f['name']];body='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 expected=f"/*@ With {x['withs']} Require {x['facts']} && {x['resources']} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app({x['code']}, tail)) Ensure {x['facts']} && {x['resources']} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, {x['code']}), tail) */"
 assert norm(body)==norm(expected),'Original BODY contract mapping drift: '+f['name']
 sf=next(x for x in sourcefs if x['name']==f['name']);ls=source.splitlines()
 ss='\n'.join(ls[i-1] for a,b in sf['specification']for i in range(a,b+1))
 rows.append(dict(function=f['name'],target_contract_sha256=sha(body),source_contract_sha256=sha(ss),status='reviewed',review='All original pure facts, parameter-prefix/offset or frame/PC constraints and full resources retained in pre/post; exact output code, arbitrary done/tail and existing policy/cg boundary preserved.'))
assert len(rows)==3
decl=[]
for x in coq_regions(lib):
 frag=lib[x['start']:x['end']]
 decl.append(dict(name=x.get('name'),kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip())for l in coq_mask(frag).splitlines())))
models=[x for x in decl if x['kind'] in ['Definition','Fixpoint','Inductive','Record']]
assert {x['name'] for x in models}=={'cm_emit_param_stores','cm_emit_prologue','cm_emit_function','cm_emit_params_head','cm_emit_params_tail'}
reviews={
 'cm_emit_param_stores':'Exact nil/cons equations; recurse on tail at slot+1 first, then normalize head, original parameter-prefix FP address, and store. No input restriction.',
 'cm_emit_prologue':'Exact 14 instructions and immediates, mathematical frame size at total function lookup, followed by parameter stores at slot 0.',
 'cm_emit_function':'Exact prologue ++ statement body at function-PC+prologue-count with temp/break/continue 0 ++ PUSH 0 ++ return epilogue.',
 'cm_emit_params_head':'Transparent existing cm_slot_at 0 lookup. Used under nonempty shape; empty default does not restrict BODY inputs or alter emission equations.',
 'cm_emit_params_tail':'Transparent list tail, used under matching list shape; no heap or operational assumption.'}
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(decl,indent=2)+'\n')
audit=dict(status='contract mapping reviewed; final model/proof review pending',contracts=rows,annotation_stage_model_declarations=models,annotation_stage_model_review=reviews,additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,source_model='baseline/cmc_codegen.c:981',model_review='Three instruction-list equations independently compared with source; two total observations used only through constructor facts. Final merged declarations and proofs require separate review.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print('All three original BODY contracts and five model declarations reviewed.')
