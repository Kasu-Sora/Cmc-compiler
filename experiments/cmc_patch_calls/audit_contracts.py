"""Independent full-file original BODY contract and model audit."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_patch_calls_migration.c').read_text();lib=(Q/'Rocq/examples/QCP_demos_human/cmc_patch_calls_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest();norm=lambda s:re.sub(r'\s+','',s)
facts='cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p)'
resources='cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))'
specs={
 'cmc_patch_code_arrays':dict(withs='(policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (raw : list tvm_inst) (functions_ptr : Z)',facts=facts+' && 0 <= length && length <= 2147483647 && length == Zlength(raw)',pre=resources+' * cm_patch_arrays_rep(ops, imms, length, raw)',post=resources+' * cm_patch_arrays_rep(ops, imms, length, cm_patch_code(policy, p, raw))'),
 'cmc_patch_resolved_calls':dict(withs='(policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (resolved : list tvm_inst) (functions_ptr : Z) (out : Z) (capacity : Z)',facts=facts,pre=resources+' * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, resolved)',post=resources+' * cm_emitter_rep(emitter, out, capacity, cm_rep_ops(resolved), cm_rep_imms(resolved))')}
source=(R/'baseline/cmc_concrete_patch_calls.c').read_text();ls=source.splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());rows=[]
for f in c_functions(c):
 if f['prototype']:continue
 x=specs[f['name']];body='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));expected=f"/*@ With {x['withs']} Require {x['facts']} && {x['pre']} Ensure {x['facts']} && {x['post']} */"
 assert norm(body)==norm(expected),'Original BODY mapping drift: '+f['name']
 sf=next(x for x in fs if x['name']==f['name']);ss='\n'.join(ls[i-1] for a,b in sf['specification'] for i in range(a,b+1));rows.append(dict(function=f['name'],target_contract_sha256=sha(body),source_contract_sha256=sha(ss),status='reviewed',review='Original wf/code-ready, context and complete function-list retained; exact array patching or resolved-to-physical output. No new valid-id, raw=model-code or nonnull-empty-array premise. Existing policy/cg boundary unchanged.'))
assert len(rows)==2
decl=[]
for x in coq_regions(lib):
 frag=lib[x['start']:x['end']];decl.append(dict(name=x.get('name'),kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip())for l in coq_mask(frag).splitlines())))
models=[x for x in decl if x['kind'] in ['Definition','Fixpoint','Inductive','Record']];assert {x['name']for x in models}=={'cm_patch_tail','cm_patch_arrays_rep'}
mr=next(x for x in coq_regions(lib) if x.get('name')=='cm_patch_tail');expected_model='Definition cm_patch_tail (raw : list tvm_inst) : list tvm_inst := tl raw.'
assert norm(coq_mask(lib[mr['start']:mr['end']]))==norm(expected_model)
mr=next(x for x in coq_regions(lib) if x.get('name')=='cm_patch_arrays_rep')
expected_arrays='Definition cm_patch_arrays_rep (ops imms length : Z) (raw : list tvm_inst) : Assertion := IntArray.full ops length (cm_rep_ops raw) ** Int64Array.full imms length (cm_rep_imms raw).'
assert norm(coq_mask(lib[mr['start']:mr['end']]))==norm(expected_arrays)

(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(decl,indent=2)+'\n')
audit=dict(status='contract mapping reviewed; final model/proof review pending',contracts=rows,annotation_stage_model_declarations=models,annotation_stage_model_review={'cm_patch_tail':'Total tl: nil maps to nil, cons maps to tail, exactly matching source exported observation.','cm_patch_arrays_rep':'Transparent abbreviation exactly equal to original two full-array resources. No new pure condition, nonnull restriction or hidden state. Allows raw inference at recursive and wrapper call sites.'},additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,source_model='baseline/cmc_concrete_patch_calls.c:9',array_mapping='store_int_array and store_int64_array map to IntArray.full and Int64Array.full: complete indexed cell ownership with corresponding 4/8 byte element stores; empty full arrays impose no extra base nonnull condition. Existing emitter uses matching seg/undef_seg resources.',model_review='Reused exact patch_inst/code definitions: opcode unchanged; only code22 immediate mapped through unrestricted total function PC. Resolved wrapper existential raw buffer is not identified with resolved. Final merged proof and any helpers separately reviewed.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');print('Two original BODY contracts and total tail model reviewed.')
