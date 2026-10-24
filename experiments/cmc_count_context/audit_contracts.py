#!/usr/bin/env python3
"""Freeze manually reviewed wrapper contracts; this is not semantic automation."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_count_context_migration.c').read_text()
src=(R/'baseline/cmc_concrete_count_context.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text())
expected={f['name'] for f in fs if not f['prototype']};assert len(expected)==4
checks={
'cm_expr_type_code_context':'Exact encoded type output, expr ownership restored; no added type validity precondition.',
'cm_expr_lvalue_count_context':'Full program/function/expr ownership and original wf/lookup/representability/struct safety restored; exact lvalue count and i32 bound.',
'cm_expr_rvalue_count_context':'Full program/function/expr ownership and original wf/lookup/representability/struct safety restored; exact rvalue count and i32 bound.',
'cm_stmt_code_count_context':'Full program/function/stmt ownership restored; original loop_ and function lookup equality retained; exact statement count and i32 bound.'}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b]) for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 sources.append({'function':n,'contract':source})
 rows.append({'function':n,'source_contract_sha256':hashlib.sha256(source.encode()).hexdigest(),'target_contract_sha256':hashlib.sha256(target.encode()).hexdigest(),'checks':[checks[n],'Same runtime parameters/results; source contract has no additional fid bound','Same full contexts and original pure facts under the established counts translation'],'adaptation':'Reuse the same cm_lookup_policy and cm_codegen_obligations boundary from verified counts; no additional abstraction or concrete TVM instantiation.'})
assert {r['function']for r in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_count_context_migration_lib.v').read_text();regs=coq_regions(lib)
assert not any(x['kind'] in ['Definition','Fixpoint','Record','Inductive','Lemma','Theorem'] for x in regs),'New declarations need explicit semantic review before recording.'
audit={'status':'Four contracts manually reviewed; final verification pending','contracts':rows,'annotation_stage_model_declarations':[],'inherited_model_boundary':'Counts library and layout lookup policy preserved byte-for-byte; four universally quantified emitter/TVM obligations still lack concrete Rocq instantiation. No new model definitions.','review_method':'Manual source/target pre/post and resource comparison; hashes only detect subsequent changes, not semantic equivalence.'}
previous=R/'metrics/semantic-audit.json'
if previous.exists():assert json.loads(previous.read_text())['contracts']==rows,'Contracts changed since main review; read and re-audit explicitly.'
previous.write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n')
baseline=[]
for x in regs:
 a,b=line_span(lib,x['start'],x['end']);fragment=lib[x['start']:x['end']]
 baseline.append(dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=hashlib.sha256(fragment.encode()).hexdigest()))
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Four reviewed contracts frozen; annotation library imports only.')
