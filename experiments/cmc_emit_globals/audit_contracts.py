#!/usr/bin/env python3
"""Freeze main's completed manual contract/model review; hashes only detect drift."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_globals_migration.c').read_text()
src=(R/'baseline/cmc_concrete_emit_globals.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text())
expected={f['name']for f in fs if not f['prototype']};assert expected=={'cmc_emit_globals'}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 sources.append({'function':n,'contract':source})
 rows.append({'function':n,'source_contract_sha256':hashlib.sha256(source.encode()).hexdigest(),'target_contract_sha256':hashlib.sha256(target.encode()).hexdigest(),'checks':['Original globals safety and complete pointwise global wellformedness retained and restored','Same nonnegative cursor, capacity bound and total output-space requirement','Global-list ownership preserved','Original initialized prefix followed by exact cm_globals_bytes, with same undefined remainder','Exact returned cursor+representation size','No added nonnull data or initialized-value precondition; empty list and all original branches preserved'],'adaptation':'Existing UCharArray segment predicates represent source initialized and undefined byte regions; same verified global models and ABI reused.'})
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_lib.v').read_text();regs=coq_regions(lib);models=[];baseline=[]
for x in regs:
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=hashlib.sha256(fragment.encode()).hexdigest());baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:models.append(item)
assert {x['name']for x in models}=={'cm_data_globals_wf'},'Additional models require explicit review.'
audit={'status':'Original emitter contract and complete data-global wellformedness reviewed; final verification pending','contracts':rows,'annotation_stage_model_declarations':models,'inherited_model_boundary':'Immutable verified counts/layout/copy-bytes and word encoding models; this case does not introduce lookup-policy or codegen-obligations parameters. Full pointer-initialization restrictions remain in existing cm_global_wf.','review_method':'Manual comparison of source/target pre/post resources and definition conjuncts; hashes are drift checks, not an automatic equivalence proof.','encoding_bridge_review':'Existing counts map/seq/power-divisor model must be proved equal to existing eight-entry word model for all signed values, without replacing either dependency.'}
previous=R/'metrics/semantic-audit.json'
if previous.exists():assert json.loads(previous.read_text())['contracts']==rows,'Contract changed: re-review explicitly.'
previous.write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Reviewed emitter contract and new model recorded.')
