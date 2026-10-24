#!/usr/bin/env python3
"""Freeze main's completed manual contract/model review; hashes only detect drift."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_data_migration.c').read_text()
src=(R/'baseline/cmc_concrete_emit_data.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text())
expected={f['name']for f in fs if not f['prototype']};assert expected=={'cmc_emit_data'}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 sources.append({'function':n,'contract':source})
 rows.append({'function':n,'source_contract_sha256':hashlib.sha256(source.encode()).hexdigest(),'target_contract_sha256':hashlib.sha256(target.encode()).hexdigest(),'checks':['All seven original pure preconditions also explicitly retained in Ensure: globals-safe, data-globals-wf, strings-safe, both size lower bounds, combined capacity and INT_MAX bound','Both global-list and string-list ownership restored, including source string byte arrays','Require empty initialized prefix and entire undefined destination','Ensure exact ((zeros 8 ++ cm_globals_bytes structs globals) ++ cm_strings_bytes strings)','Exact return and buffer boundary (8+globals_size)+strings_size; undefined remainder preserved','No added nonnull data or extra program/global/string validity conditions'],'adaptation':'Existing UCharArray segment predicates express original destination regions. Builtin zeros 8 is repeat 0 (Z.to_nat 8), matching source ireplicate 8 0; prior global/string models and ABI are unchanged.'})
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_data_migration_lib.v').read_text();regs=coq_regions(lib);models=[];baseline=[]
for x in regs:
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=hashlib.sha256(fragment.encode()).hexdigest());baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:models.append(item)
assert not models,'Additional models require explicit review.'
audit={'status':'Original emit-data composition contract, all retained pure facts and both list resources reviewed; final verification pending','contracts':rows,'annotation_stage_model_declarations':models,'inherited_model_boundary':'Immutable verified globals/strings/counts/layout/copy/word models; no new model, codegen obligation or TVM assumption introduced.','review_method':'Manual comparison of source/target conditions, resource ownership, arithmetic grouping and byte order; hashes detect drift and do not prove semantic equivalence.','composition_review':'Eight zeros followed by globals followed by strings, preserving original left-associated concatenation and original three helper contracts.'}
previous=R/'metrics/semantic-audit.json'
if previous.exists():assert json.loads(previous.read_text())['contracts']==rows,'Contract changed: re-review explicitly.'
previous.write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Reviewed emitter contract and new model recorded.')
