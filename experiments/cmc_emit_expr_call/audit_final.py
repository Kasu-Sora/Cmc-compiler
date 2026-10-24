"""Freeze final provenance and enumerate actual reused lemmas, after controller success."""
import hashlib,json,re
from pathlib import Path
from audit_syntax import coq_regions,coq_mask
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id']
s=json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert s['phase']=='done' and s['final_check']['status']=='passed'
paths={k:Q/v for k,v in s['target_files'].items() if isinstance(v,str)}
manual=paths['proof_manual_file'].read_text();lib=paths['formal_case_lib'].read_text()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(paths['proof_manual_file'])==s['final_candidate']['proof_manual_sha256']
assert sha(paths['formal_case_lib'])==s['final_candidate']['proving_merged_lib_sha256']
for t in (manual,lib): assert not re.search(r'\b(?:Admitted|Axiom|Parameter)\b',coq_mask(t))
usage=[]
for dep in json.loads((R/'baseline/reused-dependencies.json').read_text()):
 p=Path(dep['canonical_path'])
 assert sha(p)==dep['sha256']
 if p.suffix!='.v':continue
 for region in coq_regions(p.read_text()):
  if region['kind'] not in ('Lemma','Theorem','Corollary'):continue
  name=region['name'];pat=r'\b'+re.escape(name)+r'\b'
  nm=len(re.findall(pat,coq_mask(manual)));nl=len(re.findall(pat,coq_mask(lib)))
  if nm+nl:usage.append(dict(name=name,canonical_path=str(p),manual_references=nm,new_library_references=nl,incremental_lines=0))
(R/'metrics/reused-helper-usage.json').write_text(json.dumps(usage,indent=2)+'\n')
review=dict(status='controller-passed; final semantic review recorded separately',manual_sha256=sha(paths['proof_manual_file']),lib_sha256=sha(paths['formal_case_lib']),new_library_declarations=[dict(kind=x['kind'],name=x.get('name'),ending=x.get('ending')) for x in coq_regions(lib)],no_new_manual_or_library_admitted_axiom_parameter=True,reused_dependencies_unchanged=True,prior_helper_function_proofs_imported=False)
(R/'metrics/final-library-review.json').write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({'phase':s['phase'],'actual_reused_lemmas':usage},indent=2))
