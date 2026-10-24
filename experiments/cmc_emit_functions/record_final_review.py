"""Record completed final review, bound to controller-accepted artifacts."""
import hashlib,json
from pathlib import Path
from audit_syntax import coq_regions
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id']
state=json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert state['phase']=='done' and state['final_check']['status']=='passed'
p=R/'metrics/final-library-review.json';review=json.loads(p.read_text())
libpath=Q/state['target_files']['formal_case_lib'];manualpath=Q/state['target_files']['proof_manual_file']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert review['lib_sha256']==sha(libpath) and review['manual_sha256']==sha(manualpath)
lib=libpath.read_text();regions=coq_regions(lib)
assert not [r for r in regions if r['kind'] in ['Lemma','Theorem','Corollary']]
proofs=[r for r in coq_regions(manualpath.read_text()) if 'ending' in r]
assert len(proofs)==41 and all(r['ending']=='Qed' for r in proofs)
sp=R/'metrics/semantic-audit.json';semantic=json.loads(sp.read_text())
for x in semantic['annotation_stage_model_declarations']:
 r=next(r for r in regions if r.get('name')==x['name'])
 assert hashlib.sha256(lib[r['start']:r['end']].encode()).hexdigest()==x['sha256']
review.update(status='passed',new_helper_review={},
 model_review='Exact nil/cons function-list emission equation and transparent tail observation retain reviewed annotation bytes; head emission is determined by current fid exactly as in source.',
 manual_review='Reviewed all 41 final proof regions, covering 12 top-level obligations and 29 splits: readiness projections and reused statement length, null/cons resource shape, context open/fold, next-PC integer arithmetic, recursive resource restoration and append associativity. All end in Qed; controller also checks statements, routes, imports, unchanged annotation seal and full goal-check.',
 support_mapping={
 'private ready-fact injection':'Transparent readiness definitions and proved conjunct extraction, with no new premise.',
 'statement code length/count':'Existing cm_emit_stmt_length__stmt_capacity connects reused normalized readiness to exact emitter contract.',
 'function list null/cons and head context':'Existing list/context representations and explicit separation logic reasoning; whole list restored after recursion.',
 'head-count return retargeting':'Local cell annotation with its generated proof obligation; original runtime value unchanged.',
 'fid and next PC safety':'Original readiness successor bounds and exact next-PC equation; no added entry fid constraint.',
 'emission list combination':'Exact recursive model and append associativity with arbitrary done/tail.'},
 scope='One runtime BODY contract and necessary proof support; existing lookup-policy/codegen-obligations parameterization retained; no new TVM execution, termination, linking or compilation-preservation theorem.')
p.write_text(json.dumps(review,indent=2)+'\n')
semantic.update(status='passed',final_library_review='final-library-review.json',final_model_hashes_unchanged=True,new_assumptions=False)
sp.write_text(json.dumps(semantic,indent=2)+'\n')
print('Final semantic review recorded against accepted hashes.')
