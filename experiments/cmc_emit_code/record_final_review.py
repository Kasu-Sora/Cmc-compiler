"""Bind completed manual/library review to accepted artifact hashes."""
from pathlib import Path
import hashlib,json
from audit_syntax import coq_regions
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id'];state=json.loads((Q/'reports'/run/'controller_state.json').read_text());assert state['phase']=='done' and state['final_check']['status']=='passed'
p=R/'metrics/final-library-review.json';review=json.loads(p.read_text());libpath=Q/state['target_files']['formal_case_lib'];manualpath=Q/state['target_files']['proof_manual_file'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert review['lib_sha256']==sha(libpath) and review['manual_sha256']==sha(manualpath)
lib=libpath.read_text();regions=coq_regions(lib);assert not [r for r in regions if r['kind'] in ['Lemma','Theorem','Corollary']]
proofs=[r for r in coq_regions(manualpath.read_text()) if 'ending' in r];assert proofs and all(r['ending']=='Qed' for r in proofs)
sp=R/'metrics/semantic-audit.json';semantic=json.loads(sp.read_text())
for x in semantic['annotation_stage_model_declarations']:
 r=next(r for r in regions if r.get('name')==x['name']);assert hashlib.sha256(lib[r['start']:r['end']].encode()).hexdigest()==x['sha256']
review.update(status='passed',new_helper_review={},model_review='Exact source cm_model_code = prelude ++ functions-from-zero composition retains reviewed annotation bytes.',manual_review='Reviewed every final region: context open/close preserves all original pure facts and full function-list ownership; PC-zero is derived from existing function PC/prefix definitions; exact plan composition is exposed with append associativity; both helper postconditions restore the exact original context/list/facts and final done/tail. All completed regions end in Qed. Controller checks statements/routes, imports, annotation seal and full goal-check.',proof_regions=len(proofs),support_mapping={'PC-zero':'Existing total cm_function_pc and prefix definitions, derived in the case proof without an added premise.','program read':'Existing context definition and same fields restored, retaining whole function-list ownership.','model composition':'Exact prelude then complete functions at fid zero; append associativity under arbitrary done/tail.','original facts':'All seven original pure facts retained through both helper calls and into postcondition.'},scope='One concrete emission implementation BODY, existing policy/cg boundary preserved; no new patch/link, compiler preservation or TVM execution/termination theorem.')
p.write_text(json.dumps(review,indent=2)+'\n');semantic.update(status='passed',final_library_review='final-library-review.json',final_model_hashes_unchanged=True,new_assumptions=False);sp.write_text(json.dumps(semantic,indent=2)+'\n');print('Final semantic review recorded against accepted hashes.')
