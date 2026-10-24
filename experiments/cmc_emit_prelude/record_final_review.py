"""Record independent semantic/proof review against controller accepted hashes."""
from pathlib import Path
import hashlib,json
from audit_syntax import coq_regions
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id'];state=json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert state['phase']=='done' and state['final_check']['status']=='passed'
p=R/'metrics/final-library-review.json';review=json.loads(p.read_text())
libpath=Q/state['target_files']['formal_case_lib'];manualpath=Q/state['target_files']['proof_manual_file'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert review['lib_sha256']==sha(libpath) and review['manual_sha256']==sha(manualpath)
lib=libpath.read_text();regions=coq_regions(lib)
assert not [r for r in regions if r['kind'] in ['Lemma','Theorem','Corollary']]
proofs=[r for r in coq_regions(manualpath.read_text()) if 'ending' in r]
assert proofs and all(r['ending']=='Qed' for r in proofs)
sp=R/'metrics/semantic-audit.json';semantic=json.loads(sp.read_text())
for x in semantic['annotation_stage_model_declarations']:
 r=next(r for r in regions if r.get('name')==x['name']);assert hashlib.sha256(lib[r['start']:r['end']].encode()).hexdigest()==x['sha256']
review.update(status='passed',new_helper_review={},model_review='Exact 11-instruction source sequence retains reviewed annotation bytes, including CALL at total cm_function_pc policy p (cm_program_main p). No extra validity assumptions.',manual_review='Reviewed every final proof region: program-context opening/restoration, main_id equality, fixed plan expansion, per-call opcode facts and sequence routing, append associativity and final plan/context restoration. All end in Qed; controller checks exact statements/routes, imports, annotation seal and full goal-check.',proof_regions=len(proofs),support_mapping={'context read':'Existing cm_program_context_rep definition; exact field ownership reopened and folded.','instruction sequence':'Transparent exact source model, opcode computation and existing plan predicates.','CALL':'Exact main_id equality and unrestricted cm_emit_call_plan contract; no entry-validity precondition.','final output':'Append associativity combines singleton emissions under arbitrary done/tail.'},scope='One runtime BODY contract; existing lookup-policy boundary retained. No new main execution, termination, linking or compiler preservation theorem.')
p.write_text(json.dumps(review,indent=2)+'\n');semantic.update(status='passed',final_library_review='final-library-review.json',final_model_hashes_unchanged=True,new_assumptions=False);sp.write_text(json.dumps(semantic,indent=2)+'\n')
print('Final semantic review recorded against accepted hashes.')
