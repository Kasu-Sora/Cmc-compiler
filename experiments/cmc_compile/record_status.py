from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');run='cmc_compile_migration-20261019230022';A=Q/'reports'/run/'annotation-attempts/annotation-attempt1'
for n in ['agent_report.json','agent_output.md','annotation_plan.json']:
 shutil.copy2(A/n,R/'logs'/n)
for n in ['controller_state.json','controller_target_topology.json']:
 shutil.copy2(Q/'reports'/run/n,R/'logs'/n)
for p in [Q/'QCP_examples/QCP_demos_human/cmc_compile_migration.c',Q/'Rocq/examples/QCP_demos_human/cmc_compile_migration_lib.v']:
 shutil.copy2(p,R/'target'/p.name)
result=dict(status='blocked_before_target_verification',controller_run=run,annotation_attempt='cmc_compile_migration-annotation-r1-attempt-1',owner='/root/compile_annotation',accepted_annotation_report=json.loads((A/'agent_report.json').read_text()),finalize_delivery={'status':'blocked','errors':[]},target_checks_run=0,target_vcs=None,target_completed_annotation_lines=0,target_completed_proof_lines=0,new_verified_public_definitions=0,new_verified_public_lemmas=0,final_target_annotation_cost=None,final_target_proof_cost=None,additional_public_dependency_cost=None,historical_source_development_time=None,human_active_time=None,skill_updated=False,inventory_success_updated=False,retry_error=dict(command='controller.py --main-root '+str(Q)+' retry-round --run '+run+' --phase annotation --reason annotation-blocked --previous-attempt cmc_compile_migration-annotation-r1-attempt-1',exit_code=1,exception='FileNotFoundError',missing_file=str(Q/'verification_runs'/run/'annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_compile_migration_proof_manual.v'),explanation='Controller returned retry-round after accepting pre-VC dependency blocker, but retries require a manual artifact not yet generated. No fabricated manual file or state edit used.'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result['original_sources_unchanged']=all(sha(Path('/Users/nizitong/cmc')/x['path'])==x['sha256'] for x in json.loads((R/'baseline/source-manifest.json').read_text()))
result['prior_targets_unchanged']=all(sha(Path(x['path']))==x['sha256'] for x in json.loads((R/'baseline/target-manifest.json').read_text()))
result['documentation_unchanged']=all(sha(Path(x['path']))==x['sha256'] for x in json.loads((R/'metrics/documentation-baseline.json').read_text()))
assert result['original_sources_unchanged'] and result['prior_targets_unchanged'] and result['documentation_unchanged']
(R/'metrics/status.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print({k:result[k]for k in ['status','original_sources_unchanged','prior_targets_unchanged','documentation_unchanged']})
