"""Publish evidence for type readiness only; never mark the compiler complete."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
R=Path(__file__).resolve().parent;E=R.parent;W=E.parent.parent
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='TypesAudit');a=next(x for x in reversed(checks)if x['mode']=='development' and x['module']=='TypesAudit')
assert k['exit_code']==a['exit_code']==0 and k['sha256']==a['sha256']==sha(R/'target/TypesAudit.v')
log=Path(a['log']).read_text();assert log.count('AUDIT ')==log.count('Closed under the global context')==eff['expected_assumption_audits'] and 'Axioms:'not in log
assert len(pub)==len(eff['modules']) and all(x['exit_code']==0 and sha(Path(x['path']))==x['sha256']for x in pub)
for x in eff['modules']:assert sha(Path(x['file']))==x['sha256']
for x in read(R/'metrics/kernel-input-manifest.json'):assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['vo']))==x['vo_sha256']
for x in read(E/'baseline/source-manifest.json'):assert sha(Path('/Users/nizitong/cmc')/x['path'])==sha(E/'baseline/cstar_project'/x['path'])==x['sha256']
for f in [E/'baseline/target-manifest.json',R/'baseline/previous-public-manifest.json']:
 for x in read(f):assert sha(Path(x['path']))==x['sha256']
for p,h in read(R/'baseline/frozen-inputs.json').items():assert sha(Path(p))==h
for name,p in [('SKILL.md',Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md')),('migration_inventory.csv',W/'migration_inventory.csv')]:assert sha(p)==sha(E/'baseline/documentation-before'/name)
doc=read(R/'metrics/external-documentation-change.json');assert sha(Path(doc['path']))==doc['observed_sha256']
components=read(E/'tagged/metrics/invariant-components.json')
for x in components['components']:
 if x['name']=='cm_task_type_ready':x.update(target_definition_present=True,transition_status='proved_along_successful_execution_with_verified_support_invariants',iteration_theorem='cm_source_termination_type_ready')
components['note']='Sixteen components proved by actual initial/step/iter proofs. Two components and original full preservation remain pending.'
write(R/'metrics/invariant-components.json',components)
verified=[x['name']for x in components['components']if x['transition_status'].startswith('proved')];remaining=[x['name']for x in components['components']if not x['transition_status'].startswith('proved')];assert len(verified)==16 and len(remaining)==2
obligations=read(E/'tagged/metrics/remaining-obligations.json')
for x in obligations['remaining']:
 x['detail']=x['detail'].replace('Fifteen','Sixteen').replace('fifteen-component','sixteen-component').replace('type, code-layout','code-layout')
write(R/'metrics/remaining-obligations.json',obligations)
eff.update(status='kernel_checked_published_public_support_only',tool_seconds=sum(x['seconds']for x in checks),publication_tool_seconds=sum(x['seconds']for x in pub));write(R/'metrics/effort.json',eff)
write(R/'metrics/development-failures.json',dict(attempts=[x for x in checks if x['exit_code']],note='All failures retained; no unfinished goals published. Final 24 modules pass 88 closed-context audits and independent kernel checking.'))
now=eff['totals'];checkpoint=dict(status='incremental_public_support_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),top_level_qcp_verified=False,public_modules=24,public_cost=now,assumption_audits=88,axioms_used_by_new_proofs=[],kernel=k,canonical_publication_all_passed=True,original_components_proved_along_successful_execution=verified,new_components=['cm_task_type_ready'],remaining_components=remaining,top_level_vcs_generated=False,skill_updated=False,remaining_obligations=str(R/'metrics/remaining-obligations.json'))
write(R/'metrics/checkpoint.json',checkpoint)
batches=['semantics','preservation','invariants','structural','transport','runtime','readiness','tagged','types'];incs=[dict(path=str(E/n/'metrics/effort.json'),totals=read(E/n/'metrics/effort.json')['totals'])for n in batches];total={key:sum(x['totals'].get(key,0)for x in incs)for key in set().union(*(x['totals']for x in incs))}
status=read(E/'metrics/status.json');status.update(status='in_progress_sixteen_support_invariants_verified_full_simulation_pending',public_support_checkpoints=[str(E/n/'metrics/checkpoint.json')for n in batches],latest_public_support_checkpoint=checkpoint,additional_public_dependency_cost_so_far=total,new_verified_public_definitions=total['definitions'],new_verified_public_lemmas=total['lemmas'],skill_updated=False,inventory_success_updated=False,current_dependency_gap='Sixteen original components proved along successful source execution. Pending code-layout and full target simulation. Original preservation, success bridge and top QCP remain incomplete.');write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall.update(status=checkpoint['status'],additional_public_dependency_cost_so_far=total,public_support_increments=incs,note='Nine verified increments. Top final annotation/proof and complete C* dependency closure remain null. Partial same-name source lines are not a comparable migration-cost denominator.');overall['target_completed_this_attempt'].update(verified_public_definitions=total['definitions'],verified_public_lemmas=total['lemmas'],public_definition_lines=total['definition_lines'],public_proof_lines=total['proof_lines']);write(E/'metrics/effort.json',overall)
source=read(R/'metrics/source-reference-cost.json')['totals']
print(json.dumps(dict(increment=now,cumulative=total,verified=16,remaining=2),ensure_ascii=False))
