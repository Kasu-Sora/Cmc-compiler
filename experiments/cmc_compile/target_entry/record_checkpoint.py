"""Publish evidence for complete code-layout invariant support; never mark the compiler complete."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
R=Path(__file__).resolve().parent;E=R.parent;W=E.parent.parent
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='TargetEntryAudit');a=next(x for x in reversed(checks)if x['mode']=='development' and x['module']=='TargetEntryAudit')
assert k['exit_code']==a['exit_code']==0 and k['sha256']==a['sha256']==sha(R/'target/TargetEntryAudit.v')
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
components=read(E/'code_cont/metrics/invariant-components.json')
for x in components['components']:
 if x['name']=='cm_task_layout':x.update(target_definition_present=True,transition_status='proved_initial_step_iter_under_successful_source_execution')
components['note']='Seventeen components have actual initial/step/iter proofs, including full code layout. Full target simulation remains pending.'
write(R/'metrics/invariant-components.json',components)
verified=[x['name']for x in components['components']if x['transition_status'].startswith('proved')];remaining=[x['name']for x in components['components']if not x['transition_status'].startswith('proved')];assert len(verified)==17 and len(remaining)==1
obligations=read(E/'code_cont/metrics/remaining-obligations.json')
for x in obligations['remaining']:
 if x['id']=='preservation_step':x['detail']='Seventeen components, including full code layout, proved along successful source executions. Target simulation additionally covers unary/load/output/branches/halt/exit and block/loop scope restoration. All S starts, member/index and short-circuit operations, temporary stores and reloads now proved. Source initialization, assignment stores all ordinary binary cases and complete C control dispatch from original invariants now proved. Pending-call memory transport and pointwise store comparison support now proved. Parameter permutation and completion have now been proved constructively by pointwise state equality under the original function well-formedness, frame segment and arity conditions. The actual parameter TVM sequence to original cm_enter_call and the 14-instruction prologue prefix are now proved. Prologue caller-to-pending-machine bridge, full call transition, Start/prelude and total dispatch remain. No new C preconditions or axioms.'
obligations['next_layout_steps']=[]
write(R/'metrics/remaining-obligations.json',obligations)
coverage=read(R/'metrics/transition-coverage.json');coverage['status']='kernel_checked_and_canonically_published';write(R/'metrics/transition-coverage.json',coverage)
eff.update(status='kernel_checked_published_partial_target_simulation',tool_seconds=sum(x['seconds']for x in checks),publication_tool_seconds=sum(x['seconds']for x in pub));write(R/'metrics/effort.json',eff)
write(R/'metrics/development-failures.json',dict(attempts=[x for x in checks if x['exit_code']],note='All failures retained; all new modules pass closed-context audits and independent kernel checking. Target simulation is partial; no full target invariant or preservation is claimed.'))
now=eff['totals'];checkpoint=dict(status='partial_target_simulation_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),top_level_qcp_verified=False,public_modules=len(eff['modules']),public_cost=now,assumption_audits=eff['expected_assumption_audits'],axioms_used_by_new_proofs=[],kernel=k,canonical_publication_all_passed=True,original_components_proved_along_successful_execution=verified,new_components=[],partial_components=['cm_task_target_sim'],remaining_components=remaining,top_level_vcs_generated=False,skill_updated=False,remaining_obligations=str(R/'metrics/remaining-obligations.json'))
write(R/'metrics/checkpoint.json',checkpoint)
batches=['semantics','preservation','invariants','structural','transport','runtime','readiness','tagged','types','code_layout','code_expr','code_cont','target_expr','target_value','target_state','target_store','target_binary','target_return','target_call','target_params','target_entry'];incs=[dict(path=str(E/n/'metrics/effort.json'),totals=read(E/n/'metrics/effort.json')['totals'])for n in batches];total={key:sum(x['totals'].get(key,0)for x in incs)for key in set().union(*(x['totals']for x in incs))}
status=read(E/'metrics/status.json');status.update(status='in_progress_seventeen_support_invariants_verified_full_simulation_pending',public_support_checkpoints=[str(E/n/'metrics/checkpoint.json')for n in batches],latest_public_support_checkpoint=checkpoint,additional_public_dependency_cost_so_far=total,new_verified_public_definitions=total['definitions'],new_verified_public_lemmas=total['lemmas'],skill_updated=False,inventory_success_updated=False,current_dependency_gap='Seventeen original components proved along successful source execution, including full code-layout induction. Full target simulation remains. Original preservation, success bridge and top QCP incomplete.');write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall.update(status=checkpoint['status'],additional_public_dependency_cost_so_far=total,public_support_increments=incs,note='Twenty-one verified public increments, including full code layout and partial target simulation. Seventeen complete component invariants. Top final annotation/proof and complete C* dependency closure remain null. Partial same-name source lines are not a comparable migration-cost denominator.');overall['target_completed_this_attempt'].update(verified_public_definitions=total['definitions'],verified_public_lemmas=total['lemmas'],public_definition_lines=total['definition_lines'],public_proof_lines=total['proof_lines']);write(E/'metrics/effort.json',overall)
print(json.dumps(dict(increment=now,cumulative=total,verified=17,remaining=1),ensure_ascii=False))
