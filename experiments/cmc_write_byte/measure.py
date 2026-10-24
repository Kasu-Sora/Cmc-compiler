#!/usr/bin/env python3
"""Snapshot the accepted controller result and count explicitly classified regions."""
import datetime, hashlib, json, pathlib, re, shutil
ROOT=pathlib.Path(__file__).resolve().parent
QCP=pathlib.Path('/Users/nizitong/QCP/qcp-binary-democases')
RUN='cmc_write_byte_migration-20261015151544'
REPORT=QCP/'reports'/RUN
state=json.loads((REPORT/'controller_state.json').read_text())
assert state['phase']=='done' and state['final_check']['status']=='passed'
source_check=json.loads((ROOT/'metrics/cstar-verification.json').read_text())
assert source_check['clean']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ROOT/'baseline/cmc_concrete_emit_bytes.c')==source_check['source_sha256']
manifest=[]
annotation=next(a for a in state['attempts'].values() if a['phase']=='annotation' and a['status']=='accepted')
sealed=pathlib.Path(annotation['annotation_history_directory'])/'after'
for role in ['c_file','formal_case_lib','goal_file','proof_auto_file','proof_manual_file','goal_check_file']:
    rel=state['target_files'][role]; p=QCP/rel
    if role=='proof_manual_file':
        assert sha(p)==state['final_candidate']['proof_manual_sha256']
    elif role=='formal_case_lib':
        assert sha(p)==state['final_candidate']['proving_merged_lib_sha256']
    else:
        assert p.read_bytes()==(sealed/rel).read_bytes(), 'Accepted file drift: '+rel
    out=ROOT/'target'/p.name; shutil.copy2(p,out)
    manifest.append(dict(role=role,canonical_path=str(p),snapshot=str(out.relative_to(ROOT)),sha256=sha(p)))
for rel in ['controller_state.json','controller_target_topology.json','timing_summary.json','run_logs.json',
            'annotation-attempts/annotation-attempt1/agent_output.md',
            'annotation-attempts/annotation-attempt1/agent_report.json',
            'annotation-attempts/annotation-attempt1/annotation_plan.json',
            'rounds/cmc_write_byte_migration-vc-proving-r1/proving_merged_result.json']:
    out=ROOT/'logs/qcp-controller'/rel; out.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(REPORT/rel,out)
p=QCP/'verification_runs'/RUN/'makefile_dependency_snapshot.json'
shutil.copy2(p,ROOT/'logs/qcp-controller/makefile_dependency_snapshot.json')
(ROOT/'target/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Stable original regions; each count lists its source and exact inclusive lines.
regions=[
 ('cstar','specification','baseline/cmc_concrete_emit_bytes.c',[(13,26)]),
 ('cstar','case_proof','baseline/cmc_concrete_emit_bytes.c',[(28,37),(39,47)]),
 ('cstar','imports_exports','baseline/cmc_concrete_emit_bytes.c',[(1,6),(8,9)]),
 ('qcp','specification','target/cmc_write_byte_migration.c',[(8,15)]),
 ('qcp','external_predicate_declarations','target/cmc_write_byte_migration.c',[(1,3)]),
 ('qcp','case_lib_seed','target/cmc_write_byte_migration_lib.v',[(1,3)]),
 # Existing direct source dependency excerpts, not a full transitive library size.
 ('cstar_reused','byte_range_definition','baseline/tower_base.c',[(16,17)]),
 ('cstar_reused','fill_wrapper_proof','baseline/cmc_rep.c',[(3049,3058),(3060,3069),(3107,3110)]),
 ('cstar_reused','fill_generic_proof','baseline/userlib/array.c',[(187,193),(197,200)]),
]
counts={k:{} for k in ['cstar','qcp','cstar_reused']}; classified=[]
for system,category,file,spans in regions:
    lines=(ROOT/file).read_text().splitlines()
    n=sum(bool(lines[i-1].strip()) for a,b in spans for i in range(a,b+1))
    counts[system][category]=counts[system].get(category,0)+n
    classified.append(dict(system=system,category=category,file=file,spans=spans,nonblank_lines=n,sha256=sha(ROOT/file)))
for system in ['cstar','qcp']:
    counts[system]['annotation']=0
    counts[system]['specification_plus_annotation']=counts[system]['specification']
counts['qcp']['case_proof']=0
manual=(ROOT/'target/cmc_write_byte_migration_proof_manual.v').read_text()
lib=(ROOT/'target/cmc_write_byte_migration_lib.v').read_text()
auto=(ROOT/'target/cmc_write_byte_migration_proof_auto.v').read_text()
assert not re.search(r'\b(Lemma|Theorem|Admitted|Axiom)\b',manual)
assert not re.search(r'\b(Definition|Fixpoint|Inductive|Lemma|Theorem|Admitted|Axiom)\b',lib)
auto_lemmas=re.findall(r'^Lemma\s+(\w+)',auto,re.M)
assert len(auto_lemmas)==2 and len(re.findall(r'\bAdmitted\.',auto))==2
source_lines=(ROOT/'baseline/cmc_concrete_emit_bytes.c').read_text().splitlines()
remove={i for a,b in [(28,37),(39,47)] for i in range(a,b+1)}
source='\n'.join(l for i,l in enumerate(source_lines,1) if i>=11 and i not in remove)
source=re.sub(r'\[\[cst::.*?\]\]','',source,flags=re.S)
target=re.sub(r'/\*.*?\*/','',(ROOT/'target/cmc_write_byte_migration.c').read_text(),flags=re.S)
tokens=lambda s:re.findall(r'\w+|\S',s)
assert tokens(source)==tokens(target)
(ROOT/'metrics/runtime-cstar.c').write_text(source+'\n')
(ROOT/'metrics/runtime-qcp.c').write_text(target+'\n')
reused=[]
for file in ['Rocq/SeparationLogic/ArrayLib.v','Rocq/SeparationLogic/ArrayLibCore.v']:
    p=QCP/file; out=ROOT/'baseline/qcp-reused'/p.name
    out.parent.mkdir(exist_ok=True);shutil.copy2(p,out)
    reused.append(dict(canonical_path=str(p),sha256=sha(p),classification='existing-target-library-not-new-migration'))
timing=json.loads((REPORT/'timing_summary.json').read_text())
result=dict(direction='C*/HOL -> QCP/Rocq',function='cmc_write_byte',
  counting_method='Nonblank physical lines in exact regions, syntax wrappers included, standalone QCP */ excluded. Function contract counted once, duplicated C* header excluded. Inline C* proof blocks count as proof, not annotation.',
  counts=counts,regions=classified,runtime_tokens_equal=True,
  newly_migrated_common=dict(model_definitions=0,representation_predicates=0,helper_lemmas=0,model_lines=0,proof_lines=0,generated_seed_scaffolding_lines=3),
  entries=dict(cstar_contract_items=3,qcp_contract_items=3,cstar_logic_parameters=2,qcp_logic_parameters=2,cstar_body_annotations=0,qcp_body_annotations=0,cstar_proof_blocks=2,qcp_handwritten_case_lemmas=0,qcp_automatic_witnesses=2),
  verification=dict(cstar=source_check,qcp_phase=state['phase'],qcp_final_check=state['final_check'],qcp_trusted_auto_admissions=auto_lemmas,qcp_remaining_manual_vcs=0,cross_prover_equivalence_theorem=False),
  process=dict(controller_timing=timing,historical_cstar_active_seconds=None,human_active_seconds=None,model_active_seconds=None,source_environment_failed_checks=1,initial_controller_python_version_rejection=1,annotation_candidates=1,annotation_repairs=0),
  reused_target_dependencies=reused,artifacts=manifest)
(ROOT/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(counts=counts,new_common=result['newly_migrated_common'],qcp_run_seconds=timing['run']['elapsed_seconds'],runtime_tokens_equal=True),indent=2))
