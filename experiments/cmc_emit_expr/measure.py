#!/usr/bin/env python3
"""Audit complete emit-expr migration and count final regions; does not run a prover."""
import hashlib,json,re,shutil
from audit_syntax import c_functions, coq_regions, coq_mask, line_span, nonblank
from pathlib import Path
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
RUN=json.loads((R/'metrics/run.json').read_text())['run_id']
P=Q/'reports'/RUN
state=json.loads((P/'controller_state.json').read_text())
assert state['phase']=='done' and state['final_check']['status']=='passed'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'baseline/cmc_concrete_emit_expr.c'
check=json.loads((R/'metrics/cstar-verification.json').read_text())
assert check['clean'] and check['source_sha256']==sha(source)
annotation=next(a for a in reversed(list(state['attempts'].values())) if a['phase']=='annotation' and a['status']=='accepted')
sealed=Path(annotation['annotation_history_directory'])/'after'
artifacts=[]
for role in ['c_file','formal_case_lib','goal_file','proof_auto_file','proof_manual_file','goal_check_file']:
 p=Q/state['target_files'][role]
 if role=='proof_manual_file':assert sha(p)==state['final_candidate']['proof_manual_sha256']
 elif role=='formal_case_lib':assert sha(p)==state['final_candidate']['proving_merged_lib_sha256']
 else:assert p.read_bytes()==(sealed/state['target_files'][role]).read_bytes()
 out=R/'target'/p.name;shutil.copy2(p,out)
 artifacts.append({'role':role,'canonical_path':str(p),'snapshot':str(out.relative_to(R)),'sha256':sha(p)})
abi=Q/'QCP_examples/QCP_demos_human/cmc_layout_migration_abi.h'
assert abi.read_bytes()==(R/'baseline/cmc_layout_migration_abi.h').read_bytes()
shutil.copy2(abi,R/'target'/abi.name)
artifacts.append({'role':'runtime_abi_header','canonical_path':str(abi),'sha256':sha(abi)})
(R/'target/manifest.json').write_text(json.dumps(artifacts,indent=2)+'\n')
shutil.copytree(P,R/'logs/qcp-controller',dirs_exist_ok=True)
shutil.copy2(Q/'verification_runs'/RUN/'makefile_dependency_snapshot.json',R/'logs/qcp-controller/makefile_dependency_snapshot.json')
fs=json.loads((R/'metrics/source-functions.json').read_text())
expected=[f['name']for f in fs if not f['prototype']]
assert len(expected)==7 and len(set(expected))==7
source_effort=json.loads((R/'metrics/source-effort.json').read_text())
# Per-function original contracts count once; forward prototype repeats body contract.
counts={'cstar':{},'qcp':{}};regions=[];counted_lines={};record_cache={}
for key in ['specification','annotation','inline_proof']:
 counts['cstar'][key]=sum(f[key]for f in source_effort['function_counts'])
for key in ['exported_shared_proof_closure','private_case_proof_support']:
 counts['cstar'][key]=sum(h['nonblank_lines']for h in source_effort['source_top_level_proof_helpers']if h['category']==key)
counts['cstar']['case_proof']=counts['cstar']['inline_proof']+counts['cstar']['private_case_proof_support']
counts['cstar']['proof_including_shared']=counts['cstar']['case_proof']+counts['cstar']['exported_shared_proof_closure']
def record(category,file,start,end,name=None):
 if file not in record_cache:
  content=(R/file).read_text()
  record_cache[file]=(coq_mask(content,mask_strings=False) if file.endswith('.v') else content).splitlines()
 counted=record_cache[file]
 n=sum(bool(l.strip())for l in counted[start-1:end])
 seen=counted_lines.setdefault((file,category),set())
 present={i for i in range(start,end+1) if counted[i-1].strip()}
 new_count=len(present-seen);seen.update(present)
 counts['qcp'][category]=counts['qcp'].get(category,0)+new_count
 fragment='\n'.join(counted[start-1:end])
 regions.append(dict(category=category,file=file,span=[start,end],nonblank_lines=n,new_counted_lines=new_count,lexical_tokens=len(re.findall(r'\w+|\S',fragment)),characters=len(fragment),name=name))
cfile='target/cmc_emit_expr_migration.c';c=(R/cfile).read_text()
# Ordinary comments and formal annotations do not affect runtime tokens.
runtime=re.sub(r'/\*.*?\*/|//[^\n]*','',c,flags=re.S)
runtime=re.sub(r'^\s*#.*$','',runtime,flags=re.M)
# Imported verified helper prototypes are integration declarations, not source bodies.
for f in reversed(c_functions(runtime)):
 if f['prototype'] and f['name'] not in expected:runtime=runtime[:f['start']]+runtime[f['end']:]
tokens=lambda s:re.findall(r'\w+|\S',s)
runtime_functions='\n'.join(runtime[f['start']:f['end']] for f in c_functions(runtime) if not f['prototype'])
assert tokens(runtime_functions)==tokens((R/'baseline/runtime-source.c').read_text()), 'Runtime function drift'
emitter_struct=re.search(r'struct cm_emitter \{.*?\};',runtime,re.S).group()
assert tokens(emitter_struct)==tokens((R/'baseline/emitter-abi.c').read_text()), 'Emitter ABI drift'
(R/'metrics/runtime-qcp.c').write_text(runtime)
cfs=c_functions(c)
assert [f['name'] for f in cfs if not f['prototype']]==expected
# All fifteen imported helper contracts are independently audited against previously verified BODY contracts.
helper_contract_audit=json.loads((R/'metrics/helper-contract-audit.json').read_text())
assert len(helper_contract_audit)==15
for f in cfs:
 if not f['prototype'] or f['name'] in expected:continue
 contract=''.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 row=next(x for x in helper_contract_audit if x['function']==f['name'])
 assert hashlib.sha256(contract.encode()).hexdigest()==row['target_contract_sha256']
 assert row['semantic_audit']=='passed'
per_function={fn:dict(specification=0,annotation=0,case_proof=0) for fn in expected}
for m in re.finditer(r'/\*@.*?\*/',c,re.S):
 block=m.group(); owner=next((f for f in cfs if f['start']<=m.start()<f['end']),None)
 category=('specification' if owner and m.start()<owner['body_start'] else 'annotation' if owner else 'coq_imports' if 'Import Coq' in block else 'external_declarations')
 a,b=line_span(c,m.start(),m.end())
 if c.splitlines()[b-1].strip() in ['*/','*/;']:b-=1
 if owner and owner['prototype']:
  category='duplicate_prototype_specification' if owner['name'] in expected else 'integration_helper_specification'
 record(category,cfile,a,b,owner['name'] if owner else None)
 if owner and not owner['prototype']:per_function[owner['name']][category]+=regions[-1]['nonblank_lines']
manualfile='target/cmc_emit_expr_migration_proof_manual.v';manual=(R/manualfile).read_text()
libfile='target/cmc_emit_expr_migration_lib.v';lib=(R/libfile).read_text()
for text in [manual,lib]:assert not re.search(r'\b(Admitted|Axiom|Parameter)\b',coq_mask(text))
assert not re.search(r'\bAbort\b',coq_mask(lib))
aborted=[]
def lemmas(text,file,category):
 names=[]
 for region in coq_regions(text):
  if 'ending' not in region:continue
  if region['ending']=='Abort':
   assert category=='case_proof' and '_split_goal_' in region['name']
   aborted.append(region['name']);continue
  assert region['ending'] in ['Qed','Defined']
  names.append(region['name']);a,b=line_span(text,region['start'],region['end'])
  record(category,file,a,b,region['name'])
  if category=='case_proof':
   fn=next((fn for fn in sorted(expected,key=len,reverse=True) if region['name'].startswith('proof_of_'+fn+'_')),None)
   if fn:per_function[fn]['case_proof']+=regions[-1]['nonblank_lines']
 return names
mn=lemmas(manual,manualfile,'case_proof');hn=lemmas(lib,libfile,'new_common_proof')
for name in aborted:
 assert re.sub(r'_split_goal_\d+$','',name) in mn, 'Unused split lacks proved parent: '+name
auto=(R/'target/cmc_emit_expr_migration_proof_auto.v').read_text();an=re.findall(r'^Lemma\s+(\w+)',auto,re.M)
assert len(an)==len(re.findall(r'\bAdmitted\.',auto))
top=[n for n in mn if '_split_goal_'not in n]
assert len(top)>0
coverage={fn:[]for fn in expected}
for n in top+an:
 fn=next((fn for fn in sorted(expected,key=len,reverse=True)if n.startswith('proof_of_'+fn+'_')),None)
 assert fn is not None,n
 coverage[fn].append(n)
assert all(coverage.values()),'An original function lacks generated/checked obligations'
# Model/representation declaration regions are audited from the actual completed lib.
# Preserve counts separately rather than swallowing library code into case proof.
model_names=[]
for region in coq_regions(lib):
 if region['kind'] in ['Ltac','Ltac2','Hint','Create','Set','Unset','Arguments']:
  a,b=line_span(lib,region['start'],region['end']);record('new_common_automation_or_configuration',libfile,a,b,region['name'])
 if region['kind'] in ['From','Require','Import','Open']:
  a,b=line_span(lib,region['start'],region['end']);record('new_common_imports_or_scopes',libfile,a,b)
 if region['kind'] not in ['Definition','Fixpoint','Inductive','Record']:continue
 model_names.append(region['name']);a,b=line_span(lib,region['start'],region['end'])
 record('new_common_definitions',libfile,a,b,region['name'])
for category in ['case_proof','new_common_proof','new_common_definitions']:
 counts['qcp'].setdefault(category,0)
counts['qcp']['proof_including_shared']=counts['qcp']['case_proof']+counts['qcp']['new_common_proof']
counts['qcp']['total_annotation_with_integration']=counts['qcp'].get('annotation',0)+counts['qcp'].get('integration_helper_specification',0)
counts['qcp']['specification_plus_annotation_with_integration']=counts['qcp']['specification']+counts['qcp']['total_annotation_with_integration']
for system in counts:
 counts[system].setdefault('annotation',0)
 counts[system]['specification_plus_annotation']=counts[system]['specification']+counts[system]['annotation']
counted_manual=coq_mask(manual,mask_strings=False)
body_lines=sum(nonblank(counted_manual,x['body_start'],x['body_end']) for x in coq_regions(manual) if 'body_start' in x and x['ending']!='Abort')
audit=json.loads((R/'metrics/semantic-audit.json').read_text())
assert audit['status']=='passed'
final_review=json.loads((R/'metrics/final-library-review.json').read_text())
assert final_review['status']=='passed'
assert final_review['manual_sha256']==hashlib.sha256(manual.encode()).hexdigest()
assert final_review['lib_sha256']==hashlib.sha256(lib.encode()).hexdigest()
for f in cfs:
 if f['prototype']:continue
 contract='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 reviewed=next(x for x in audit['contracts'] if x['function']==f['name'])
 assert hashlib.sha256(contract.encode()).hexdigest()==reviewed['target_contract_sha256'], 'Contract changed since semantic audit: '+f['name']
model_regions={r['name']:r for r in coq_regions(lib) if r['kind'] in ['Definition','Fixpoint','Inductive','Record']}
for reviewed in audit['annotation_stage_model_declarations']:
 region=model_regions[reviewed['name']]
 assert hashlib.sha256(lib[region['start']:region['end']].encode()).hexdigest()==reviewed['sha256'],'Model changed since audit: '+reviewed['name']
for dep in json.loads((R/'baseline/reused-dependencies.json').read_text()):
 assert sha(Path(dep['canonical_path']))==dep['sha256']
snapshot=json.loads((R/'logs/qcp-controller/makefile_dependency_snapshot.json').read_text())
reused=json.loads((R/'baseline/reused-dependencies.json').read_text())
for dep in reused:
 relative=str(Path(dep['canonical_path']).relative_to(Q))
 if not relative.endswith('.v'):continue
 assert any(x['relative_path']==relative and x['sha256']==dep['sha256'] for x in snapshot['base_sources']), 'Reused dependency absent from actual build: '+relative
assert not any('cmc_copy_bytes_migration_proof_' in x['relative_path'] for x in snapshot['base_sources'])
for region in coq_regions(manual):
 if region['kind'] in ['Ltac','Ltac2','Hint','Create','Set','Unset','Arguments']:
  a,b=line_span(manual,region['start'],region['end']);record('case_automation_or_configuration',manualfile,a,b,region['name'])
for fn in expected:
 per_function[fn]['specification_plus_annotation']=per_function[fn]['specification']+per_function[fn]['annotation']
timing=json.loads((P/'timing_summary.json').read_text())
result=dict(direction='C*/HOL -> QCP/Rocq',unit='cmc_concrete_emit_expr.c',function_count=7,counts=counts,regions=regions,source_effort=source_effort,target_per_function=per_function,runtime_tokens_equal=True,abi_unchanged=True,coverage=coverage,entries=dict(manual_top_level=len(top),manual_splits=len(mn)-len(top),automatic_witnesses=len(an),new_helpers=hn,new_model_declarations=model_names),proof_body_lines=body_lines,proof_wrapper_lines=counts['qcp']['case_proof']-body_lines,verification=dict(cstar=check,qcp_final_check=state['final_check'],phase=state['phase'],trusted_auto=an,remaining_manual=0),process=dict(timing=timing,notes=json.loads((R/'metrics/process-notes.json').read_text()),historical_cstar_active_seconds=None,human_active_seconds=None,model_active_seconds=None),artifacts=artifacts,counting_note='Nonblank exact regions, statement/Proof/Qed wrappers included, generated VC texts excluded; new shared definitions/proofs separate. Final source/target per-function and logical-definition classification audit required.')
result['verified_reused_dependencies']=reused
result['helper_contract_audit']=helper_contract_audit
result['counting_note']='Nonblank exact regions, statement/Proof/Qed wrappers included, generated VC texts and unused aborted split drafts excluded; new shared definitions/proofs separate. All seven runtime bodies and reviewed contracts/models retain their audited identities; case proof equals the per-function sum. Library declarations and all final proved helpers reviewed in final merged form.'
assert sum(x['case_proof'] for x in per_function.values())==counts['qcp']['case_proof']
masked_lib=coq_mask(lib);masked_manual=coq_mask(manual);lib_regions=coq_regions(lib)
usage=[]
for name in hn:
 declaration=next(x for x in lib_regions if x.get('name')==name)
 others=masked_lib[:declaration['start']]+masked_lib[declaration['end']:]
 usage.append(dict(name=name,direct_manual_references=len(re.findall(r'\b'+name+r'\b',masked_manual)),other_library_references=len(re.findall(r'\b'+name+r'\b',others)),lines=next(x['nonblank_lines'] for x in regions if x.get('name')==name and x['category']=='new_common_proof')))
result['shared_helper_usage']=usage
result['reused_helper_usage']=json.loads((R/'metrics/reused-helper-usage.json').read_text())
initial=json.loads((R/'metrics/annotation-library-baseline.json').read_text())
initial_names={x['name'] for x in initial}
result['common_cost_by_stage']={'annotation_definitions':sum(x['nonblank_lines'] for x in initial if x['kind'] in ['Definition','Fixpoint','Record','Inductive']), 'annotation_helpers':sum(x['nonblank_lines'] for x in initial if x['kind'] in ['Lemma','Theorem']), 'final_helpers_added_during_proving':[x for x in usage if x['name'] not in initial_names]}
result['source_text_size']=json.loads((R/'metrics/source-text-size.json').read_text())
result['process']['group_effort']=json.loads((R/'metrics/group-effort.json').read_text())
assert not result['process']['group_effort']['missing'], 'Missing owner check accounting'
result['source_additional_dependency_definitions']=json.loads((R/'metrics/source-additional-definitions.json').read_text())
(R/'metrics/shared-helper-usage.json').write_text(json.dumps(usage,indent=2)+'\n')
result['unused_split_drafts_aborted']=aborted
result['dependency_snapshot_metrics']=snapshot['dependency_metrics']
result['prior_dependency_function_proofs_imported']=False
assert not any(re.search(r'cmc_.*_migration_proof_',x['relative_path']) for x in snapshot['base_sources'])
counts['cstar']['additional_public_proof_closure']=result['source_additional_dependency_definitions']['public_proof_lines']
counts['cstar']['proof_including_shared']+=counts['cstar']['additional_public_proof_closure']
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':counts,'entries':result['entries'],'function_coverage':len(coverage),'runtime_tokens_equal':True},indent=2))
