"""Measure accepted top C artifacts only after controller final-check succeeds."""
from pathlib import Path
import sys,json,re,hashlib,shutil
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sys.path.insert(0,str(R.parent/'cmc_patch_calls'))
from audit_syntax import c_functions,coq_regions,coq_mask,line_span
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
run='cmc_compile_migration-20261019230022';P=Q/'reports'/run;s=read(P/'controller_state.json')
assert s['phase']=='done' and s['final_check']['status']=='passed'
source=read(R/'metrics/source-effort.json');cstar=read(R/'metrics/cstar-verification.json')
assert cstar['clean'] and cstar['source_sha256']==sha(R/'baseline/cmc.c')==sha(Path('/Users/nizitong/cmc/cmc.c'))
a=next(a for a in reversed(list(s['attempts'].values()))if a['phase']=='annotation' and a['status']=='accepted');sealed=Path(a['annotation_history_directory'])/'after'
artifacts={}
for role in ['c_file','formal_case_lib','goal_file','proof_auto_file','proof_manual_file','goal_check_file']:
 p=Q/s['target_files'][role]
 if role=='proof_manual_file':assert sha(p)==s['final_candidate']['proof_manual_sha256']
 elif role=='formal_case_lib':assert sha(p)==s['final_candidate']['proving_merged_lib_sha256']
 else:assert p.read_bytes()==(sealed/s['target_files'][role]).read_bytes()
 dest=R/'target'/p.name;shutil.copy2(p,dest);artifacts[role]=dict(canonical_path=str(p),snapshot=str(dest),sha256=sha(p))
shutil.copytree(P,R/'logs/qcp-controller',dirs_exist_ok=True)
for f in ['makefile_dependency_snapshot.json']:
 p=Q/'verification_runs'/run/f
 if p.exists():shutil.copy2(p,R/'logs/qcp-controller'/f)
for x in read(R/'baseline/target-manifest.json'):assert sha(Path(x['path']))==x['sha256']
for x in read(R/'baseline/source-manifest.json'):assert sha(Path('/Users/nizitong/cmc')/x['path'])==x['sha256']
snapshot_path=Q/'verification_runs'/run/'makefile_dependency_snapshot.json'
if snapshot_path.exists():
 dependency=read(snapshot_path)
 assert not any(re.search(r'cmc_.*_migration_proof_',x['relative_path'])for x in dependency['base_sources']), 'Unexpected dependency on prior case proof templates'
text=lambda role:Path(artifacts[role]['snapshot']).read_text()
c=text('c_file');manual=text('proof_manual_file');lib=text('formal_case_lib');auto=text('proof_auto_file')
functions=c_functions(c);assert[f['name']for f in functions if not f['prototype']]==['cmc_compile']
strip=lambda x:re.sub(r'/\*.*?\*/|//[^\n]*','',x,flags=re.S)
tokens=lambda x:re.findall(r'\w+|\S',x)
rt='\n'.join(strip(c[f['start']:f['end']])for f in functions if not f['prototype'])
assert tokens(rt)==tokens((R/'baseline/runtime-source.c').read_text()),'Runtime changed'
abi=Q/'QCP_examples/QCP_demos_human/cmc_layout_migration_abi.h';assert abi.read_bytes()==(R/'baseline/cmc_layout_migration_abi.h').read_bytes()
emitter=re.search(r'struct cm_emitter \{.*?\};',strip(c),re.S).group()
assert tokens(emitter)==tokens((R/'baseline/emitter-abi.c').read_text()),'Emitter ABI changed'
regions=[];counts={};seen={}
def record(category,path,t,start,end,name=None):
 clean=coq_mask(t,mask_strings=False) if path.endswith('.v') else t
 lines=clean.splitlines();a,b=line_span(t,start,end)
 present={i for i in range(a,b+1)if lines[i-1].strip()};key=(path,category);fresh=present-seen.setdefault(key,set());seen[key]|=present
 counts[category]=counts.get(category,0)+len(fresh)
 regions.append(dict(category=category,file=path,span=[a,b],name=name,new_counted_lines=len(fresh)))
for m in re.finditer(r'/\*@.*?\*/',c,re.S):
 f=next((f for f in functions if f['start']<=m.start()<f['end']),None)
 category=('integration_helper_specification' if f['prototype'] else 'specification' if m.start()<f['body_start'] else 'annotation')if f else 'imports' if 'Import Coq'in m.group()else 'external_declarations'
 end=m.end();a,b=line_span(c,m.start(),end)
 if c.splitlines()[b-1].strip()in['*/','*/;']:end=c.rfind('\n',0,end)
 record(category,'target/cmc_compile_migration.c',c,m.start(),end,f['name']if f else None)
for t in[manual,lib]:
 masked=coq_mask(t)
 assert not re.search(r'\b(Admitted|admit)\b',masked)
 assert not any(r['kind'] in ['Axiom','Axioms','Parameter','Parameters'] for r in coq_regions(t))
assert not re.search(r'\bAbort\b',coq_mask(lib))
manual_names=[];public_names=[];aborted=[];defs=[]
for role,t in [('proof_manual_file',manual),('formal_case_lib',lib)]:
 file='target/'+Path(artifacts[role]['snapshot']).name;private=role=='proof_manual_file'
 for r in coq_regions(t):
  kind=r['kind'];cat=None
  if 'ending'in r:
   if r['ending']=='Abort':
    assert private and '_split_goal_'in r['name'];aborted.append(r['name']);continue
   assert r['ending']in['Qed','Defined'];cat='case_proof'if private else 'case_public_proof';(manual_names if private else public_names).append(r['name'])
  elif kind in ['Definition','Fixpoint','Inductive','Record']:
   cat='case_private_definitions'if private else 'case_public_definitions';defs.append(r['name'])
  elif kind in ['Ltac','Ltac2','Hint','Create']:cat='case_automation'if private else 'case_public_automation'
  if cat:record(cat,file,t,r['start'],r['end'],r.get('name'))
for n in aborted:assert re.sub(r'_split_goal_(?:\d+|spatial)$','',n)in manual_names
an=[r['name']for r in coq_regions(auto)if 'ending'in r];assert len(an)==len(re.findall(r'\bAdmitted\.',coq_mask(auto)))
top=[n for n in manual_names if '_split_goal_'not in n];assert top
for k in ['annotation','specification','integration_helper_specification','case_proof','case_automation','case_public_definitions','case_public_proof','case_public_automation']:counts.setdefault(k,0)
counts['specification_plus_annotation']=counts['specification']+counts['annotation']
counts['specification_plus_annotation_with_integration']=counts['specification_plus_annotation']+counts['integration_helper_specification']
overall_public=read(R/'metrics/effort.json')
math=overall_public['additional_public_dependency_cost_so_far']
import_closure={x['relative_path']for x in dependency['base_sources']}
module_usage=[]
for increment in overall_public['public_support_increments']:
 batch=Path(increment['path']).parent.parent
 for mod in read(batch/'metrics/publication.json'):
  canonical=Path(mod['path']);assert sha(canonical)==mod['sha256']
  module_usage.append(dict(path=str(canonical),in_import_closure=str(canonical.relative_to(Q))in import_closure))
write(R/'metrics/public-module-import-usage.json',module_usage)

result=dict(status='controller_verified_final_artifact_sizes',direction='C* -> QCP',unit='cmc_compile',source=source['totals'],target=counts,regions=regions,manual_top_level=len(top),manual_splits=len(manual_names)-len(top),automatic_trusted_witnesses=len(an),automatic_admitted_names=an,unused_aborted_split_drafts=aborted,new_case_public_lemmas=public_names,new_case_definitions=defs,mathematical_public_cost=math,source_dependency_slice='source-dependency-slice.json',source_to_target_full_dependency_ratio=None,runtime_tokens_equal=True,original_sources_unchanged=True,prior_targets_unchanged=True,artifacts=artifacts,controller_final_check=s['final_check'],historical_source_active_time=None,human_active_time=None,counting_note='Nonempty noncomment physical lines, deduplicated per category. Proof includes statements and Proof/Qed. Generated VC text excluded; public definitions, proofs and automation separate. Imported prior helpers have zero new proof cost; their copied contracts are integration annotation. Trusted proof_auto Admitted is not an independent kernel certificate.')
result['automatic_top_level_vcs']=len([n for n in an if not n.endswith('_pure')])
result['automatic_pure_subobligations']=len([n for n in an if n.endswith('_pure')])
write(R/'metrics/final-effort.json',result);write(R/'target/manifest.json',artifacts)
print(json.dumps({k:v for k,v in result.items()if k in['target','manual_top_level','manual_splits','automatic_trusted_witnesses','new_case_public_lemmas','new_case_definitions']},ensure_ascii=False))
