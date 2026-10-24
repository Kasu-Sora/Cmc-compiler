from pathlib import Path
import hashlib,json,shutil,subprocess
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/cmc');Q=Path('/Users/nizitong/QCP/qcp-binary-democases');P=R.parent/'cmc_patch_calls'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (R/'baseline').exists()
for d in ['baseline/reused','baseline/documentation-before','metrics','logs','target']:(R/d).mkdir(parents=True,exist_ok=True)
shutil.copytree(S,R/'baseline/cstar_project',ignore=shutil.ignore_patterns('.git','_verif'))
source=[dict(path=str(p.relative_to(S)),sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and p.suffix in ['.c','.h'] and '.git' not in p.parts and '_verif' not in p.parts]
(R/'baseline/source-manifest.json').write_text(json.dumps(source,indent=2)+'\n')
for n in ['cmc.c','cmc.h']:shutil.copy2(S/n,R/'baseline'/n)
prior=list((Q/'QCP_examples/QCP_demos_human').glob('cmc_*_migration.c'))+list((Q/'Rocq/examples/QCP_demos_human').glob('cmc_*_migration_lib.v'))
rows=[]
for p in sorted(prior):
 shutil.copy2(p,R/'baseline/reused'/p.name);rows.append(dict(canonical_path=str(p),sha256=sha(p)))
(R/'baseline/reused-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
shutil.copy2(Q/'QCP_examples/QCP_demos_human/cmc_layout_migration_abi.h',R/'baseline/cmc_layout_migration_abi.h')
shutil.copy2(P/'baseline/emitter-abi.c',R/'baseline/emitter-abi.c')
state={}
for name,path in [('source',S),('qcp',Q),('workspace',W)]:state[name]={k:subprocess.run(['git',*args],cwd=path,text=True,capture_output=True).stdout for k,args in [('head',['rev-parse','HEAD']),('status',['status','--short'])]}
(R/'baseline/repository-state.json').write_text(json.dumps(state,indent=2)+'\n')
old=json.loads((P/'baseline/tooling-modified-files.json').read_text());tooling=[dict(path=x['path'],sha256=sha(Path(x['path'])))for x in old];(R/'baseline/tooling-modified-files.json').write_text(json.dumps(tooling,indent=2)+'\n')
docs=[Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md'),W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']
for p in docs:shutil.copy2(p,R/'baseline/documentation-before'/p.name)
(R/'metrics/documentation-baseline.json').write_text(json.dumps([dict(path=str(p),sha256=sha(p))for p in docs],indent=2)+'\n')
print({'source_files':len(source),'prior_target_files':len(rows)})
