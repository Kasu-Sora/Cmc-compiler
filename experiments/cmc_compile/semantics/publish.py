"""Publish only kernel-checked public mathematics; no runtime case/skill edits."""
from pathlib import Path
import json,hashlib,subprocess,time,shutil
R=Path(__file__).resolve().parent;E=R.parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');B=Q/'Rocq'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=json.loads((R/'metrics/checks.json').read_text());effort=json.loads((R/'metrics/effort.json').read_text())
k=next(x for x in reversed(checks) if x['mode']=='kernel' and x['module']=='SemanticsAudit')
assert k['exit_code']==0 and k['sha256']==sha(R/'target/SemanticsAudit.v')
a=next(x for x in reversed(checks) if x['mode']=='development' and x['module']=='SemanticsAudit')
log=Path(a['log']).read_text();assert a['exit_code']==0
assert log.count('AUDIT ')==log.count('Closed under the global context')==effort['expected_assumption_audits']
assert 'Axioms:' not in log
for x in effort['modules']:assert sha(Path(x['file']))==x['sha256']
for x in json.loads((E/'baseline/target-manifest.json').read_text()):assert sha(Path(x['path']))==x['sha256']
order=['cmc_tvm_object_migration_lib','cmc_tower_semantics_migration_lib','cmc_tvm_execution_migration_lib','cmc_source_state_migration_lib','cmc_source_initial_migration_lib','cmc_source_call_migration_lib','cmc_source_execution_migration_lib','cmc_simulation_state_migration_lib','cmc_preservation_observation_migration_lib']
c=json.loads((R/'metrics/coq-config.json').read_text());records=[]
for name in order:
 src=R/'target'/f'{name}.v';dst=B/'examples/QCP_demos_human'/src.name
 if dst.exists():assert sha(dst)==sha(src),f'Refusing to overwrite different existing source: {dst}'
 else:shutil.copy2(src,dst)
 cmd=[c['coqc'],*c['flags'],str(dst)];logpath=R/'logs'/f'publish-{name}.log';t=time.monotonic()
 with logpath.open('w')as f:p=subprocess.run(cmd,cwd=B,stdout=f,stderr=subprocess.STDOUT)
 records.append(dict(module=name,path=str(dst),sha256=sha(dst),command=cmd,exit_code=p.returncode,seconds=time.monotonic()-t,log=str(logpath)))
 (R/'metrics/publication.json').write_text(json.dumps(records,indent=2)+'\n');print(name,p.returncode,flush=True)
 if p.returncode:print(logpath.read_text());raise SystemExit(p.returncode)
