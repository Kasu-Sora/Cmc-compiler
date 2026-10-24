"""Rebuild unchanged reused pure libraries in QCP's canonical logical path."""
from pathlib import Path
import hashlib,json,re,subprocess,time
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');B=Q/'Rocq';c=json.loads((R/'metrics/coq-config.json').read_text())
allowed={Path(x['path']).stem:x for x in json.loads((R/'metrics/reused-closure.json').read_text())};seen=set();records=[]
def build(name):
 if name in seen:return
 seen.add(name);x=allowed[name];p=Path(x['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256']
 for dep in re.findall(r'Require\s+(?:Export|Import)\s+SimpleC\.EE\.QCP_demos_human\.(\w+)',p.read_text()):build(dep)
 log=R/'logs'/f'canonical-reused-{name}.log';cmd=[c['coqc'],*c['flags'],str(p)];start=time.monotonic()
 with log.open('w')as f:result=subprocess.run(cmd,cwd=B,stdout=f,stderr=subprocess.STDOUT)
 records.append(dict(module=name,sha256=x['sha256'],command=cmd,exit_code=result.returncode,seconds=time.monotonic()-start,log=str(log),incremental_source_cost=0))
 (R/'metrics/canonical-reused-checks.json').write_text(json.dumps(records,indent=2)+'\n');print(name,result.returncode,flush=True)
 if result.returncode:print(log.read_text());raise SystemExit(result.returncode)
build('cmc_emit_code_migration_lib');build('cmc_emit_globals_migration_lib')
