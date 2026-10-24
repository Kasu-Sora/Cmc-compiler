from pathlib import Path
import json,re,shutil,subprocess,time,hashlib
R=Path(__file__).resolve().parent;W=R.parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');c=json.loads((R/'metrics/coq-config.json').read_text())
b=R/'build/Rocq';formal=b/'examples/QCP_demos_human'
manifest=json.loads((W/'baseline/target-manifest.json').read_text());allowed={Path(x['path']).stem:x for x in manifest if x['path'].endswith('.v')}
seen=set();records=[]
def prepare(n):
 if n in seen:return
 seen.add(n)
 row=allowed[n];src=Path(row['path']);assert hashlib.sha256(src.read_bytes()).hexdigest()==row['sha256']
 dst=formal/src.name
 if dst.exists():assert dst.read_bytes()==src.read_bytes()
 else:shutil.copy2(src,dst)
 text=re.sub(r'\(\*.*?\*\)','',src.read_text(),flags=re.S)
 for m in re.finditer(r'Require\s+(?:Import|Export)\s+([^\n]*?)\.(?:\s|$)',text):
  for dep in re.findall(r'SimpleC\.EE\.QCP_demos_human\.(\w+)',m.group(1)):prepare(dep)
 if dst.with_suffix('.vo').exists():return
 log=R/'logs'/f'prepare-{n}.log';cmd=[c['coqc'],*c['flags'],str(dst)];start=time.monotonic()
 with log.open('w')as f:p=subprocess.run(cmd,cwd=b,stdout=f,stderr=subprocess.STDOUT)
 records.append(dict(module=n,sha256=row['sha256'],command=cmd,exit_code=p.returncode,seconds=time.monotonic()-start))
 (R/'metrics/preparation.json').write_text(json.dumps(records,indent=2)+'\n')
 print(n,p.returncode,flush=True)
 if p.returncode:print(log.read_text());raise SystemExit(p.returncode)
prepare('cmc_emit_code_migration_lib')
prepare('cmc_emit_globals_migration_lib')
(R/'metrics/reused-closure.json').write_text(json.dumps([allowed[n]for n in sorted(seen)],indent=2)+'\n')
