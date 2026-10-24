from pathlib import Path
import json,subprocess,time,hashlib,sys,shutil
R=Path(__file__).resolve().parent; Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=json.loads((R/'metrics/coq-config.json').read_text()); mode=sys.argv[1]; names=sys.argv[2:]
rows=json.loads((R/'metrics/checks.json').read_text()) if (R/'metrics/checks.json').exists() else []
for name in names:
 src=R/'target'/f'{name}.v';dest=R/'build/Rocq/examples/QCP_demos_human'/src.name
 if mode!='kernel':shutil.copy2(src,dest)
 cmd=[c['coqc'],*c['flags'],str(dest)] if mode!='kernel' else [c['coqchk'],'-silent','-o',*c['flags'],'SimpleC.EE.QCP_demos_human.'+name]
 log=R/'logs'/f'{len(rows)+1:03d}-{mode}-{name}.log';start=time.monotonic()
 with log.open('w') as f:p=subprocess.run(cmd,cwd=R/'build/Rocq',stdout=f,stderr=subprocess.STDOUT)
 row=dict(mode=mode,module=name,command=cmd,exit_code=p.returncode,seconds=time.monotonic()-start,sha256=hashlib.sha256(src.read_bytes()).hexdigest(),log=str(log))
 rows=json.loads((R/'metrics/checks.json').read_text()) if (R/'metrics/checks.json').exists() else []
 rows.append(row);(R/'metrics/checks.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True);print(log.read_text()[-4000:],flush=True)
 if p.returncode:sys.exit(p.returncode)
