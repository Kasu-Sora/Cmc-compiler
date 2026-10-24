"""Compile the pure Rocq module in a frozen accepted dependency closure."""
from pathlib import Path
import json, subprocess, time, hashlib, shutil, sys
R = Path(__file__).resolve().parent
Q = Path('/Users/nizitong/QCP/qcp-binary-democases')
config = json.loads((R/'metrics/coq-config.json').read_text())
p = Q/'Rocq/examples/QCP_demos_human/cmc_code_ready_migration_lib.v'
kind = sys.argv[1] if len(sys.argv)>1 else 'development'
if kind == 'audit':
    p = R/'target/CodeReadinessAudit.v'
dest = R/'build/Rocq/examples/QCP_demos_human'/p.name
shutil.copy2(p, dest)
history = R/'metrics/checks.json'
rows = json.loads(history.read_text()) if history.exists() else []
args = [config['coqc'], *config['flags'], str(dest)]
cwd = R/'build/Rocq'
if kind == 'publication':
    cwd = Q/'Rocq'
    args = [config['coqc'], *config['flags'], str(p)]
if kind == 'kernel':
    args = [config['coqchk'], '-silent', '-o', *config['flags'], 'SimpleC.EE.QCP_demos_human.cmc_code_ready_migration_lib']
log = R/'logs'/f'{len(rows)+1:02d}-{kind}.log'
start = time.monotonic()
with log.open('w') as f:
    proc = subprocess.run(args,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
row = dict(kind=kind, command=args, cwd=str(cwd), exit_code=proc.returncode,
    elapsed_seconds=time.monotonic()-start, source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(), log=str(log))
rows.append(row);history.write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(row,indent=2));print(log.read_text()[-6000:])
sys.exit(proc.returncode)
