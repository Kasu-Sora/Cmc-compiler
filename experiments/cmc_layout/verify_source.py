#!/usr/bin/env python3
"""Check an unmodified isolated C* source snapshot; never edit the original repo."""
import datetime, hashlib, json, os, pathlib, shutil, signal, socket, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
PROJECT=ROOT/'baseline/cstar_project'
TOOLCHAIN=ROOT.parent/'arr_sum/toolchain/cstar_v0.5.7_darwin-aarch64'
if not PROJECT.exists():
    shutil.copytree('/Users/nizitong/cmc', PROJECT, ignore=shutil.ignore_patterns('.git','_verif'))
if not (PROJECT/'proof/proof.h').exists():
    shutil.copytree(ROOT.parent/'cmc_write_byte/baseline/cstar_project/proof',PROJECT/'proof',dirs_exist_ok=True,ignore=shutil.ignore_patterns('.git','_verif'))
assert (PROJECT/'cmc_concrete_layout.c').read_bytes()==(ROOT/'baseline/cmc_concrete_layout.c').read_bytes()
env=dict(os.environ, CSTAR_HOME=str(TOOLCHAIN))
env['PATH']=str(TOOLCHAIN/'bin')+os.pathsep+env['PATH']
with socket.socket() as s:
    s.bind(('127.0.0.1',0)); port=s.getsockname()[1]
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out=ROOT/'logs'/f'{stamp}-cstar-source'; out.mkdir()
start=time.monotonic()
with (out/'server.log').open('w') as log:
    proc=subprocess.Popen([str(TOOLCHAIN/'bin/cstarc'),'server','--port',str(port)],cwd=PROJECT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    try:
        while True:
            if proc.poll() is not None: raise RuntimeError('Prover stopped')
            try:
                with socket.create_connection(('127.0.0.1',port),timeout=.5): break
            except OSError:
                if time.monotonic()-start>90: raise TimeoutError('Prover startup timeout')
                time.sleep(.25)
        cmd=[str(TOOLCHAIN/'bin/cstarc'),'verify','cmc_concrete_layout.c','--port',str(port)]
        begin=time.monotonic()
        with (out/'stdout.txt').open('w') as stdout,(out/'stderr.txt').open('w') as stderr:
            result=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=stdout,stderr=stderr,timeout=600)
        elapsed=time.monotonic()-begin
        try: report=json.loads((out/'stdout.txt').read_text())
        except ValueError: report=None
        clean=result.returncode==0 and isinstance(report,dict) and all(report.get(k)==[] for k in ['verification_conditions','axioms','strategies'])
        record=dict(command=cmd,exit_code=result.returncode,report=report,clean=clean,verification_seconds=elapsed,source_sha256=hashlib.sha256((PROJECT/'cmc_concrete_layout.c').read_bytes()).hexdigest(),log_directory=str(out))
        (ROOT/'metrics/cstar-verification.json').write_text(json.dumps(record,indent=2)+'\n')
        print(json.dumps(record,indent=2),flush=True)
    finally:
        if proc.poll() is None:
            os.killpg(proc.pid,signal.SIGTERM)
            try: proc.wait(timeout=10)
            except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); proc.wait()

raise SystemExit(0 if clean else (result.returncode or 2))
