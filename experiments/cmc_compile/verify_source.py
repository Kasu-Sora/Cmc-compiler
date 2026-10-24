#!/usr/bin/env python3
"""Replay unchanged C* sources with bounded time, progress and complete attempt records."""
import argparse, datetime, hashlib, json, os, pathlib, shutil, signal, socket, subprocess, time
ROOT = pathlib.Path(__file__).resolve().parent
PROJECT = ROOT / 'baseline/cstar_project'
TOOLCHAIN = ROOT.parent / 'arr_sum/toolchain/cstar_v0.5.7_darwin-aarch64'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--timeout-seconds', type=int, default=3600)
p.add_argument('--heartbeat-seconds', type=int, default=30)
args = p.parse_args()
if args.timeout_seconds <= 0 or args.heartbeat_seconds <= 0:
    p.error('timeouts and heartbeat intervals must be positive')
assert (PROJECT/'cmc.c').read_bytes() == (ROOT/'baseline/cmc.c').read_bytes()
# Do not silently run against modified proof support.
for row in json.loads((ROOT/'baseline/source-manifest.json').read_text()):
    assert hashlib.sha256((PROJECT/row['path']).read_bytes()).hexdigest() == row['sha256'], row['path']
env = dict(os.environ, CSTAR_HOME=str(TOOLCHAIN))
env['PATH'] = str(TOOLCHAIN/'bin') + os.pathsep + env['PATH']
with socket.socket() as sock:
    sock.bind(('127.0.0.1', 0)); port = sock.getsockname()[1]
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
out = ROOT/'logs'/f'{stamp}-cstar-source'; out.mkdir()
cmd = [str(TOOLCHAIN/'bin/cstarc'), 'verify', 'cmc.c', '--port', str(port)]
record = dict(status='starting', clean=False, command=cmd, timeout_seconds=args.timeout_seconds,
              source_sha256=hashlib.sha256((PROJECT/'cmc.c').read_bytes()).hexdigest(),
              log_directory=str(out), cache_note='Existing compilation objects reused; HOL proof execution is still checked.',
              verification_seconds=None, exit_code=None, report=None)
server = worker = None
start = time.monotonic(); begin = None

def save():
    (out/'attempt.json').write_text(json.dumps(record, indent=2)+'\n')
    (ROOT/'metrics/cstar-verification.json').write_text(json.dumps(record, indent=2)+'\n')

def stop(proc):
    if proc is None: return
    # Kill the whole dedicated group, including the verifier spawned by cstarc.
    try: os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError: return
    try: proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try: os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError: pass
        proc.wait()
    # A leader can exit before its children. Remove any surviving group members.
    try: os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError: pass

save()
with (out/'server.log').open('w') as slog, (out/'stdout.txt').open('w') as stdout, (out/'stderr.txt').open('w') as stderr:
    try:
        server = subprocess.Popen([str(TOOLCHAIN/'bin/cstarc'), 'server', '--port', str(port)],
                                  cwd=PROJECT, env=env, stdout=slog, stderr=subprocess.STDOUT, start_new_session=True)
        record['server_pid'] = server.pid
        while True:
            if server.poll() is not None: raise RuntimeError('Prover exited during startup')
            try:
                with socket.create_connection(('127.0.0.1', port), timeout=.5): break
            except OSError:
                if time.monotonic()-start > 90: raise TimeoutError('Prover startup exceeded 90 seconds')
                time.sleep(.25)
        record['startup_seconds'] = time.monotonic()-start
        begin = time.monotonic()
        worker = subprocess.Popen(cmd, cwd=PROJECT, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        record.update(status='running', worker_pid=worker.pid); save()
        print(json.dumps(dict(log_directory=str(out), worker_pid=worker.pid, server_pid=server.pid, timeout_seconds=args.timeout_seconds)), flush=True)
        next_heartbeat = begin
        while worker.poll() is None:
            now = time.monotonic(); elapsed = now-begin
            if elapsed >= args.timeout_seconds:
                record.update(status='timeout', verification_seconds=elapsed)
                break
            if server.poll() is not None:
                record.update(status='server-exited', verification_seconds=elapsed, server_exit_code=server.returncode)
                break
            if now >= next_heartbeat:
                entry = dict(verification_seconds=round(elapsed, 2),
                             stdout_bytes=(out/'stdout.txt').stat().st_size,
                             stderr_bytes=(out/'stderr.txt').stat().st_size,
                             server_log_bytes=(out/'server.log').stat().st_size)
                # Process CPU time and RSS help distinguish ongoing computation from an idle wait.
                proc_rows = subprocess.run(['ps', '-axo', 'pid,ppid,pgid,time,%cpu,rss,state,comm'], text=True, capture_output=True)
                lines = proc_rows.stdout.splitlines()
                entry['processes'] = [line for line in lines[1:] if len(line.split()) >= 3 and line.split()[2] in {str(server.pid),str(worker.pid)}]
                with (out/'progress.jsonl').open('a') as f: f.write(json.dumps(entry)+'\n')
                print(json.dumps(entry), flush=True)
                next_heartbeat = now + args.heartbeat_seconds
            time.sleep(min(1, max(.01, args.timeout_seconds-elapsed)))
        if record['status'] == 'running':
            record.update(exit_code=worker.returncode, verification_seconds=time.monotonic()-begin)
            try: record['report'] = json.loads((out/'stdout.txt').read_text())
            except ValueError: pass
            report = record['report']
            record['clean'] = worker.returncode == 0 and isinstance(report,dict) and all(report.get(k)==[] for k in ['verification_conditions','axioms','strategies'])
            record['status'] = 'passed' if record['clean'] else 'failed'
    except Exception as exc:
        record.update(status='runner-error', error=repr(exc))
        if begin is not None: record['verification_seconds'] = time.monotonic()-begin
    finally:
        # Stop the client first; do not create misleading prover-disconnected errors by stopping the server first.
        stop(worker); stop(server)
        record['total_seconds'] = time.monotonic()-start
        record['cleanup_complete'] = True
        save()
print(json.dumps(record, indent=2), flush=True)
raise SystemExit(0 if record['clean'] else 124 if record['status']=='timeout' else 1)
