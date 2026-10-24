#!/usr/bin/env python3
"""Independently check the unused pure Rocq helper, outside the QCP C run.

Only compiles a hash-checked copy of the completed result and an assumptions
audit. Does not edit QCP sources, controller state, seals, or build products.
"""
import datetime
import hashlib
import json
import pathlib
import shutil
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parent
COQC = '/Users/nizitong/.opam/qcp-8.20.1/bin/coqc'
manifest = json.loads((ROOT / 'target/manifest.json').read_text())
item = next(x for x in manifest if x['role'] == 'formal_case_lib')
source = pathlib.Path(item['canonical_path'])
assert hashlib.sha256(source.read_bytes()).hexdigest() == item['sha256']
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
build = ROOT / 'logs' / (stamp + '-shared-helper')
build.mkdir()
shutil.copy2(source, build / source.name)
(build / 'AssumptionsAudit.v').write_text(
    'Require Import cmc_write_zeroes_migration_lib.\n'
    'Print Assumptions zeros_snoc__zero_step.\n')
checks = []
for filename in [source.name, 'AssumptionsAudit.v']:
    cmd = [COQC, '-q', '-Q', str(build), '', filename]
    started = time.monotonic()
    result = subprocess.run(cmd, cwd=build, text=True, capture_output=True)
    elapsed = time.monotonic() - started
    (build / (filename + '.stdout.txt')).write_text(result.stdout)
    (build / (filename + '.stderr.txt')).write_text(result.stderr)
    checks.append(dict(command=cmd, cwd=str(build), exit_code=result.returncode,
                       seconds=elapsed, stdout=result.stdout, stderr=result.stderr))
    if result.returncode:
        break
clean = (len(checks) == 2 and all(c['exit_code'] == 0 for c in checks)
         and 'Closed under the global context' in checks[-1]['stdout'])
report = dict(purpose='supplemental standalone pure Rocq helper validation',
              source=str(source), sha256=item['sha256'], clean=clean,
              used_by_case_manual=False, checks=checks)
(ROOT / 'metrics/shared-verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
raise SystemExit(0 if clean else 1)
