"""Check post-verification documentation and unchanged formal/source artifacts."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases');S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
run=json.loads((R/'metrics/run.json').read_text())['run_id']
state=json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert state['phase']=='done' and state['final_check']['status']=='passed'
source=json.loads((R/'baseline/source-manifest.json').read_text())
for row in source:
 assert sha(Path('/Users/nizitong/cmc')/row['path'])==row['sha256']
 assert sha(R/'baseline/cstar_project'/row['path'])==row['sha256']
for row in json.loads((R/'baseline/reused-manifest.json').read_text()):assert sha(Path(row['canonical_path']))==row['sha256']
for row in json.loads((R/'target/manifest.json').read_text()):assert sha(Path(row['canonical_path']))==row['sha256']
for row in json.loads((R/'baseline/tooling-modified-files.json').read_text()):assert sha(Path(row['path']))==row['sha256']
a=(R/'baseline/documentation-before/migration_inventory.csv').read_bytes().splitlines();b=(W/'migration_inventory.csv').read_bytes().splitlines()
assert len(a)==len(b)
diff=[(x,y) for x,y in zip(a,b) if x!=y]
assert len(diff)==1 and {row[0].split(b',')[0] for row in diff}=={b'/Users/nizitong/cmc/cmc_concrete_emit_code.c'}
assert 'Skill is valid' in (R/'logs/skill-validation.log').read_text()
files=[S/'SKILL.md',S/'references/cmc-emit-code-case.md',W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']
result=dict(status='passed',updated_after_final_check=True,recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),controller_run=run,controller_phase=state['phase'],skill_validation='logs/skill-validation.log',covered_implementation_units=29,covered_runtime_functions=129,source_files_unchanged=len(source),formal_artifacts_unchanged_after_documentation=True,inventory_rows_changed=len(diff),files=[dict(path=str(p),sha256=sha(p)) for p in files])
(R/'metrics/skill-update.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
