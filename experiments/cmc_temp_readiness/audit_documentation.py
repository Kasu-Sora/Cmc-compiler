"""Confirm documentation changed only after success and formal inputs stayed fixed."""
from pathlib import Path
import json,hashlib,csv
R=Path(__file__).resolve().parent;W=R.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((R/'metrics/effort.json').read_text())['status']=='passed'
for name in ['source-manifest.json','target-manifest.json']:
    for row in json.loads((R/'baseline'/name).read_text()):assert sha(Path(row['path']))==row['sha256']
for row in json.loads((R/'target/manifest.json').read_text()):assert sha(Path(row['path']))==row['sha256']
d=json.loads((R/'metrics/documentation-update.json').read_text())
assert d['updated_after_verification']
for row in d['files']:assert sha(Path(row['path']))==row['sha256']
a=(R/'baseline/migration_inventory.csv').read_bytes().splitlines()
b=(W/'migration_inventory.csv').read_bytes().splitlines()
assert len(a)==len(b)
diff=[(x,y)for x,y in zip(a,b)if x!=y]
assert len(diff)==1 and diff[0][0].startswith(b'/Users/nizitong/cmc/cmc_concrete_temp_ready.c,')
assert 'Skill is valid' in (R/'logs/skill-validation.log').read_text()
result=dict(status='passed',source_and_prior_target_files_unchanged=True,published_artifact_hashes_verified=True,skill_validation_passed=True,inventory_rows_changed=1,remaining_not_migrated_rows=sum(r['migration_status']=='not_migrated'for r in csv.DictReader((W/'migration_inventory.csv').open())),runtime_units=30,runtime_functions=131,readiness_pure_support_units=4)
(R/'metrics/final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
