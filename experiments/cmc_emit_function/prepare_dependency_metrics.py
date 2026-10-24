"""Freeze actual library import closure and source of reused helper BODY contracts."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
lib=Q/'Rocq/examples/QCP_demos_human/cmc_emit_function_migration_lib.v'
manifest=json.loads((R/'baseline/reused-manifest.json').read_text());byname={Path(x['canonical_path']).name:x for x in manifest}
names=set(re.findall(r'cmc_\w+_migration_lib',lib.read_text()))-{'cmc_emit_function_migration_lib'};seen=set()
while names-seen:
 n=sorted(names-seen)[0];seen.add(n);names|=set(re.findall(r'cmc_\w+_migration_lib',(R/'baseline/reused'/(n+'.v')).read_text()))
helpers={'cmc_code_slot_size': 'cmc_layout_migration.c', 'cm_emit_normalize_plan': 'cmc_emit_plan_migration.c', 'cm_emit_fp_address_plan': 'cmc_emit_plan_migration.c', 'cm_emit_store_plan': 'cmc_emit_plan_migration.c', 'cmc_frame_size': 'cmc_layout_migration.c', 'cm_emit_plan': 'cmc_emit_plan_migration.c', 'cmc_function_prologue_count': 'cmc_counts_migration.c', 'cmc_stmt_temps': 'cmc_layout_migration.c', 'cmc_emit_stmt': 'cmc_emit_stmt_migration.c', 'cm_emit_return_epilogue_plan': 'cmc_emit_return_migration.c'}
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_function_migration.c').read_text()
actual={f['name'] for f in c_functions(c)if f['prototype']}-{'cmc_emit_param_stores_from','cmc_emit_prologue','cmc_emit_function'}
assert actual==helpers.keys(),actual
rows=[]
for n in sorted({n+'.v' for n in seen}|set(helpers.values())):
 x=byname[n];assert hashlib.sha256(Path(x['canonical_path']).read_bytes()).hexdigest()==x['sha256']
 rows.append(dict(canonical_path=x['canonical_path'],sha256=x['sha256'],snapshot='baseline/reused/'+n,incremental_definitions=0,incremental_proof=0))
abi=Q/'QCP_examples/QCP_demos_human/cmc_layout_migration_abi.h';assert abi.read_bytes()==(R/'baseline'/abi.name).read_bytes()
rows.append(dict(canonical_path=str(abi),sha256=hashlib.sha256(abi.read_bytes()).hexdigest(),snapshot='baseline/'+abi.name,incremental_definitions=0,incremental_proof=0))
(R/'baseline/reused-dependencies.json').write_text(json.dumps(rows,indent=2)+'\n')
(R/'metrics/helper-source-map.json').write_text(json.dumps(helpers,indent=2)+'\n')
print('Actual imported library closure',len(seen),'helper C files',len(set(helpers.values())))
