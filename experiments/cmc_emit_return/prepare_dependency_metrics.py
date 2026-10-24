from pathlib import Path
import json,re,hashlib,shutil
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
lib=Q/'Rocq/examples/QCP_demos_human/cmc_emit_return_migration_lib.v'
manifest=json.loads((R/'baseline/reused-manifest.json').read_text());byname={Path(x['canonical_path']).name:x for x in manifest}
names=set(re.findall(r'cmc_\w+_migration_lib',lib.read_text()));seen=set()
while names-seen:
 n=sorted(names-seen)[0];seen.add(n);names|=set(re.findall(r'cmc_\w+_migration_lib',(R/'baseline/reused'/(n+'.v')).read_text()))
selected=[n+'.v' for n in sorted(seen)]+['cmc_emit_plan_migration.c']
rows=[]
for n in selected:
 x=byname[n];assert hashlib.sha256(Path(x['canonical_path']).read_bytes()).hexdigest()==x['sha256']
 rows.append(dict(canonical_path=x['canonical_path'],sha256=x['sha256'],snapshot='baseline/reused/'+n,incremental_definitions=0,incremental_proof=0))
abi=Q/'QCP_examples/QCP_demos_human/cmc_layout_migration_abi.h'
assert abi.read_bytes()==(R/'baseline'/abi.name).read_bytes()
rows.append(dict(canonical_path=str(abi),sha256=hashlib.sha256(abi.read_bytes()).hexdigest(),snapshot='baseline/'+abi.name,incremental_definitions=0,incremental_proof=0))
(R/'baseline/reused-dependencies.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Actual imported library closure',len(seen),'plus 1 helper C file and ABI')
