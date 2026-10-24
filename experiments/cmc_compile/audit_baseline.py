from pathlib import Path
import json,hashlib,re,shutil
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');S=R/'baseline/cstar_project'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((R.parent/'cmc_compile_readiness/baseline/target-manifest.json').read_text())
ps={x['path']:x['sha256'] for x in old}
p=Q/'Rocq/examples/QCP_demos_human/cmc_compile_ready_migration_lib.v';ps[str(p)]=sha(p)
assert all(sha(Path(p))==h for p,h in ps.items())
(R/'baseline/target-manifest.json').write_text(json.dumps([dict(path=p,sha256=h)for p,h in sorted(ps.items())],indent=2)+'\n')
# This is a source-load dependency inventory, NOT a theorem-use closure or effort estimate.
graph={p.name:re.findall(r'^#require "([^"\n]+\.c)"',p.read_text(),re.M) for p in S.glob('*.c')}
seen=set();todo=['cmc.c']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(x for x in graph.get(n,[]) if x not in seen)
rows=[dict(file=n,exists=(S/n).exists(),direct_requires=graph.get(n,[])) for n in sorted(seen)]
(R/'metrics/source-load-dependencies.json').write_text(json.dumps(dict(note='Transitive #require load closure only; may include examples and unused theorem declarations. Not incremental proof cost.',files=rows),indent=2)+'\n')
print(dict(prior_targets_unchanged=len(ps),source_load_units=len(rows)))
