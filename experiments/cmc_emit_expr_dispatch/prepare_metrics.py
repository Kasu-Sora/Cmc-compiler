from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parent
(R/'metrics/run.json').write_text(json.dumps({'run_id':'cmc_emit_expr_dispatch_migration-20261017164114'},indent=2)+'\n')
m=json.loads((R/'baseline/source-manifest.json').read_text());bad=[]
for row in m:
 for base in [R/'baseline/cstar_project',Path('/Users/nizitong/cmc')]:
  p=base/row['path']
  if hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256']:bad.append(str(p))
assert not bad
(R/'metrics/source-snapshot-audit.json').write_text(json.dumps(dict(status='passed',source_files_checked=len(m),differences=bad),indent=2)+'\n')
header=(R/'baseline/cmc_concrete_emit_expr_dispatch.h').read_text();src=(R/'baseline/cmc_concrete_emit_expr_dispatch.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());rows=[]
for f in fs:
 n=f['name'];mt=re.search(r'^void\s+'+n+r'\b',header,re.M);assert mt
 end=header.index(';',mt.start());attrs=lambda t:re.findall(r'\[\[cst::(\w+)\((.*?)\)\]\]',t,re.S)
 hs=attrs(header[mt.start():end]);ss=attrs('\n'.join('\n'.join(src[a-1:b])for a,b in f['specification']))
 norm=lambda a:[(k,re.sub(r'\s','',v))for k,v in a]
 rows.append(dict(function=n,identical=norm(hs)==norm(ss),body_contract=ss,header_contract=hs))
assert all(x['identical']for x in rows)
(R/'metrics/source-header-audit.json').write_text(json.dumps(dict(baseline='C body verified contract',difference=None,functions=rows),indent=2)+'\n')
(R/'metrics/process-notes.json').write_text(json.dumps({'status':'annotation in progress','historical_cstar_active_seconds':None,'human_active_seconds':None,'model_active_seconds':None,'annotation_development':{},'proof_development':{},'public_reuse':'Leaf library transitive closure; four verified leaf emitter body contracts'},indent=2)+'\n')
print('Source/header and 507 source snapshots checked.')
