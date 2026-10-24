from pathlib import Path
import json,re,sys,runpy,hashlib
R=Path(__file__).resolve().parent
(R/'metrics/run.json').write_text(json.dumps({'run_id':'cmc_emit_expr_leaf_migration-20261017144315'},indent=2)+'\n')
p=R/'measure.py';s=p.read_text().replace('len(expected)==2 and len(set(expected))==2','len(expected)==9 and len(set(expected))==9').replace('function_count=2','function_count=9').replace('The two runtime bodies','The nine runtime bodies').replace('len(helper_contract_audit)==5','len(helper_contract_audit)==6')
a=s.index('helper_sources=');b=s.index('\nprior_texts=',a)
s=s[:a]+"helper_sources={**{n:'cmc_layout_migration.c' for n in ['cmc_string_address','cmc_type_size_at','cmc_member_array','cmc_pointee','cmc_member_offset_at']}, 'cm_emit_plan':'cmc_emit_plan_migration.c'}"+s[b:];p.write_text(s)
p=R/'measure_source.py';s=p.read_text().replace('Seven same-file static PROOF declarations counted as private case support; semantic address definitions and incremental public prefix bridge closure inventoried separately.','Eight same-file static PROOF declarations counted as private case support; new leaf-model and semantic size/address bridge closure inventoried separately.');p.write_text(s)
sys.path.insert(0,str(R));runpy.run_path(str(R/'measure_source.py'));runpy.run_path(str(R/'measure_text.py'))
m=json.loads((R/'baseline/source-manifest.json').read_text());bad=[]
for row in m:
 for base in [R/'baseline/cstar_project',Path('/Users/nizitong/cmc')]:
  p=base/row['path']
  if hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256']:bad.append(str(p))
assert not bad
(R/'metrics/source-snapshot-audit.json').write_text(json.dumps(dict(status='passed',source_files_checked=len(m),differences=bad),indent=2)+'\n')
header=(R/'baseline/cmc_concrete_emit_expr_leaf.h').read_text();src=(R/'baseline/cmc_concrete_emit_expr_leaf.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());rows=[]
for f in fs:
 n=f['name'];mt=re.search(r'^(?:void|int|long long)\s+'+n+r'\b',header,re.M)
 if mt is None:continue
 end=header.index(';',mt.start());attrs=lambda t:re.findall(r'\[\[cst::(\w+)\((.*?)\)\]\]',t,re.S)
 hs=attrs(header[mt.start():end]);ss=attrs('\n'.join('\n'.join(src[a-1:b])for a,b in f['specification']))
 norm=lambda a:[(k,re.sub(r'\s','',v))for k,v in a]
 rows.append(dict(function=n,identical=norm(hs)==norm(ss),body_contract=ss,header_contract=hs))
assert [x['function']for x in rows if not x['identical']]==['cm_emit_const_expr']
(R/'metrics/source-header-audit.json').write_text(json.dumps(dict(baseline='C body verified contract',difference='Header cm_emit_const_expr omits cm_type_code_wf ty from both pre and post; retained implementation contract, no claim of weaker header proof',functions=rows),indent=2)+'\n')
