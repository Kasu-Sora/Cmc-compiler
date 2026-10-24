"""Check exact verified external BODY contracts and mutual-recursion interfaces."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest();norm=lambda s:re.sub(r'\s+','',s)
def contract(text,name,prototype):
 f=next(f for f in c_functions(text)if f['name']==name and f['prototype']==prototype)
 return '\n'.join(re.findall(r'/\*@.*?\*/',text[f['start']:f['body_start']],re.S))
rows=[]
for name,filename in json.loads((R/'metrics/helper-source-map.json').read_text()).items():
 new=contract(c,name,True);old=contract((R/'baseline/reused'/filename).read_text(),name,False)
 assert norm(new)==norm(old),'Helper BODY contract mismatch: '+name
 rows.append(dict(function=name,source_body_file=filename,target_contract_sha256=sha(new),previous_body_contract_sha256=sha(old),whitespace_normalized_identical=True,semantic_audit='passed'))
(R/'metrics/helper-contract-audit.json').write_text(json.dumps(rows,indent=2)+'\n')
mutual=[]
for f in c_functions(c):
 if f['prototype'] and f['name'] in ['cmc_emit_stmt','cmc_emit_if_stmt']:
  a=contract(c,f['name'],True);b=contract(c,f['name'],False)
  assert norm(a)==norm(b),'Mutual recursion contract mismatch: '+f['name']
  mutual.append(dict(function=f['name'],prototype_sha256=sha(a),body_sha256=sha(b),whitespace_normalized_identical=True))
assert any(x['function']=='cmc_emit_stmt'for x in mutual)
(R/'metrics/recursive-contract-audit.json').write_text(json.dumps(mutual,indent=2)+'\n')
print('External helper contracts checked:',len(rows),'recursive prototypes:',len(mutual))
