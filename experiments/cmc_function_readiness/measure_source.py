from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parent
rows=[]
for filename in ['cmc_concrete_function_ready.c']:
 s=(R/'baseline'/filename).read_text()
 masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S)
 for m in re.finditer(r'^PROOF\s+(?:static\s+)?\w+\s+(\w+)\b',masked,re.M):
  at=m.end();depth=0
  while at<len(masked):
   c=masked[at]
   if c=='{':depth+=1
   elif c=='}':
    depth-=1
    if depth==0:at+=1;break
   elif c==';' and depth==0:at+=1;break
   at+=1
  frag=s[m.start():at];name=m.group(1)
  kind='definition' if re.search(r'new_(?:fun|rec)_definition',frag) else 'getter' if name.startswith('get_') else 'framework_scaffolding' if name.startswith('_') else 'proof'
  rows.append(dict(name=name,file='baseline/'+filename,kind=kind,span=[s[:m.start()].count('\n')+1,s[:at-1].count('\n')+1],nonblank_lines=sum(bool(l.strip())for l in frag.splitlines()),text=frag,sha256=hashlib.sha256(frag.encode()).hexdigest()))
result=dict(runtime_functions=0,annotation=0,specification=0,source_top_level_proof_helpers=rows,totals={k:sum(x['nonblank_lines']for x in rows if x['kind']==k)for k in ['definition','proof','getter','framework_scaffolding']})
(R/'metrics/source-effort.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['totals'])
print([(r['name'],r['kind'],r['nonblank_lines'])for r in rows])
