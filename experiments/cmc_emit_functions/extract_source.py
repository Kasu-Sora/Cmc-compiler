#!/usr/bin/env python3
"""Extract runtime functions and exact effort regions from the fixed C* baseline."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parent
p=R/'baseline/cmc_concrete_emit_functions.c';s=p.read_text()
# Mask quoted terms/strings/comments while preserving positions and newlines.
pattern=r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\''
masked=re.sub(pattern,lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S)
def block_end(start):
 d=1;i=start+1
 while d:
  d+=(masked[i]=='{')-(masked[i]=='}');i+=1
 return i
line=lambda pos:s[:pos].count('\n')+1
spans=lambda a,b:[line(a),line(b-1)]
functions=[];chunks=[]
for m in re.finditer(r'^(?:static )?(?:int|long long|void)\s+(\w+)\s*\(',masked,re.M):
 # Attributes have only quoted payloads; the first brace/semicolon is real body/prototype.
 delim=re.search(r'[{};]',masked[m.end():]);at=m.end()+delim.start()
 assert masked[at] in '{;'
 end=block_end(at) if masked[at]=='{' else at+1
 text=s[m.start():end];proof=[]
 for pm in re.finditer(r'\[\[cst::proof\]\]\s*\{',masked[m.start():end]):
  a=m.start()+pm.start();b=block_end(m.start()+pm.end()-1);proof.append((a,b))
 attrs=[]
 for am in re.finditer(r'\[\[cst::(?!proof\b)(\w+).*?\]\]',s[m.start():end],re.S):
  a=m.start()+am.start();b=m.start()+am.end();attrs.append((a,b,am.group(1)))
 remove=sorted([(a,b)for a,b in proof]+[(a,b)for a,b,k in attrs],reverse=True)
 runtime=text
 for a,b in remove:runtime=runtime[:a-m.start()]+runtime[b-m.start():]
 runtime='\n'.join(l for l in runtime.splitlines() if l.strip())+'\n'
 chunks.append(runtime)
 functions.append({'name':m.group(1),'prototype':masked[at]==';','source_span':spans(m.start(),end),'specification':[spans(a,b)for a,b,k in attrs if a<at], 'annotation':[spans(a,b)for a,b,k in attrs if a>at], 'inline_proof':[spans(a,b)for a,b in proof],'runtime':runtime})
(R/'baseline/runtime-source.c').write_text('\n'.join(chunks))
(R/'metrics/source-functions.json').write_text(json.dumps(functions,indent=2)+'\n')
print(json.dumps({'function_bodies':sum(not f['prototype']for f in functions),'forward_declarations':sum(f['prototype']for f in functions),'names':[f['name']for f in functions if not f['prototype']],'runtime_lines':sum(bool(l.strip())for l in '\n'.join(chunks).splitlines()),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()},indent=2))
