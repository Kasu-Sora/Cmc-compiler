from pathlib import Path
import json,re
R=Path(__file__).resolve().parent;S=R/'baseline/cstar_project'
roots={'cmc_correct.c':['cmc_prove_successful_exec_simulation','cmc_successful_exec_simulation','cmc_prove_valid_input_bridge','cmc_valid_input_bridge','cmc_prove_preservation','cmc_preservation'],'cmc_rep.c':['cm_output_decodes_def','cm_output_decode_unique','cm_model_output_decodes']}
rows=[]
for filename,names in roots.items():
 text=(S/filename).read_text();masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),text,flags=re.S)
 for name in names:
  m=re.search(r'^PROOF\s+(?:static\s+)?\w+\s+'+name+r'\b',masked,re.M);assert m,name
  end=m.end();depth=0
  while end<len(masked):
   c=masked[end];end+=1
   if c=='{':depth+=1
   if c=='}':
    depth-=1
    if depth==0:break
   if c==';' and depth==0:break
  frag=text[m.start():end];clean=re.sub(r'/\*.*?\*/|//[^\n]*','',frag,flags=re.S)
  rows.append(dict(file=filename,name=name,start_line=text[:m.start()].count('\n')+1,end_line=text[:end-1].count('\n')+1,nonblank_lines=sum(bool(x.strip())for x in clean.splitlines())))
(R/'metrics/preservation-root-source-size.json').write_text(json.dumps(dict(status='partial_inventory_not_full_cost',note='These are root declaration sizes only. Builder dependencies, semantic definitions and simulation invariants are not included. Never treat this subtotal as the complete additional public dependency effort.',declarations=rows),indent=2)+'\n')
print(rows)
