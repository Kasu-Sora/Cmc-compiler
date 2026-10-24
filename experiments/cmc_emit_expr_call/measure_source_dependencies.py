"""Incremental mathematical source closure; excludes previously charged models."""
from pathlib import Path
import json,re,hashlib,shutil
R=Path(__file__).resolve().parent
D={}
for filename in ['cmc_lang.c','cmc_codegen.c','cmc_concrete_defs.c','cmc_temp_algebra.c']:
 p=R/'baseline'/filename
 if not p.exists():shutil.copy2(Path('/Users/nizitong/cmc')/filename,p)
 text=p.read_text();masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),text,flags=re.S)
 for m in re.finditer(r'^PROOF\s+(?:static\s+|extern\s+)?\w+\s+(\w+)\b',masked,re.M):
  at=m.end();depth=0
  while at<len(masked):
   c=masked[at]
   if c=='{':depth+=1
   if c=='}':
    depth-=1
    if depth==0:at+=1;break
   if c==';' and depth==0:at+=1;break
   at+=1
  frag=text[m.start():at]
  D[m.group(1)]=dict(name=m.group(1),file='baseline/'+filename,span=[text[:m.start()].count('\n')+1,text[:at-1].count('\n')+1],nonblank_lines=sum(bool(x.strip())for x in frag.splitlines()),sha256=hashlib.sha256(frag.encode()).hexdigest(),text=frag)
new_defs=['cm_pointer_scale_def','cm_binary_finish_code_def','cm_emit_args_reload_def','cm_expr_temps_for_def']
roots=['cm_expr_code_lengths','cm_expr_temps_nonnegative','cm_args_count_matches_length','cm_imax_left_bound','cm_imax_right_bound','cm_temp_offset_mono','cm_add_temp_offset_bound_st']
# Follow proof constructors and theorem constants, but not already-existing mathematical definitions/getters.
proofs=set(roots)
while True:
 more=set()
 for n in proofs:
  for name in set(re.findall(r'\b\w+\b',D[n]['text']))&D.keys():
   d=D[name]
   if name.startswith('get_') or re.search(r'new_(?:fun|rec|datatype)_definition',d['text']) or 'cst_add_const_to_header' in d['text']:continue
   if d['file'] in ['baseline/cmc_codegen.c','baseline/cmc_temp_algebra.c'] or name in ['cm_prove_temp_offset_mono']:more.add(name)
 more-=proofs
 if not more:break
 proofs|=more
rows=[]
for name in new_defs+sorted(proofs):
 d={k:v for k,v in D[name].items()if k!='text'};d['category']='definition' if name in new_defs else 'public_proof_closure';rows.append(d)
# Previously migrated leaf and var equations are subtracted from the mutual source definition.
text=(R/'baseline/cmc_codegen.c').read_text();lines=text.splitlines()
for name,a,b in [('Assign',729,742),('Binary',743,768),('Unary',769,783),('Index',784,807),('Member',808,823),('Call',824,831),('Putc',841,846),('Puti',847,852),('Exit',853,859),('ArgsNil',860,862),('ArgsCons',863,871)]:
 frag='\n'.join(lines[a-1:b]);rows.append(dict(name='cm_emit_expr_pair.'+name,file='baseline/cmc_codegen.c',span=[a,b],nonblank_lines=sum(bool(x.strip())for x in frag.splitlines()),sha256=hashlib.sha256(frag.encode()).hexdigest(),category='definition_equation'))
result=dict(scope='New general-expression equations, argument code and temporary/code-length proof closure; prior leaf/var equations and primitives excluded',declarations=rows,definition_count=len(new_defs),equation_slices=11,definition_lines=sum(x['nonblank_lines']for x in rows if x['category'].startswith('definition')),public_proof_lines=sum(x['nonblank_lines']for x in rows if x['category']=='public_proof_closure'),new_public_roots=roots,historical_development_seconds=None,reused_models=['cm_emit_pair and projections','cm_emit_expr_pair.Const/String/Var/Sizeof/Getc','cm_emit_lvalue/rvalue and cm_expr_code_for selectors','core instructions/temp code/binary opcode','count/wf/typing/AST representation'],note='Same-file private support counted separately in source-effort.json. Shared closure counts builders/constants once, not old helper implementations. Source proof root count is not a cross-system VC count.')
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='declarations'},indent=2))
