from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parent
# Parse C* PROOF declarations including function and constant bodies.
D={}
for filename in ['cmc_lang.c','cmc_codegen.c','cmc_concrete_defs.c']:
 text=(R/'baseline'/filename).read_text()
 masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),text,flags=re.S)
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
  fragment=text[m.start():at];a=text[:m.start()].count('\n')+1;b=text[:at-1].count('\n')+1
  D[m.group(1)]=dict(name=m.group(1),file='baseline/'+filename,span=[a,b],nonblank_lines=sum(bool(x.strip())for x in fragment.splitlines()),sha256=hashlib.sha256(fragment.encode()).hexdigest(),text=fragment)
rows=[]
d={k:v for k,v in D['cm_leaf_expr_def'].items() if k!='text'};d['category']='definition';rows.append(d)
result=dict(scope='Incremental source leaf-kind predicate only; all four leaf code equations, selectors, shape/count facts and helper implementations reused',declarations=rows,definition_count=1,equation_slices=0,definition_lines=sum(x['nonblank_lines']for x in rows),public_lemma_count=0,public_state_tactic_count=0,public_proof_lines=0,historical_development_seconds=None,new_public_roots=[],reused_models=['cm_emit_expr_pair.Const/String/Getc/Sizeof','cm_expr_code_for_def','cm_expr_wf_def','cm_expr_counts_representable_def'],reused_public_roots=['cm_open_expr_count_facts and count fact helpers (counts)','cm_expr_const/string/sizeof/getc_shape_ent (layout/counts)','cm_open_expr_rep_st/cm_close_expr_rep_st','four verified leaf implementation proofs'],note='New source predicate has four kind alternatives. Generic expression count/shape support was already needed by counts; no duplicate incremental charge. Full recursive emitter is not claimed.')
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='declarations'})
