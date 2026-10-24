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
models=[]
new_roots=['cm_binding_array_code_zero','cm_binding_array_code_nonzero','cm_select_code_plan_st','cm_restore_code_plan_st']
reused_models=['cm_binding_array_def','cm_binding_array_code_def','cm_emit_pair_ty','cm_lcode_of_def','cm_rcode_of_def','cm_emit_lvalue_def','cm_emit_rvalue_def','cm_expr_code_for_def']
proof_names=['cm_binding_array_code_zero','cm_binding_array_code_nonzero','cm_prove_binding_array_code_zero','cm_prove_binding_array_code_nonzero','cm_select_code_plan_st','cm_restore_code_plan_st']
rows=[]
for name in proof_names:
 d={k:v for k,v in D[name].items() if k!='text'};d['category']='public_proof_support';rows.append(d)
a,b=721,728
t='\n'.join((R/'baseline/cmc_codegen.c').read_text().splitlines()[a-1:b]);assert 'CMVarE' in t and 'then [] else cm_load_code ty' in t
rows.append(dict(name='cm_emit_expr_pair.Var',file='baseline/cmc_codegen.c',span=[a,b],category='definition_equation_slice',nonblank_lines=sum(bool(l.strip())for l in t.splitlines()),sha256=hashlib.sha256(t.encode()).hexdigest()))
result=dict(scope='Incremental variable equation, array-code zero/nonzero proof and plan-selection state tactics; inherited layout/AST/leaf selector closure excluded',declarations=rows,definition_count=0,leaf_equation_slices=1,equation_slices=1,definition_lines=sum(x['nonblank_lines']for x in rows if x['category'].startswith('definition')),public_lemma_count=2,public_state_tactic_count=2,public_proof_lines=sum(x['nonblank_lines']for x in rows if x['category']=='public_proof_support'),historical_development_seconds=None,new_public_roots=new_roots,reused_models=reused_models,reused_public_roots=['cm_nonnegative_i32_cast','program/function/expression context open-close helpers','existing AST and plan implementation proofs'],note='Source delta only: prior leaf selectors already counted; binding-array semantics and integer encoding already represented in layout/counts. Two theorem constructors plus exports and two state tactics counted once. Complete recursive emitter not claimed. leaf_equation_slices is a legacy metric key for equation-slice count; actual constructor is Var.')
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='declarations'})
