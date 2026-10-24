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
models=['cm_slots_prefix_def','cm_globals_prefix_def','cm_global_address_def','cm_param_offset_def','cm_local_offset_def','cm_binding_address_code_def','cm_push_code_def']
proofs=['cm_rep_member_prefix_matches','cm_prove_rep_member_prefix_matches','cm_rep_globals_prefix_matches','cm_prove_rep_globals_prefix_matches','cm_globals_wf_head','cm_prove_globals_wf_head','cm_globals_wf_tail','cm_prove_globals_wf_tail']
rows=[]
for name in models+proofs:
 d={k:v for k,v in D[name].items()if k!='text'};d['category']='definition' if name in models else 'public_proof_support';rows.append(d)
result=dict(scope='Incremental source AST dependency definitions and prefix proof closure; previously used slot size/slots head-tail and global size proofs excluded',declarations=rows,definition_count=len(models),definition_lines=sum(x['nonblank_lines']for x in rows if x['category']=='definition'),public_lemma_count=4,public_proof_lines=sum(x['nonblank_lines']for x in rows if x['category']=='public_proof_support'),historical_development_seconds=None,note='Two prefix lemmas plus global list head/tail wf lemmas and their private proof constructors counted once. Existing cm_slots_wf_head/tail and size bridge closure were already needed in emit-core; cm_rep_global_size_matches in emit-globals. Context, opcode, binding nonnegativity and plan open/close reused.')
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='declarations'})
