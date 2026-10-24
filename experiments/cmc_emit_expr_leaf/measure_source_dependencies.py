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
models=['cm_member_offset_slots_def','cm_member_offset_def','cm_strings_prefix_def','cm_string_address_def','cm_const_immediate_def','cm_emit_pair_ty','cm_lcode_of_def','cm_rcode_of_def','cm_emit_lvalue_def','cm_emit_rvalue_def','cm_expr_code_for_def']
new_roots=['cm_rep_type_size_matches','cm_rep_struct_member_prefix_matches','cm_rep_string_address_matches','cm_type_encode_nonnegative']
reused_roots=['cm_rep_members_size_matches','cm_rep_global_size_matches','cm_rep_member_prefix_matches','cm_rep_globals_prefix_matches','cm_char_encode','cm_pointer_encode_threshold']
def closure(roots):
 used=set(roots)
 while True:
  more=set()
  for n in used:
   more |= {x for x in re.findall(r'\b\w+\b',D[n]['text']) if x in D and not x.startswith('get_') and x not in used and x not in models and not x.endswith('_def') and not x.startswith('_')}
  if not more:return used
  used|=more
reused=closure(reused_roots);fresh=closure(new_roots)-reused
rows=[]
for name in models+sorted(fresh):
 d={k:v for k,v in D[name].items()if k!='text'};d['category']='definition' if name in models else 'public_proof_support';rows.append(d)
# Only the four constructor equations used in leaf proofs, not the full recursive expression emitter.
for name,a,b in [('cm_emit_expr_pair.Const',712,716),('cm_emit_expr_pair.String',717,720),('cm_emit_expr_pair.Sizeof',832,836),('cm_emit_expr_pair.Getc',837,840)]:
 t='\n'.join((R/'baseline/cmc_codegen.c').read_text().splitlines()[a-1:b]);rows.append(dict(name=name,file='baseline/cmc_codegen.c',span=[a,b],category='definition_equation_slice',nonblank_lines=sum(bool(l.strip()) for l in t.splitlines()),sha256=hashlib.sha256(t.encode()).hexdigest()))
result=dict(scope='New source size/address/member bridge closure after subtracting previous size/prefix/encoding closure; expression-model support plus four leaf equations only',declarations=rows,definition_count=len(models),leaf_equation_slices=4,definition_lines=sum(x['nonblank_lines']for x in rows if x['category'].startswith('definition')),public_lemma_count=sum(not re.search(r'^PROOF\s+static\b',D[n]['text'])for n in fresh),public_proof_lines=sum(x['nonblank_lines']for x in rows if x['category']=='public_proof_support'),historical_development_seconds=None,reused_public_roots=reused_roots,new_public_roots=new_roots,reused_proof_closure=sorted(reused),note='Selected source proof graph excludes definition getters/export scaffolding and previously migrated source closure. Leaf model counts exact four selected emitter equations plus selectors; full recursive emitter is not counted as migrated.')
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k not in ['declarations','reused_proof_closure']});print('New proofs:',sorted(fresh))
