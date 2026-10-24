"""Incremental source support closure, subtracting actual prior source dependencies."""
from pathlib import Path
import json,re,hashlib,shutil
R=Path(__file__).resolve().parent;D={}
files=['cmc_lang.c','cmc_codegen.c','cmc_concrete_defs.c','cmc_temp_algebra.c','cmc_concrete_layout.c','cmc_rep.c','cmc_concrete_emit_stmt_proof.c','cmc_concrete_counts.c','cmc_stack_local_syntax.c']
for filename in files:
 p=R/'baseline'/filename
 if not p.exists():shutil.copy2(R/'baseline/cstar_project'/filename,p)
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
  kind='model' if re.search(r'new_(?:fun|rec|datatype)_definition',frag) else 'export' if 'cst_add_const_to_header' in frag else 'proof'
  clean_frag=re.sub(r'/\*.*?\*/|//[^\n]*',lambda x:re.sub(r'[^\n]',' ',x.group()),frag,flags=re.S)
  D[m.group(1)]=dict(name=m.group(1),file='baseline/'+filename,span=[text[:m.start()].count('\n')+1,text[:at-1].count('\n')+1],nonblank_lines=sum(bool(x.strip())for x in clean_frag.splitlines()),sha256=hashlib.sha256(frag.encode()).hexdigest(),text=frag,kind=kind)
def refs(s):
 words=set(re.findall(r'\b\w+\b',s));return (words|{n[4:] for n in words if n.startswith('get_')})&D.keys()
def closure(roots):
 seen=set();todo=set(roots)
 while todo:
  n=todo.pop()
  if n in seen:continue
  if D[n]['kind']!='proof' or n.startswith('get_'):continue
  seen.add(n);todo|=refs(D[n]['text'])-seen
 return seen
source=(R/'baseline/cmc_concrete_temp_ready.c').read_text();local_names=set(re.findall(r'^PROOF\s+(?:static\s+)?\w+\s+(\w+)',source,re.M));current=closure(refs(source)-local_names);prior=set();prior_units=[]
# Complete source units whose target runtime bodies already passed; do not include headers or arbitrary shared source snapshots.
units=['cmc_concrete_emit_bytes.c','cmc_concrete_copy_bytes.c','cmc_concrete_emit_word.c','cmc_concrete_emit_char.c','cmc_concrete_layout.c','cmc_concrete_counts.c','cmc_concrete_count_context.c','cmc_concrete_function_pc_total.c','cmc_concrete_emit_globals.c','cmc_concrete_emit_strings.c','cmc_concrete_emit_data.c','cmc_concrete_emit_core.c','cmc_concrete_emit_resolved.c','cmc_concrete_emit_plan.c','cmc_concrete_emit_ast.c','cmc_concrete_emit_expr_leaf.c','cmc_concrete_emit_expr_var.c','cmc_concrete_emit_expr_dispatch.c','cmc_concrete_emit_expr_simple.c','cmc_concrete_emit_expr_call.c','cmc_concrete_emit_binary_finish.c','cmc_concrete_emit_expr.c','cmc_concrete_emit_zeroes.c','cmc_concrete_emit_return.c','cmc_concrete_emit_stmt.c','cmc_concrete_emit_function.c','cmc_concrete_emit_functions.c','cmc_concrete_emit_prelude.c','cmc_concrete_emit_code.c','cmc_concrete_patch_calls.c','cmc_concrete_data_ready.c','cmc_concrete_program_ready.c','cmc_concrete_code_ready.c']
for name in units:
 p=R/'baseline/cstar_project'/name
 assert p.exists(),name
 prior_text=p.read_text()
 # A prior file's private function is not the same shared declaration merely
 # because its C identifier matches (expr has a private rvalue-length helper).
 private_names=set(re.findall(r'^PROOF\s+static\s+\w+\s+(\w+)',prior_text,re.M))
 shadowed={n for n in private_names if n in D and D[n]['file']!='baseline/'+name}
 prior|=closure(refs(prior_text)-shadowed);prior_units.append(name)
# Model definitions are measured separately by measure_source.py.
new_defs=[]
new_proofs=sorted(current-prior)
rows=[]
for name in new_defs+new_proofs:
 d={k:v for k,v in D[name].items() if k not in ['text','kind']};d['category']='definition' if name in new_defs else 'public_proof_closure';rows.append(d)
result=dict(scope='Temp readiness source proof dependencies; subtract 30 runtime and 3 pure support source unit closures',declarations=rows,definition_count=sum(x['category']=='definition' for x in rows),equation_slices=0,definition_lines=sum(x['nonblank_lines']for x in rows if x['category']=='definition'),public_proof_lines=sum(x['nonblank_lines']for x in rows if x['category']=='public_proof_closure'),new_public_roots=sorted((refs(source)&set(new_proofs))),prior_source_units=prior_units,reused_public_declarations=sorted(current&prior),historical_development_seconds=None,note='Source size, not historical effort. Includes new proof builders/constants once; excludes previous full-unit proof closures, existing general code model, framework getters/exports and same-file private support. Same-file support is counted in source module proof; no definition is double counted here. Existing stmt_proof.c support is reused. Existing counts helpers are subtracted using prior full-unit closures.')
result['support_file_summary']={f:dict(declarations=[d['name'] for d in rows if d['file']==f and d['category']=='public_proof_closure'],nonblank_lines=sum(d['nonblank_lines'] for d in rows if d['file']==f and d['category']=='public_proof_closure'))for f in sorted({d['file']for d in rows if d['category']=='public_proof_closure'})}
result['private_name_collision_note']='Source static names are resolved within each prior unit; stmt proof support is already covered by the previous stmt migration.'
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['declarations','prior_source_units','reused_public_declarations']},indent=2))
print([(x['name'],x['nonblank_lines']) for x in rows])
