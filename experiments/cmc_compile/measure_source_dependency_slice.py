"""Conservative, reproducible declaration slice; not a minimal theorem-use trace."""
from pathlib import Path
from collections import defaultdict
import re,json,hashlib
R=Path(__file__).resolve().parent; S=R/'baseline/cstar_project'
D={};public=defaultdict(list);local={}
def strip_comments(t):
 return re.sub(r'/\*.*?\*/|//[^\n]*',lambda m:re.sub(r'[^\n]',' ',m.group()),t,flags=re.S)
def mask(t):
 return re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),t,flags=re.S)
for p in sorted(S.glob('*.c')):
 text=p.read_text();mtext=mask(text)
 for m in re.finditer(r'^PROOF\s+(?:(static|extern)\s+)?\w+\s+(\w+)\b',mtext,re.M):
  tail=re.search('[;{]',mtext[m.end():]);assert tail
  at=m.end()+tail.start();end=at+1
  if mtext[at]=='{':
   depth=1
   while depth:depth+=(mtext[end]=='{')-(mtext[end]=='}');end+=1
  elif '=' not in mtext[m.start():end]:continue # declaration only
  frag=text[m.start():end];name=m[2];key=p.name+'::'+name
  kind='definition' if re.search(r'new_(?:fun|rec|datatype)_definition',frag) else 'framework_scaffolding' if name.startswith('get_') or 'cst_add_const_to_header' in frag or 'axioms_before' in name or 'get_all_axioms' in frag else 'proof'
  D[key]=dict(file=p.name,name=name,span=[text[:m.start()].count('\n')+1,text[:end-1].count('\n')+1],nonblank_lines=sum(bool(l.strip())for l in strip_comments(frag).splitlines()),category=kind,sha256=hashlib.sha256(frag.encode()).hexdigest(),text=frag)
  local[(p.name,name)]=key
  if m[1]!='static':public[name].append(key)
assert all(len(v)==1 for v in public.values()),{k:v for k,v in public.items()if len(v)>1}
public={k:v[0]for k,v in public.items()}
def refs(text,file):
 words=set(re.findall(r'\b\w+\b',strip_comments(text)))
 words|={w[4:]for w in words if w.startswith('get_')}
 words|={w+'_def'for w in words if w+'_def'in public or(file,w+'_def')in local}
 return {local.get((file,w),public.get(w))for w in words}-{None}
def closure(roots):
 seen=set();todo=set(roots)
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k);todo|=refs(D[k]['text'],D[k]['file'])-seen
 return seen
units=['cmc_concrete_emit_bytes.c','cmc_concrete_copy_bytes.c','cmc_concrete_emit_word.c','cmc_concrete_emit_char.c','cmc_concrete_layout.c','cmc_concrete_counts.c','cmc_concrete_count_context.c','cmc_concrete_function_pc_total.c','cmc_concrete_emit_globals.c','cmc_concrete_emit_strings.c','cmc_concrete_emit_data.c','cmc_concrete_emit_core.c','cmc_concrete_emit_resolved.c','cmc_concrete_emit_plan.c','cmc_concrete_emit_ast.c','cmc_concrete_emit_expr_leaf.c','cmc_concrete_emit_expr_var.c','cmc_concrete_emit_expr_dispatch.c','cmc_concrete_emit_expr_simple.c','cmc_concrete_emit_expr_call.c','cmc_concrete_emit_binary_finish.c','cmc_concrete_emit_expr.c','cmc_concrete_emit_zeroes.c','cmc_concrete_emit_return.c','cmc_concrete_emit_stmt.c','cmc_concrete_emit_function.c','cmc_concrete_emit_functions.c','cmc_concrete_emit_prelude.c','cmc_concrete_emit_code.c','cmc_concrete_patch_calls.c','cmc_concrete_data_ready.c','cmc_concrete_program_ready.c','cmc_concrete_code_ready.c','cmc_concrete_temp_ready.c','cmc_concrete_function_ready.c','cmc_concrete_compile_ready.c']
prior=set()
for name in units:
 assert(S/name).exists(),name
 prior|=closure(refs((S/name).read_text(),name))
roots=refs((S/'cmc.c').read_text(),'cmc.c');current=closure(roots)
assert 'cmc_correct.c::cmc_preservation' in current
assert 'cmc_preservation_total_iter.c::cm_preservation_iter' in current
assert 'cmc_preservation_total_step.c::cm_preservation_step' in current
new={k for k in current-prior if D[k]['file']!='cmc.c' and D[k]['category']!='framework_scaffolding'}
rows=[{k:v for k,v in D[n].items()if k!='text'}for n in sorted(new)]
result=dict(status='conservative_lexical_slice_not_minimal_dependency_cost',method='Resolve PROOF declarations by translation-unit static scope, then public scope. Follow lexical identifiers, get_ references and HOL constant -> _def references to a fixed point. Subtract complete slices of the 30 prior concrete units and six readiness units. Exclude top cmc.c (already measured), external framework code and getter/export scaffolding.',limitations=['Includes quoted identifiers and unused local helpers if lexically referenced; this is not an execution trace of proof construction.','Generated datatype/interface declarations and generic HOL framework support are not a complete historical implementation cost.','No source-to-target dependency ratio is inferred from this conservative slice.'],prior_units=units,root_declarations=sorted(roots),new_declarations=rows,reused_declarations=sorted(current&prior),totals=dict(definitions=sum(x['category']=='definition'for x in rows),definition_lines=sum(x['nonblank_lines']for x in rows if x['category']=='definition'),proof_declarations=sum(x['category']=='proof'for x in rows),proof_lines=sum(x['nonblank_lines']for x in rows if x['category']=='proof')),minimal_source_dependency_cost=None,source_to_target_dependency_ratio=None,source_manifest_sha256=hashlib.sha256((R/'baseline/source-manifest.json').read_bytes()).hexdigest())
(R/'metrics/source-dependency-slice.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['totals']))
