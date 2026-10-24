"""Generate theorem-signature/assumption audit, cost ledger, and source links.
Counts current public support only; never declares cmc_compile complete.
"""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parent;E=R.parent
sys.path.insert(0,str(E.parent/'cmc_compile_readiness'))
from audit_syntax import coq_commands,coq_mask,line_span
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=sorted((R/'target').glob('*_lib.v'));rows=[];audit=[];checks=json.loads((R/'metrics/checks.json').read_text())
source_paths=list((E/'baseline/cstar_project').glob('*.c'));source={}
for p in source_paths:
 s=p.read_text();masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S)
 clean=re.sub(r'/\*.*?\*/|//[^\n]*',lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S).splitlines()
 for m in re.finditer(r'^PROOF\s+(?:static\s+|extern\s+)?\w+\s+(\w+)\b',masked,re.M):
  d=re.search(r'[;{]',masked[m.end():]);at=m.end()+d.start();end=at+1
  if masked[at]=='{':
   depth=1
   while depth:depth+=(masked[end]=='{')-(masked[end]=='}');end+=1
  text=s[m.start():end];a,b=line_span(s,m.start(),end)
  source.setdefault(m.group(1),[]).append(dict(file=p.name,span=[a,b],nonblank_lines=sum(bool(l.strip())for l in clean[a-1:b]),text=text,sha256=sha(p)))
for p in files:
 s=p.read_text();masked=coq_mask(s);commands=coq_commands(s);decls=[];pending=None;proven=[]
 assert not re.search(r'\b(Axiom|Axioms|Parameter|Parameters|Admitted|admit|Abort)\b',masked),p
 for a,b,cmd in commands:
  m=re.match(r'(\w+)\s+(\w+)',cmd);kind=m.group(1)if m else cmd.strip('. ');name=m.group(2)if m else None
  if pending:
   if kind in ('Qed','Defined'):
    pending['end']=b;pending['ending']=kind;decls.append(pending);pending=None
   elif kind=='Proof':pending['proof_start']=a
  elif kind in ('Lemma','Theorem','Corollary','Fact','Proposition','Remark') or (kind=='Definition' and ':='not in cmd):
   pending=dict(kind=kind,name=name,start=a,statement_end=b)
  elif kind in ('Definition','Fixpoint','Inductive','Record','Ltac'):
   decls.append(dict(kind=kind,name=name,start=a,end=b))
 assert pending is None
 counts=dict(definitions=0,lemmas=0,definition_lines=0,lemma_lines=0,decision_proof_lines=0,automation_declarations=0,automation_lines=0)
 for d in decls:
  d['span']=line_span(s,d['start'],d['end']);d['nonblank_lines']=sum(bool(l.strip())for l in masked[d['start']:d['end']].splitlines())
  islemma=d['kind'] in ('Lemma','Theorem','Corollary','Fact','Proposition','Remark')
  if d['kind']=='Ltac':counts['automation_declarations']+=1;counts['automation_lines']+=d['nonblank_lines']
  elif islemma:counts['lemmas']+=1;counts['lemma_lines']+=d['nonblank_lines']
  else:
   counts['definitions']+=1
   if 'proof_start'in d:
    cost=sum(bool(l.strip())for l in masked[d['proof_start']:d['end']].splitlines());counts['decision_proof_lines']+=cost;counts['definition_lines']+=d['nonblank_lines']-cost
   else:counts['definition_lines']+=d['nonblank_lines']
  if 'ending'in d:proven.append(d['name'])
  candidates=source.get(d['name']+('_def'if not islemma else ''),[])
  if not candidates and d['kind']in('Inductive','Record'):
   candidates=[x for vs in source.values()for x in vs if re.search(r'new_datatype_definition\(\s*"'+re.escape(d['name'])+r'\s*=',x['text'])]
  d['source_declarations']=[{k:v for k,v in x.items()if k!='text'}for x in candidates]
  for key in ('start','end','statement_end','proof_start'):d.pop(key,None)
 counts['proof_lines']=counts['lemma_lines']+counts['decision_proof_lines']+counts['automation_lines']
 latest=next((x for x in reversed(checks)if x['module']==p.stem and x['mode']=='development'),None)
 assert latest and latest['exit_code']==0 and latest['sha256']==sha(p),(p,latest)
 rows.append(dict(file=str(p),sha256=sha(p),counts=counts,declarations=decls,compiled=True,used_by_top_level_case=False))
 audit.append('Require Import SimpleC.EE.QCP_demos_human.'+p.stem+'.')
 for name in proven:
  q=p.stem+'.'+name
  audit += [f'Goal True. idtac "AUDIT {q}". exact I. Qed.',f'Check {q}.',f'Print Assumptions {q}.']
(R/'target/TransportAudit.v').write_text('\n'.join(audit)+'\n')
totals={k:sum(x['counts'][k]for x in rows)for k in rows[0]['counts']}
result=dict(status='compiled_public_support_only',top_level_verified=False,modules=rows,totals=totals,
 expected_assumption_audits=sum('ending'in d for x in rows for d in x['declarations']),
 counting_note='Nonblank non-comment physical lines. Definitions/datatype/record declarations separate; lemma lines include statement and Proof/Qed; constructive equality decision proof bodies and Ltac automation counted separately and included in proof_lines. Generated audit and tooling excluded. All helpers counted, including currently unused ones. Source links are matched declarations, NOT the completed preservation dependency closure.',
 final_source_dependency_proof_cost=None,final_top_level_cost=None,source_historical_development_time=None,human_active_time=None,
 tool_seconds=sum(x['seconds']for x in checks),development_attempts=len([x for x in checks if x['mode']=='development' and x['module'].endswith('_lib')]),development_failures=len([x for x in checks if x['mode']=='development' and x['module'].endswith('_lib') and x['exit_code']]))
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(totals=totals,modules=len(rows),assumption_checks=result['expected_assumption_audits'])))
