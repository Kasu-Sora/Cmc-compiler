"""Collect owner-reported invocation counts without modifying formal artifacts."""
from pathlib import Path
import json,re

R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id']
root=Q/'reports'/run
state=json.loads((root/'controller_state.json').read_text())
keys=['development_calls','development_failed','debug_calls','debug_failed',
      'exact_calls','exact_failed','new_helpers']
rows=[];missing=[]
for attempt in state['attempts'].values():
 if 'groups' not in attempt:continue
 for group_id,group in attempt.get('groups',{}).items():
  if group['status'] not in ['accepted','blocked']:continue
  outputs=list((Path(attempt['report_directory'])/'groups').glob('group_*__'+group_id+'/group_worker_output.md'))
  if len(outputs)!=1:
   missing.append(dict(round=attempt['round'],group=group_id,reason='missing unique output'));continue
  output=outputs[0];found=[]
  for block in re.findall(r'```json\s*\n(.*?)\n```',output.read_text(),re.S):
   try:d=json.loads(block)
   except json.JSONDecodeError:continue
   if isinstance(d,dict) and all(k in d for k in keys):found.append(d)
  if len(found)!=1:
   missing.append(dict(round=attempt['round'],group=group_id,reason='missing unique effort block'));continue
  d=found[0]
  assert all(isinstance(d[k],int) and d[k]>=0 for k in keys)
  assert all(d[k+'_failed']<=d[k+'_calls'] for k in ['development','debug','exact'])
  rows.append(dict(round=attempt['round'],group=group_id,status=group['status'],
                   source=str(output.relative_to(root)),effort=d))
totals={k:sum(row['effort'][k] for row in rows) for k in keys}
result=dict(scope='Owner-reported checks only; main finalization checks counted separately',
            groups=rows,totals=totals,missing=missing)
events=[json.loads(line) for line in (root/'run_logs.json').read_text().splitlines() if line.strip()]
result['controller_group_validations']=[e for e in events if e['event']=='group-attempt-validated']
(R/'metrics/group-effort.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(groups=len(rows),totals=totals,missing=missing),indent=2))
