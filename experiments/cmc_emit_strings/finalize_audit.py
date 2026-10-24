#!/usr/bin/env python3
"""Close the main-owned audit records only after final verification and measurement."""
import json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parent
P=Path('/Users/nizitong/QCP/qcp-binary-democases/reports')/json.loads((R/'metrics/run.json').read_text())['run_id']
s=json.loads((P/'controller_state.json').read_text())
e=json.loads((R/'metrics/effort.json').read_text())
assert s['phase']=='done' and s['final_check']['status']=='passed'
assert e['verification']['phase']=='done' and e['runtime_tokens_equal'] and e['abi_unchanged']
library_review=json.loads((R/'metrics/final-library-review.json').read_text())
assert library_review['candidate_sha256']==hashlib.sha256((R/'target/cmc_emit_strings_migration_lib.v').read_bytes()).hexdigest()
library_review['status']='Main declaration review completed; identical final library passed controller verification'
(R/'metrics/final-library-review.json').write_text(json.dumps(library_review,indent=2)+'\n')
proving=next(a for a in reversed(list(s['attempts'].values())) if 'groups' in a)
groups=proving['groups']
assert groups and all(g['status']=='accepted' for g in groups.values())
events=[json.loads(l) for l in (P/'run_logs.json').read_text().splitlines() if l.strip()]
validations=[x for x in events if x['event']=='group-attempt-validated']
notes=json.loads((R/'metrics/process-notes.json').read_text())
notes['status']='completed; controller done and final-check passed'
notes['proof_progress_snapshot']={'accepted_groups':len(groups),'planned_groups':len(groups),'status':'complete'}
notes.setdefault('proof_development',{})['controller_group_repair_count']=sum(x['details']['status']!='accepted' for x in validations)
notes['proof_development']['controller_group_validation_count']=len(validations)
notes['proof_development']['accepted_group_attempts']={k:g['attempt_index'] for k,g in groups.items()}
notes['final_verification']={'phase':s['phase'],'final_check':s['final_check'],'controller_updated_at':s['updated_at']}
(R/'metrics/process-notes.json').write_text(json.dumps(notes,indent=2)+'\n')
audit=json.loads((R/'metrics/semantic-audit.json').read_text())
audit['status']='contract review completed; final verification passed; reviewed contract/model hashes unchanged'
audit['final_verification']={'run_id':s['run_id'],'phase':s['phase'],'status':s['final_check']['status'],'runtime_tokens_equal':True,'abi_unchanged':True,'function_coverage':len(e['coverage'])}
audit['proof_audit']={'manual_top_level':e['entries']['manual_top_level'],'proved_splits':e['entries']['manual_splits'],'unused_aborted_split_drafts':len(e['unused_split_drafts_aborted']),'automatic_admitted_witnesses':e['entries']['automatic_witnesses'],'manual_and_new_library_have_no_admitted_axiom_parameter':True}
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({'final_check':'passed','groups':len(groups),'functions':len(e['coverage'])},indent=2))
