#!/usr/bin/env python3
"""Freeze identities of manually reviewed contracts; not a semantic decision procedure."""
from pathlib import Path
import json,hashlib,re
from audit_syntax import c_functions
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
s=(Q/'QCP_examples/QCP_demos_human/cmc_counts_migration.c').read_text()
audit=json.loads((R/'metrics/model-review.json').read_text())
source={x['function']:x for x in json.loads((R/'metrics/source-contracts.json').read_text())}
specific={
 'cmc_expr_type_code_value':'Restore expression ownership; return encoded node type through int cell, without extra type validity assumption.',
 'cm_expr_lvalue_count':'Preserve original heap contexts, wf, equality to total function lookup, representability and i32 lcount result.',
 'cm_expr_rvalue_count':'Preserve original heap contexts, wf, equality to total function lookup, representability and i32 rcount result.',
 'cmc_args_code_count':'Preserve slots/args wf and arity relation; writable output becomes exact args count and is i32.',
 'cm_binding_address_count_value':'All runtime signed scopes allowed; zero maps to one, all other values to four.',
 'cm_expr_counts':'Preserve both output cells and additional postcondition type-wf/encoded-type-i32 facts.',
 'cmc_stmt_code_count':'Preserve universally quantified loop flag and return-type field ownership.',
 'cmc_param_stores_count':'Only param representability and slot-list ownership required; returns i32 count.',
 'cmc_function_prologue_count':'Preserve function-context ownership and original count bounds.',
 'cmc_function_code_count':'Function lookup equality remains inside counts-representable; preserve stmt-wf false and exact owned header/body.',
 'cmc_function_prefix_count':'Preserve index = full length - suffix length, remaining <= suffix length, index+remaining bound and i32(11+prefix).',
 'cmc_function_pc':'Preserve inclusive fid <= function-list length, including end-of-program boundary.',
 'cmc_functions_code_size_count':'Preserve suffix/full-list index relationship, index+suffix-length bound and recursive representability.',
 'cmc_model_code_length':'No added list-length precondition; use original wf and struct-safety with whole function-list ownership.',
 'cmc_model_data_length':'The model/representation size equality is an ORIGINAL explicit precondition and remains so, alongside global/string safety.'}
rows=[]
for f in c_functions(s):
 if f['prototype']:continue
 n=f['name'];t='\n'.join(re.findall(r'/\*@.*?\*/',s[f['start']:f['body_start']],re.S))
 rows.append({'function':n,'source_contract_sha256':hashlib.sha256(source[n]['contract'].encode()).hexdigest(),'target_contract_sha256':hashlib.sha256(t.encode()).hexdigest(),'checks':['Same runtime parameters/result','Same pure pre/post facts under documented translation','Same separated heap ownership restored in postcondition',specific[n]],'adaptation':'HOL fact(P) -> QCP pure P; total function lookup uses policy; codegen fields use universally quantified record.'})
assert len(rows)==len(source)==15
audit['contracts']=rows
audit['status']='contracts/models reviewed; QCP final verification pending'
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n')
print(len(rows))
