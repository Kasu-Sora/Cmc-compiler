#!/usr/bin/env python3
"""Inventory newly required source emitter definitions; source proof support is not target effort."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parent
roots={
 'tvm_model.c':['tvm_opcode_ty','tvm_opcode_code_def','tvm_inst_ty','tvm_inst_op_def','tvm_inst_imm_def'],
 'cmc_rep.c':['cm_rep_ops_def','cm_rep_imms_def'],
 'cmc_concrete_defs.c':['cm_emitter_rep_def','cm_emitter_plan_rep_def'],
 'cmc_codegen.c':['cm_char_normalize_code_def','cm_load_code_def','cm_store_code_def','cm_fp_relative_address_code_def','cm_temp_store_code_def','cm_temp_load_code_def','cm_binary_opcode_def']}
rows=[]
for filename,names in roots.items():
 s=(R/'baseline'/filename).read_text()
 masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S)
 for name in names:
  m=re.search(r'^PROOF\s+\w+\s+'+name+r'\b',masked,re.M);assert m,name
  end=masked.index(';',m.end())+1;t=s[m.start():end]
  rows.append(dict(name=name,file='baseline/'+filename,span=[s[:m.start()].count('\n')+1,s[:end].count('\n')+1],nonblank_lines=sum(bool(x.strip())for x in t.splitlines()),sha256=hashlib.sha256(t.encode()).hexdigest()))
result={'scope':'Newly needed concrete emitter and instruction definitions in source dependency files; existing type/AST/slot/offset models excluded as reused. Dependency proof support is inventoried separately, not folded into case proof or treated as historical migration time.','definition_count':len(rows),'definition_lines':sum(x['nonblank_lines']for x in rows),'declarations':rows,'source_public_proof_roots_used':['cm_rep_ops_append','cm_rep_imms_append','cm_rep_ops_length','cm_char_encode','cm_rep_members_size_matches','get_cm_open_int_fill','get_cm_close_int_fill','get_cm_open_int64_fill','get_cm_close_int64_fill','cm_function_context_fold_hconv'],'source_public_proof_cost_note':'These source library proofs pre-exist and were not edited. Full historical construction effort is unknown; new QCP public definitions and proofs are measured from the final merged library without charging reused imports.'}
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'definitions':len(rows),'lines':result['definition_lines']}))
