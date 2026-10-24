from pathlib import Path
import re,json
R=Path(__file__).resolve().parent;S=R.parent/'baseline/cstar_project/tvm_model.c'
s=S.read_text();quote=re.search(r'PROOF thm tvm_inst_step_def = new_rec_definition\(\s*tvm_opcode_RECURSION,\s*`(.*?)`\);',s,re.S).group(1)
clauses=re.split(r'(?=\(!code imm st\.)',quote);rows=[]
for clause in clauses:
 if not clause.strip():continue
 op=re.search(r'tvm_inst_step .*? (TVM\w+Op) ',clause,re.S).group(1)
 body=clause.split('=\n',1)[1].strip();body=re.sub(r'\s*&&\s*$','',body);assert body.endswith(')');body=body[:-1].strip()
 original=body
 replacements={
  'ilength (tvm_stack st) < 65536i':'(Zlength (tvm_stack st) <? 65536)',
  'ilength (tvm_calls st) < 65536i':'(Zlength (tvm_calls st) <? 65536)',
  '1i <= ilength (tvm_stack st)':'(1 <=? Zlength (tvm_stack st))',
  '2i <= ilength (tvm_stack st)':'(2 <=? Zlength (tvm_stack st))',
  '1i <= ilength (tvm_calls st)':'(1 <=? Zlength (tvm_calls st))',
  'tvm_target_valid code imm':'tvm_target_validb code imm',
  'tower_word_valid':'tower_word_validb','tower_addr_valid':'tower_addr_validb','tower_byte_value':'tower_byte_valueb',
  'tvm_input st == []':'list_empty (tvm_input st)',
  'HD (tvm_stack st) == 0i':'(HD (tvm_stack st) =? 0)',
  'HD (TL (tvm_stack st)) == HD (tvm_stack st)':'(HD (TL (tvm_stack st)) =? HD (tvm_stack st))',
  'HD (TL (tvm_stack st)) <= HD (tvm_stack st)':'(HD (TL (tvm_stack st)) <=? HD (tvm_stack st))',
  'HD (TL (tvm_stack st)) < HD (tvm_stack st)':'(HD (TL (tvm_stack st)) <? HD (tvm_stack st))',
  'HD (tvm_stack st) <= HD (TL (tvm_stack st))':'(HD (tvm_stack st) <=? HD (TL (tvm_stack st)))',
  'HD (tvm_stack st) < HD (TL (tvm_stack st))':'(HD (tvm_stack st) <? HD (TL (tvm_stack st)))'
 }
 for a,b in replacements.items():body=body.replace(a,b)
 body=re.sub(r'\bHD\b','hd 0',body);body=re.sub(r'\bTL\b','tl',body)
 body=re.sub(r'\b(\d+)i\b',r'\1',body).replace('--','-').replace('~(','negb (')
 assert '==' not in body and 'ilength' not in body and ':tvm' not in body
 rows.append(dict(opcode=op,source_body=original,target_body=body))
assert len(rows)==28
(R/'metrics/tvm-instruction-equations.json').write_text(json.dumps(rows,indent=2)+'\n')
(R/'target/tvm_instruction_branches.inc').write_text('\n'.join(' | '+r['opcode']+' => '+r['target_body'] for r in rows)+'\n')
