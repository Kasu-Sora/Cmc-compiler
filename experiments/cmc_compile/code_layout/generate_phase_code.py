"""Translate finite code-layout tables; retain each source/target clause for review.
Parsing does not establish any proof. coqc and later coqchk are required.
"""
from pathlib import Path
import re,json,hashlib
import equation_parser as P
R=Path(__file__).resolve().parent;S=R.parent/'baseline/cstar_project/cmc_preservation_code.c';source=S.read_text()
P.source_params={'cm_init_tail_code','cm_return_tail_code','cm_value_phase_code','cm_normal_phase_code'}
P.policy_params.update({'cm_emit_rvalue','cm_emit_lvalue','cm_emit_stmt','cm_emit_args_store'})
out=['Require Export SimpleC.EE.QCP_demos_human.cmc_type_invariant_migration_lib.','From Coq Require Import ZArith List Bool Lia.','Import ListNotations.','Local Open Scope Z_scope.'];out += ['Definition cm_emit_rvalue policy p fid pc temp expr := cm_expr_code_for policy p fid pc temp expr 0.', 'Definition cm_emit_lvalue policy p fid pc temp expr := cm_expr_code_for policy p fid pc temp expr 1.'];rows=[]
for name in ['cm_value_phase_code','cm_phase_stops','cm_phase_yields_normal','cm_normal_phase_code','cm_normal_phase_stops']:
 formula=re.search(r'PROOF thm '+name+r'_def\b.*?`(.*?)`',source,re.S)[1]
 params='(sp:cm_source_lookup_policy) (p:cm_program) (fid pc temp owner breakpc continuepc:Z) ' if name.endswith('_code') else ''
 out.append(f'Definition {name} {params}(phase:cm_aphase) := match phase with')
 for orig in P.clauses(formula):
  cl=re.sub(r'^!.*?\.\s*','',orig[1:-1],flags=re.S);cl=P.striptypes(cl);lhs,rhs=re.split(r'\s=\s',cl,maxsplit=1)
  f,args=P.flat(P.Parser(lhs).all());assert f[1]==name
  pat=P.emit(args[-1],True);body=P.emit(P.Parser(rhs).all())
  out.append(' | '+pat+' => '+body);rows.append(dict(definition=name,source_clause=orig,target_pattern=pat,target_body=body))
 out.append('end.\n')
(R/'target/cmc_code_phase_migration_lib.v').write_text('\n'.join(out)+'\n')
(R/'metrics/phase-equations.json').write_text(json.dumps(dict(source=str(S),sha256=hashlib.sha256(S.read_bytes()).hexdigest(),clauses=rows),indent=2)+'\n')
print(len(rows),'clauses')
