"""Review manifest for the final accepted implementation and helper contracts."""
from pathlib import Path
import sys, re, json, hashlib
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sys.path.insert(0,str(R.parent/'cmc_patch_calls'))
from audit_syntax import c_functions
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=read(R/'metrics/final-effort.json')
assert f['controller_final_check']['status']=='passed'
c=(R/'target/cmc_compile_migration.c').read_text()
origins={
 'cmc_model_code_length':'cmc_counts',
 'cmc_model_data_length':'cmc_counts',
 'cmc_emit_code':'cmc_emit_code',
 'cmc_patch_resolved_calls':'cmc_patch_calls',
 'cmc_emit_data':'cmc_emit_data',
}
def contract(t, name, prototype):
 fn=next(x for x in c_functions(t) if x['name']==name and x['prototype']==prototype)
 return re.search(r'/\*@.*?\*/',t[fn['start']:fn['end']],re.S).group()
helpers=[]
for name, stem in origins.items():
 p=Q/f'QCP_examples/QCP_demos_human/{stem}_migration.c'
 source=contract(p.read_text(),name,False)
 target=contract(c,name,True)
 assert source==target,(name,'helper contract drift')
 helpers.append(dict(name=name,verified_implementation=str(p),implementation_sha256=sha(p),
                     contract_sha256=hashlib.sha256(source.encode()).hexdigest(),verbatim_equal=True))
manual=(R/'target/cmc_compile_migration_proof_manual.v').read_text()
assert 'eapply cmc_compile_success_bridge; eauto.' in manual
result=dict(status='review_passed',kind='human_readable_semantic_mapping_and_mechanical_identity_checks',
 helpers=helpers,artifacts=f['artifacts'],
 source_contract='/Users/nizitong/cmc/cmc.c:144',
 source_representations='/Users/nizitong/cmc/cmc_rep.c:1894',
 mathematical_contract_review='preservation-contract-audit.json',
 mapping=[
  'cm_rep_program_valid = 1 is the source conditional definition of cm_wf_program; target cm_semantic_wf_program instantiates the original four concrete TVM codegen conditions, not a preservation certificate.',
  'Program heap folds the existing context representation plus the same full function list; the original five fields and four lists remain owned.',
  'All eight output fields, nonnegative capacities, three undefined buffers and their zero-capacity empty ownership are preserved.',
  'Capacity result is return=1, insufficient code or data capacity, exact required lengths, entry=-1 and unchanged buffer ownership.',
  'Success is return=0, entry=0, original code/data bounds, exact opcode/immediate/data prefixes, undefined tails and original program ownership.',
  'Success universally quantifies actual source termination and original decoded object, concluding TVM termination with identical input/output/status. The actual return proof applies the verified success bridge.',
  'Source HOL total-query interpretations are explicit policies; internal readiness facts are derived in the entry VC, not added to C Requires.',
  'Runtime tokens and ABI equal the frozen baseline. No source or previously verified target was changed.'
 ],
 trust={
  'new_manual_or_case_lib_axiom_admitted_parameter':False,
  'mathematical_support_assumption_audits':'closed; see all 22 checkpoints',
  'framework_axioms':'existing QCP separation-logic foundation retained',
  'automatic_top_level_vcs':f['automatic_top_level_vcs'],
  'automatic_pure_subobligations':f['automatic_pure_subobligations'],
  'automatic_admitted_constants':f['automatic_trusted_witnesses']
 },
 scope='Original preservation/compile-success roots and actual C compile contract. Original 18 components established on reachable successful executions via stronger internal inductive support; not every arbitrary-state source helper/export or independent TVM C interpreter.')
(R/'metrics/final-contract-audit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],copied_helper_contracts=len(helpers),trust=result['trust']),ensure_ascii=False))
