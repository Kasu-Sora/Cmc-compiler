#!/usr/bin/env python3
"""Audit accepted artifacts and reproduce region-based effort counts; not a prover."""
import hashlib
import json
import pathlib
import re
import shutil

ROOT = pathlib.Path(__file__).resolve().parent
QCP = pathlib.Path('/Users/nizitong/QCP/qcp-binary-democases')
RUN = 'cmc_copy_bytes_migration-20261015183239'
REPORT = QCP / 'reports' / RUN
state = json.loads((REPORT / 'controller_state.json').read_text())
assert state['phase'] == 'done' and state['final_check']['status'] == 'passed'
source_check = json.loads((ROOT / 'metrics/cstar-verification.json').read_text())
assert source_check['clean']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(ROOT / 'baseline/cmc_concrete_copy_bytes.c') == source_check['source_sha256']
manifest = []
annotation = next(a for a in state['attempts'].values()
                  if a['phase'] == 'annotation' and a['status'] == 'accepted')
sealed = pathlib.Path(annotation['annotation_history_directory']) / 'after'
for role in ['c_file', 'formal_case_lib', 'goal_file', 'proof_auto_file',
             'proof_manual_file', 'goal_check_file']:
    rel = state['target_files'][role]
    p = QCP / rel
    if role == 'proof_manual_file':
        assert sha(p) == state['final_candidate']['proof_manual_sha256']
    elif role == 'formal_case_lib':
        assert sha(p) == state['final_candidate']['proving_merged_lib_sha256']
    else:
        assert p.read_bytes() == (sealed / rel).read_bytes(), 'Accepted file drift: ' + rel
    out = ROOT / 'target' / p.name
    shutil.copy2(p, out)
    manifest.append(dict(role=role, canonical_path=str(p),
                         snapshot=str(out.relative_to(ROOT)), sha256=sha(p)))
(ROOT / 'target/manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')

# Preserve reports, receipts and logs; leave controller-owned originals untouched.
shutil.copytree(REPORT, ROOT / 'logs/qcp-controller', dirs_exist_ok=True)
shutil.copy2(QCP / 'verification_runs' / RUN / 'makefile_dependency_snapshot.json',
             ROOT / 'logs/qcp-controller/makefile_dependency_snapshot.json')

regions = []
counts = {'cstar': {}, 'qcp': {}, 'cstar_reused': {}}

def count(system, category, file, spans):
    p = ROOT / file
    lines = p.read_text().splitlines()
    n = sum(bool(lines[i - 1].strip()) for a, b in spans for i in range(a, b + 1))
    counts[system][category] = counts[system].get(category, 0) + n
    regions.append(dict(system=system, category=category, file=file, spans=spans,
                        nonblank_lines=n, sha256=sha(p)))

source_size = json.loads((ROOT / 'metrics/cstar-source-size.json').read_text())
assert source_size['sha256'] == sha(ROOT / 'baseline/cmc_concrete_copy_bytes.c')
for category, data in source_size['regions'].items():
    count('cstar', category, 'baseline/cmc_concrete_copy_bytes.c', data['spans'])

target_file = 'target/cmc_copy_bytes_migration.c'
target = (ROOT / target_file).read_text()
for match in re.finditer(r'/\*@.*?\*/', target, re.S):
    block = match.group()
    category = ('specification' if re.search(r'\bWith\b', block)
                else 'annotation' if re.search(r'\b(Inv|Assert|which)\b', block)
                else 'coq_imports' if re.search(r'\bImport Coq\b', block)
                else 'external_predicate_declarations')
    start = target[:match.start()].count('\n') + 1
    end = target[:match.end()].count('\n') + 1
    if target.splitlines()[end - 1].strip() == '*/':
        end -= 1
    count('qcp', category, target_file, [(start, end)])

def lemma_regions(file, category):
    content = (ROOT / file).read_text()
    assert not re.search(r'\b(Admitted|Axiom|Parameter|Abort)\b', content)
    names = []
    for match in re.finditer(r'^Lemma\s+(\w+).*?^Qed\.', content, re.S | re.M):
        names.append(match.group(1))
        count('qcp', category, file,
              [(content[:match.start()].count('\n') + 1,
                content[:match.end()].count('\n') + 1)])
    assert len(names) == len(re.findall(r'^Lemma\s+', content, re.M))
    return names

manual_names = lemma_regions('target/cmc_copy_bytes_migration_proof_manual.v', 'case_proof')
helper_names = lemma_regions('target/cmc_copy_bytes_migration_lib.v', 'new_common_proof')
lib = (ROOT / 'target/cmc_copy_bytes_migration_lib.v').read_text()
count('qcp', 'case_lib_seed', 'target/cmc_copy_bytes_migration_lib.v', [(1, 3)])
assert not re.search(r'^\s*(Fixpoint|Inductive)\b', lib, re.M)
definition_names = []
for match in re.finditer(r'^Definition\s+(\w+).*?\.[ \t]*$', lib, re.M | re.S):
    definition_names.append(match.group(1))
    count('qcp', 'new_common_definition', 'target/cmc_copy_bytes_migration_lib.v',
          [(lib[:match.start()].count('\n') + 1, lib[:match.end()].count('\n') + 1)])
assert len(definition_names) == len(re.findall(r'^Definition\s+', lib, re.M))
auto = (ROOT / 'target/cmc_copy_bytes_migration_proof_auto.v').read_text()
auto_names = re.findall(r'^Lemma\s+(\w+)', auto, re.M)
assert len(auto_names) == len(re.findall(r'\bAdmitted\.', auto))
manual = (ROOT / 'target/cmc_copy_bytes_migration_proof_manual.v').read_text()
assert 'Require Import SimpleC.EE.QCP_demos_human.cmc_copy_bytes_migration_lib.' in manual
assert 'cmc_uint8_buffer_nonnull' in manual
shared_check = dict(status='passed', evidence='controller accepted case-lib compilation and imported current library in final goal-check closure',
                    standalone_supplement_needed=False)
assert annotation['main_check']['formal_case_lib_coqc']['status'] == 'passed'
assert sha(ROOT / 'target/cmc_copy_bytes_migration_lib.v') == annotation['owner_generation_receipt']['target_digests'][state['target_files']['formal_case_lib']]
shared_check['case_lib_coqc'] = annotation['main_check']['formal_case_lib_coqc']
shared_check['sha256'] = sha(ROOT / 'target/cmc_copy_bytes_migration_lib.v')
model_check = json.loads((ROOT / 'metrics/cstar-model-probe.json').read_text())
assert model_check['clean']
process_notes = json.loads((ROOT / 'metrics/process-notes.json').read_text())
counts['cstar']['case_proof'] = counts['cstar']['inline_case_proof'] + counts['cstar']['private_case_helpers']
proof_body_lines = sum(bool(line.strip()) for body in re.findall(r'^Proof\.\s*\n(.*?)^Qed\.', manual, re.M | re.S) for line in body.splitlines())
for system in ['cstar', 'qcp']:
    counts[system]['specification_plus_annotation'] = (
        counts[system]['specification'] + counts[system]['annotation'])

# This direct store loop must remain byte-for-byte equivalent at C token level.
source_lines = (ROOT / 'baseline/cmc_concrete_copy_bytes.c').read_text().splitlines()
remove = {i for a, b in source_size['regions']['inline_case_proof']['spans'] for i in range(a, b + 1)}
source = '\n'.join(line for i, line in enumerate(source_lines, 1) if i >= 32 and i not in remove)
source = re.sub(r'\[\[cst::.*?\]\]', '', source, flags=re.S)
runtime_target = re.sub(r'/\*.*?\*/', '', target, flags=re.S)
tokens = lambda text: re.findall(r'\w+|\S', text)
assert tokens(source) == tokens(runtime_target)
(ROOT / 'metrics/runtime-cstar.c').write_text(source + '\n')
(ROOT / 'metrics/runtime-qcp.c').write_text(runtime_target + '\n')

# Existing source helpers are context, not new migration cost.
count('cstar_reused', 'uint8_buffer_definition', 'baseline/cmc_rep.c', [(961,965)])
reused = []
for file in ['Rocq/SeparationLogic/ArrayLib.v', 'Rocq/SeparationLogic/ArrayLibCore.v',
             'Rocq/SeparationLogic/CommonAssertion.v', 'Rocq/auxlibs/ListLib.v',
             'Rocq/listlib/Base/Positional.v', 'Rocq/listlib/General/Length.v']:
    p = QCP / file
    out = ROOT / 'baseline/qcp-reused' / p.name
    out.parent.mkdir(exist_ok=True)
    shutil.copy2(p, out)
    reused.append(dict(canonical_path=str(p), sha256=sha(p),
                       classification='existing-target-library-not-new-migration'))
timing = json.loads((REPORT / 'timing_summary.json').read_text())
result = dict(
    direction='C*/HOL -> QCP/Rocq', function='cmc_copy_bytes',
    counting_method='Nonblank physical lines in exact regions, syntax wrappers included; standalone QCP */ excluded. Contract counted once; duplicate C* header excluded. Lemma statements, Proof and Qed included. Generated VC/boilerplate excluded from handwritten proof.',
    counts=counts, regions=regions, runtime_tokens_equal=True,
    proof_body_breakdown=dict(qcp_body_lines=proof_body_lines,
                              qcp_statement_and_wrapper_lines=counts['qcp']['case_proof'] - proof_body_lines),
    newly_migrated_common=dict(model_definitions=0, representation_predicates=0,
        pure_spec_definitions=len(definition_names), definition_names=definition_names,
        helper_lemmas=len(helper_names), helper_names=helper_names,
        model_lines=0, pure_spec_definition_lines=counts['qcp'].get('new_common_definition', 0),
        proof_lines=counts['qcp'].get('new_common_proof', 0),
        new_case_lib_import_lines=0, c_import_annotation_lines=counts['qcp'].get('coq_imports', 0),
        generated_seed_scaffolding_lines=3,
        used_by_current_manual=True),
    entries=dict(cstar_logic_parameters=2, qcp_logic_parameters=2,
        cstar_loop_invariants=1, qcp_loop_invariants=1, cstar_proof_blocks=6,
        qcp_manual_lemmas=manual_names, qcp_manual_top_level_witnesses=sum("_split_goal_" not in n for n in manual_names),
        qcp_manual_split_lemmas=sum("_split_goal_" in n for n in manual_names), qcp_automatic_witnesses=len(auto_names)),
    verification=dict(cstar=source_check, qcp_phase=state['phase'],
        qcp_final_check=state['final_check'], qcp_trusted_auto_admissions=auto_names,
        qcp_remaining_manual_vcs=0, shared_library=shared_check,
        model_definition_probe=model_check, cross_prover_equivalence_theorem=False),
    process=dict(controller_timing=timing, historical_cstar_active_seconds=None,
        human_active_seconds=None, model_active_seconds=None,
        annotation_attempts=timing['annotation_metrics']['attempt_count'],
        controller_annotation_repair_rounds=timing['annotation_metrics']['annotation_repair_count'],
        owner_symexec_invocations=timing['annotation_metrics']['owner_generation_invocation_count'],
        vc_report_format_repairs=process_notes.get("vc_report_format_repairs"),
        proving_development_contract_failures=process_notes.get("proving_development_contract_failures"), proving_development_coqc_failures=process_notes.get("proving_development_coqc_failures"),
        details=process_notes),
    reused_target_dependencies=reused, artifacts=manifest)
(ROOT / 'metrics/effort.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(counts=counts, new_common=result['newly_migrated_common'],
    qcp_run_seconds=timing['run']['elapsed_seconds'], runtime_tokens_equal=True), indent=2))
