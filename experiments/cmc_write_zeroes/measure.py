#!/usr/bin/env python3
"""Audit accepted artifacts and reproduce region-based effort counts; not a prover."""
import hashlib
import json
import pathlib
import re
import shutil

ROOT = pathlib.Path(__file__).resolve().parent
QCP = pathlib.Path('/Users/nizitong/QCP/qcp-binary-democases')
RUN = 'cmc_write_zeroes_migration-20261015180614'
REPORT = QCP / 'reports' / RUN
state = json.loads((REPORT / 'controller_state.json').read_text())
assert state['phase'] == 'done' and state['final_check']['status'] == 'passed'
source_check = json.loads((ROOT / 'metrics/cstar-verification.json').read_text())
assert source_check['clean']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(ROOT / 'baseline/cmc_concrete_emit_zeroes.c') == source_check['source_sha256']
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
for category, data in source_size['regions'].items():
    count('cstar', category, 'baseline/cmc_concrete_emit_zeroes.c', data['spans'])

target_file = 'target/cmc_write_zeroes_migration.c'
target = (ROOT / target_file).read_text()
for match in re.finditer(r'/\*@.*?\*/', target, re.S):
    block = match.group()
    category = ('specification' if re.search(r'\bWith\b', block)
                else 'annotation' if re.search(r'\bInv\b', block)
                else 'external_predicate_declarations')
    start = target[:match.start()].count('\n') + 1
    end = target[:match.end()].count('\n') + 1
    if target.splitlines()[end - 1].strip() == '*/':
        end -= 1
    count('qcp', category, target_file, [(start, end)])

def lemma_regions(file, category):
    content = (ROOT / file).read_text()
    assert not re.search(r'\b(Admitted|Axiom|Parameter)\b', content)
    names = []
    for match in re.finditer(r'^Lemma\s+(\w+).*?^Qed\.', content, re.S | re.M):
        names.append(match.group(1))
        count('qcp', category, file,
              [(content[:match.start()].count('\n') + 1,
                content[:match.end()].count('\n') + 1)])
    assert len(names) == len(re.findall(r'^Lemma\s+', content, re.M))
    return names

manual_names = lemma_regions('target/cmc_write_zeroes_migration_proof_manual.v', 'case_proof')
helper_names = lemma_regions('target/cmc_write_zeroes_migration_lib.v', 'new_common_proof')
lib = (ROOT / 'target/cmc_write_zeroes_migration_lib.v').read_text()
count('qcp', 'case_lib_seed', 'target/cmc_write_zeroes_migration_lib.v', [(1, 3)])
count('qcp', 'new_common_imports', 'target/cmc_write_zeroes_migration_lib.v', [(5, 5)])
assert not re.search(r'^\s*(Definition|Fixpoint|Inductive)\b', lib, re.M)
auto = (ROOT / 'target/cmc_write_zeroes_migration_proof_auto.v').read_text()
auto_names = re.findall(r'^Lemma\s+(\w+)', auto, re.M)
assert len(auto_names) == len(re.findall(r'\bAdmitted\.', auto))
shared_check = json.loads((ROOT / 'metrics/shared-verification.json').read_text())
assert shared_check['clean'] and shared_check['sha256'] == sha(ROOT / 'target/cmc_write_zeroes_migration_lib.v')
model_check = json.loads((ROOT / 'metrics/cstar-model-probe.json').read_text())
assert model_check['clean']
process_notes = json.loads((ROOT / 'metrics/process-notes.json').read_text())
for system in ['cstar', 'qcp']:
    counts[system]['specification_plus_annotation'] = (
        counts[system]['specification'] + counts[system]['annotation'])

# This direct store loop must remain byte-for-byte equivalent at C token level.
source_lines = (ROOT / 'baseline/cmc_concrete_emit_zeroes.c').read_text().splitlines()
remove = {i for a, b in source_size['regions']['case_proof']['spans'] for i in range(a, b + 1)}
source = '\n'.join(line for i, line in enumerate(source_lines, 1) if i >= 8 and i not in remove)
source = re.sub(r'\[\[cst::.*?\]\]', '', source, flags=re.S)
runtime_target = re.sub(r'/\*.*?\*/', '', target, flags=re.S)
tokens = lambda text: re.findall(r'\w+|\S', text)
assert tokens(source) == tokens(runtime_target)
(ROOT / 'metrics/runtime-cstar.c').write_text(source + '\n')
(ROOT / 'metrics/runtime-qcp.c').write_text(runtime_target + '\n')

# Existing source helpers are context, not new migration cost.
count('cstar_reused', 'ireplicate_empty', 'baseline/userlib/pure_lists.c', [(394, 399)])
count('cstar_reused', 'ireplicate_snoc', 'baseline/userlib/pure_lists.c', [(405, 413)])
reused = []
for file in ['Rocq/SeparationLogic/ArrayLib.v', 'Rocq/SeparationLogic/ArrayLibCore.v',
             'Rocq/auxlibs/ListLib.v']:
    p = QCP / file
    out = ROOT / 'baseline/qcp-reused' / p.name
    out.parent.mkdir(exist_ok=True)
    shutil.copy2(p, out)
    reused.append(dict(canonical_path=str(p), sha256=sha(p),
                       classification='existing-target-library-not-new-migration'))
timing = json.loads((REPORT / 'timing_summary.json').read_text())
result = dict(
    direction='C*/HOL -> QCP/Rocq', function='cmc_write_zeroes',
    counting_method='Nonblank physical lines in exact regions, syntax wrappers included; standalone QCP */ excluded. Contract counted once; duplicate C* header excluded. Lemma statements, Proof and Qed included. Generated VC/boilerplate excluded from handwritten proof.',
    counts=counts, regions=regions, runtime_tokens_equal=True,
    newly_migrated_common=dict(model_definitions=0, representation_predicates=0,
        helper_lemmas=len(helper_names), helper_names=helper_names,
        model_lines=0, proof_lines=counts['qcp'].get('new_common_proof', 0),
        new_import_lines=1, generated_seed_scaffolding_lines=3,
        used_by_current_manual=False),
    entries=dict(cstar_logic_parameters=1, qcp_logic_parameters=1,
        cstar_loop_invariants=1, qcp_loop_invariants=1, cstar_proof_blocks=4,
        qcp_manual_lemmas=manual_names, qcp_manual_top_level_witnesses=3,
        qcp_manual_split_lemmas=3, qcp_automatic_witnesses=len(auto_names)),
    verification=dict(cstar=source_check, qcp_phase=state['phase'],
        qcp_final_check=state['final_check'], qcp_trusted_auto_admissions=auto_names,
        qcp_remaining_manual_vcs=0, shared_helper=shared_check,
        model_definition_probe=model_check, cross_prover_equivalence_theorem=False),
    process=dict(controller_timing=timing, historical_cstar_active_seconds=None,
        human_active_seconds=None, model_active_seconds=None,
        annotation_candidates=1, annotation_repairs=0, vc_report_format_repairs=2,
        proving_development_contract_failures=1, proving_development_coqc_failures=1,
        details=process_notes),
    reused_target_dependencies=reused, artifacts=manifest)
(ROOT / 'metrics/effort.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(counts=counts, new_common=result['newly_migrated_common'],
    qcp_run_seconds=timing['run']['elapsed_seconds'], runtime_tokens_equal=True), indent=2))
