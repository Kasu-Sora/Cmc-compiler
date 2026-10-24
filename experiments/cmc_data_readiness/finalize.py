"""Audit and report pure readiness migration after all verification succeeds."""
from pathlib import Path
import hashlib, json, re, shutil
from audit_syntax import coq_regions, coq_mask, line_span
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((R/'metrics/cstar-verification.json').read_text())
assert source['clean'] and source['exit_code']==0
checks=json.loads((R/'metrics/checks.json').read_text())
lib=Q/'Rocq/examples/QCP_demos_human/cmc_program_ready_migration_lib.v'
for kind in ['development','kernel','audit','publication']:
    last=next(x for x in reversed(checks) if x['kind']==kind)
    assert last['exit_code']==0,(kind,last)
    if kind!='audit':assert last['source_sha256']==sha(lib)
audit=next(x for x in reversed(checks) if x['kind']=='audit')
audit_text=Path(audit['log']).read_text()
assert audit_text.count('Closed under the global context')==9
assert 'Axioms:' not in audit_text
for file in ['source-manifest.json','target-manifest.json']:
    for row in json.loads((R/'baseline'/file).read_text()):assert sha(Path(row['path']))==row['sha256'],row['path']
dep=json.loads((R/'baseline/dependency-snapshot.json').read_text())
for row in dep['base_sources']+dep['base_artifacts']:
    assert sha(R/'build'/row['relative_path'])==row['sha256'],row['relative_path']
t=lib.read_text();masked=coq_mask(t)
assert not re.search(r'\b(?:Admitted|Axiom|Parameter|Abort)\b',masked)
regions=coq_regions(t);rows=[]
length_support={'cm_ready_global_bytes_length','cm_ready_globals_bytes_length','cm_ready_strings_bytes_length'}
for r in regions:
    if r['kind'] not in ['Lemma','Theorem','Definition']:continue
    if r['kind']!='Definition':assert r['ending']=='Qed'
    category='definition' if r['kind']=='Definition' else 'new_length_support' if r['name'] in length_support else 'readiness_proof'
    rows.append(dict(name=r['name'],category=category,span=line_span(t,r['start'],r['end']),nonblank_lines=sum(bool(l.strip()) for l in masked[r['start']:r['end']].splitlines()),sha256=hashlib.sha256(t[r['start']:r['end']].encode()).hexdigest()))
assert len(rows)==10
counts={k:sum(r['nonblank_lines']for r in rows if r['category']==k) for k in ['definition','new_length_support','readiness_proof']}
counts['all_new_public_proof']=counts['new_length_support']+counts['readiness_proof']
se=json.loads((R/'metrics/source-effort.json').read_text())
sd=json.loads((R/'metrics/source-additional-definitions.json').read_text())
manifest=[]
for p in [lib,lib.with_suffix('.vo'),R/'target/DataReadinessAudit.v']:
    if p.parent!=R/'target':shutil.copy2(p,R/'target'/p.name)
    manifest.append(dict(path=str(p),sha256=sha(p)))
(R/'target/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
result=dict(status='passed',direction='C*/HOL -> Rocq (QCP shared mathematical library)',source_units=['cmc_concrete_data_ready.c','cmc_concrete_program_ready.c'],runtime_functions=0,annotation=0,c_vcs='not applicable; pure proof modules',new_public_definition_count=1,new_public_theorem_count=9,new_public_helper_count=8,counts=counts,regions=rows,source_effort=se,source_additional_dependencies=sd,source_replay=source,checks=checks,source_unchanged=518,previous_target_artifacts_unchanged=True,main_theorem='forall policy p, cm_typed_program policy p -> cm_concrete_data_ready p',source_data_definition_reused=True,new_assumptions=False,all_nine_theorems_closed_under_global_context=True,trusted_auto_witnesses_added=0,source_global_historical_active_seconds=None,model_active_seconds=None,
semantic_review={
 'data_ready':'Source nil/cons equations match the existing cm_data_globals_wf exactly; checked by kernel conversion. No duplicate definition or added premise.',
 'program_ready':'All seven source conjuncts retained in the same order, including 1048560 capacity and 8-byte initial prefix; typed_program remains the only premise with the existing universal lookup policy.',
 'indexed_globals':'Bounds are used before converting Z indices to nat; only in-range lookup semantics is required. The existing rep/semantic globals size theorem is reused.',
 'sizes':'Global positivity follows from global_wf; string length is nonnegative. Static size 16 + globals + strings <=1048576 yields the precise 1048560 bound.',
 'bytes':'The existing actual byte-list model is unchanged. Length is proved directly for nonnegative global size, including initialized padding and zero-fill branches, then aggregated. This replaces internal source proof architecture; it does not claim the complete general codegen theorem family was migrated.',
 'scope':'Two pure support units; no additional runtime C bodies, compiler preservation or TVM execution theorem. QCP single-C controller is inapplicable; coqc and recursive coqchk are recorded instead.'},
process_notes=['Development 1 failed because the whole-list size in the safe predicate required unfolding.', 'Development 2 failed because generic Zlength rewriting selected the initializer rather than the repeat suffix; rewrite targeted to repeat.', 'Development 3 failed on final addition association; reduce the eight-zero prefix then lia.', 'Development 4 passed. No specification change or new premise was made.'],
counting_note='Nonblank non-comment physical regions including statements and Proof/Qed; old reused definition/lemmas charged zero increment. All target proofs are in a shared library: readiness_proof and new_length_support partition their total, not extra charges. Validation harness and framework getters/scaffolding are separate. Historical work is unknown.')
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
report=f'''# 数据 readiness：C* → Rocq

完成 `cmc_concrete_data_ready.c` 的现有定义复用核验，并迁移 `cmc_concrete_program_ready.c` 的全部公开定义／定理及必要支持。二者都是纯逻辑支持文件，运行时函数与 C annotation 均为 0；没有人为添加 C wrapper 或生成空 VC。

核心结果：`forall policy p, cm_typed_program policy p -> cm_concrete_data_ready p`。原七项结论全部保留：全局表示安全、逐项 global_wf、字符串表示安全、两类大小非负、合计不超过 1048560，以及实际数据长度等于 8 + globals + strings。保持既有 lookup policy 参数化，不增加输入前提。

## 验证

- C* 隔离重放 `cmc_concrete_program_ready.c`（包含 data_ready）通过，耗时 {source['verification_seconds']:.3f} 秒；VC、axioms、strategies 均为空。
- Rocq 8.20.1：完整模块 coqc 通过，递归 coqchk 通过，正式路径编译通过。
- 定义方程与公开定理签名独立核验通过；9 条定理的 Print Assumptions 全部为 Closed under the global context。新增 Admitted／Axiom／Parameter／自动 witness 均为 0。
- 依赖来自已验收的冻结源码／对象快照；518 个源 C/H 文件、此前 180 个目标文件均未改动。未导入任何此前案例的 proof_auto／proof_manual。

## 工作量

| 分类（非空行） | C* | Rocq |
|---|---:|---:|
| 运行时 annotation | 0 | 0 |
| 本次新增 readiness 定义 | 13 | {counts['definition']} |
| readiness 模块证明（含私有支持） | 417 | {counts['readiness_proof']} |
| 新涉及的公共长度支持定义 | 21 | 0 |
| 新涉及的公共长度支持证明 | 138 | {counts['new_length_support']} |
| 本轮 proof 合计 | 555 | {counts['all_new_public_proof']} |

data_ready 的源定义 10 行，目标既有定义 6 行，已在 emit-globals 计费，本轮新增均为 0。目标新增 1 项定义、1 条主定理和 8 条支持引理；全部位于公共库。上表 readiness 与长度支持是其成本拆分，不应再次把公共库总量相加。

源 21 行长度计数中间定义在目标通过直接对已有实际字节列表证明长度替代，没有复制另一套数据模型。只保证本例需要的非负尺寸域及原最终定理，不把更一般的 codegen 保持性模块标记为完成。既有 cm_rep_global_size_matches、cm_rep_globals_size_matches 和 cm_data_globals_wf 复用，增量为 0。

开发编译 4 次，失败 3 次后通过；失败分别为列表尺寸展开、Zlength 重写定位、末尾加法结合。每次命令、版本、退出码、耗时与日志保存于 metrics/checks.json。源 getter 9 行、框架注册／公理守卫 14 行及目标验证 harness 单列排除。历史人工与模型活跃时间无法独立测量，记为 null；行数不是工时或工具效率结论。

## 产物与后续

- [公共库]({lib})
- [计量记录]({R/'metrics/effort.json'})
- [验证记录]({R/'metrics/checks.json'})
- [定义与签名检查]({R/'target/DataReadinessAudit.v'})

运行时进度仍为 30 个实现单元、131 个函数；另完成这两个纯支持单元。readiness 链还剩 code_ready、temp_ready、function_ready、compile_ready；顶层 cmc_compile 与完整保持性证明仍待完成。
'''
(R/'REPORT.md').write_text(report)
print(json.dumps({'status':'passed','counts':counts,'new_theorems':9},indent=2))
