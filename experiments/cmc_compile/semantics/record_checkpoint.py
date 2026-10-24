"""Record a verified public-support checkpoint, never top-level completion."""
from pathlib import Path
import json,hashlib,shutil
from datetime import datetime,timezone
R=Path(__file__).resolve().parent;E=R.parent;W=E.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,indent=2)+'\n')
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='SemanticsAudit');assert k['exit_code']==0
al=Path(next(x for x in reversed(checks)if x['module']=='SemanticsAudit' and x['mode']=='development')['log']).read_text()
assert al.count('AUDIT ')==al.count('Closed under the global context')==eff['expected_assumption_audits'] and 'Axioms:'not in al
assert len(pub)==len(eff['modules'])==9 and all(x['exit_code']==0 and sha(Path(x['path']))==x['sha256']for x in pub)
for x in read(R/'metrics/kernel-input-manifest.json'):
 assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['vo']))==x['vo_sha256']
for x in read(E/'baseline/source-manifest.json'):
 assert sha(Path('/Users/nizitong/cmc')/x['path'])==sha(E/'baseline/cstar_project'/x['path'])==x['sha256']
for x in read(E/'baseline/target-manifest.json'):assert sha(Path(x['path']))==x['sha256']
assert sha(Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md'))==sha(E/'baseline/documentation-before/SKILL.md')
reg=read(R/'metrics/regression-check.json');assert reg['exit_code']==0 and reg['sha256']==sha(R/'target/SemanticsRegression.v')
summary=dict(status='public_support_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),
 top_level_qcp_verified=False,source_cstar_verified=True,public_modules=9,public_cost=eff['totals'],
 public_lemma_count=108,constructive_decision_proofs=2,assumption_audits=110,axioms_used_by_audited_proofs=[],
 kernel=k,canonical_publication_all_passed=True,executable_regression_checks=12,
 trusted_automation_results_added=0,top_level_vcs_generated=False,skill_updated=False,
 note='coqchk checks the transitive QCP environment, which contains pre-existing axioms; Print Assumptions for each of the 110 new proof constants is closed. This checkpoint does not establish compiler preservation or the cmc_compile C contract.',
 baseline=read(R/'metrics/baseline-audit.json'),remaining_obligations=str(R/'metrics/remaining-obligations.json'))
write(R/'metrics/checkpoint.json',summary)
status=read(E/'metrics/status.json');status['status']='in_progress_public_semantics_verified_preservation_pending'
status['new_verified_public_definitions']=eff['totals']['definitions'];status['new_verified_public_lemmas']=eff['totals']['lemmas']
status['public_support_checkpoint']=summary;status['additional_public_dependency_cost_so_far']=eff['totals'];status['additional_public_dependency_cost_final']=None
status['current_dependency_gap']='Actual source/TVM semantics and decoding now exist. Annotated transition/erasure, full invariant initial/step/iteration, cmc_successful_exec_simulation, cmc_preservation, and cmc_compile_success_bridge are still missing. The accepted blocked annotation report is historical.'
status['documentation_unchanged']=False;status['skill_updated']=False;status['inventory_success_updated']=False
write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall['status']=summary['status'];overall['public_support_checkpoint']=dict(totals=eff['totals'],modules=9,lemmas=108,definitions=276,used_by_top_level_case=False)
overall['target_completed_this_attempt']['verified_public_definitions']=276;overall['target_completed_this_attempt']['verified_public_lemmas']=108
overall['target_completed_this_attempt']['public_proof_lines']=370;overall['target_completed_this_attempt']['public_definition_lines']=1069
overall['note']='Top-level C proof/annotation final costs remain unknown. This checkpoint adds only public semantics/support: 276 definitions,108 lemmas,1069 definition lines,370 proof lines (368 lemma+2 decision). Do not combine this partial cost with an unproved preservation theorem or compute a source/target ratio. Reused library code is unchanged; recompilation costs are logged separately.'
write(E/'metrics/effort.json',overall)
rows=['| 模块 | 定义/数据类型 | 引理 | 定义行 | Proof 行 |','|---|---:|---:|---:|---:|']
for m in eff['modules']:
 c=m['counts'];rows.append(f"| `{Path(m['file']).name}` | {c['definitions']} | {c['lemmas']} | {c['definition_lines']} | {c['proof_lines']} |")
(R/'README.md').write_text('''# cmc_compile 公共语义支持进度

已完成本批 9 个纯 Rocq 公共模块的编译、独立内核检查与假设审计，并已接入 QCP 仓库。**顶层 cmc_compile 的 QCP 验证尚未完成，skill 未更新。**

本批包含实际对象/解码、codegen 条件具体化、数值与字节内存、TVM 28 条指令与执行/终止关系、源值/指针来源/初始化标签/调用/作用域/逐步执行/终止语义，以及内存模拟和终止输出观察支持。复用原 AST、指令、布局、代码/数据模型和已有字节编码证明；未假定 cmc_preservation，也未修改顶层原契约。

新增公共成本按非空非纯注释物理行统计。Proof 包含引理陈述和 Proof/Qed，定义单列；两项可执行相等性判定的证明体另计 2 行。生成的审计代码、测试和工具脚本不计入公共 proof。尚未被顶层 C 案例引用的辅助引理也计入本批成本。

'''+ '\n'.join(rows)+'''

合计：276 项定义/数据类型，108 条引理；定义 1069 行，proof 370 行（引理 368 + 判定证明 2）。这些是目前已完成的公共增量，最终公共闭包成本仍未知。源同名/同类型声明链接见 `metrics/source-matched-declarations.json`；它不包括对应证明构造器完整闭包，不能拿其行数计算 proof 比率。

验证证据：

- `metrics/checkpoint.json`：本批验收状态；顶层完成标志明确为 false。
- `logs/028-development-SemanticsAudit.log`：逐项签名和 Print Assumptions；110 项均 closed。
- `logs/029-kernel-SemanticsAudit.log`：coqchk 退出 0，耗时约 291.9 秒，无 unsafe fixpoint、type-in-type 或 assumed positivity。
- `metrics/publication.json`：QCP 正式目录中的 9 个模块全部编译通过。
- `metrics/canonical-reused-checks.json`：24 个原样复用库的重编译，新增源代码成本为 0。
- `target/SemanticsRegression.v`：12 项执行回归，覆盖常量、短路、调用/I/O、循环、全局字节和错误分支；不替代通用保持性证明。

QCP 传递导入环境含原有逻辑/分离逻辑公理，coqchk 的环境清单会列出它们；新证明的逐项假设审计均不依赖这些公理。没有新增 Axiom、Parameter、Admitted 或 Abort。

语义边界：总列表查询保留 HOL 的 NIL/负索引解释参数，并证明合法索引与原有查找的一致性；没有通过新增合法输入前提抹去非法索引分支。TVM 用 Forall 的地方给出与受界索引谓词的等价证明。源执行保留原最小闭包定义，并证明等价有限步见证与确定性。源初始内存与 TVM 装载内存直接证明相等。字符/整数/指针加载和初始化字节存储模拟是带明确局部模拟前提的辅助引理，不是顶层保持性结论。

仍需迁移的连接见 `metrics/remaining-obligations.json`：实际 annotation 更新/擦除、18 项保持性不变量及 initial/step/iter、成功执行模拟、cmc_preservation、cmc_compile_success_bridge，再恢复原 annotation owner 完成 C 资源标注/VC/终检。当前仍不具备这些根定理；不能把本批结果解释成编译器或顶层 C 验证通过。

重放公共库：按 publish.py 中的依赖序，运行 `python3 check.py development <模块名>`；`audit.py` 生成签名/成本审计；`python3 check.py development SemanticsAudit` 与 `python3 check.py kernel SemanticsAudit` 执行独立验证。所有完整命令、退出码和开发失败尝试保存在 metrics/checks.json。完整源 C* 重放此前已经通过，本批未重复运行。
''')
old=E/'REPORT-before-semantics.md'
if not old.exists():shutil.copy2(E/'REPORT.md',old)
(E/'REPORT.md').write_text('''# cmc_compile：公共语义支持已推进，顶层 QCP 尚未完成

本批新增 9 个公共 Rocq 模块，已通过编译、独立内核检查和逐项假设审计，并已接入 `/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/`。具体产物、命令、语义边界与工作量见 [公共支持记录](semantics/README.md)。**尚未证明完整 cmc_preservation，未完成顶层 cmc_compile 的 QCP 验证，skill 未更新。**

已补入实际 TVM/源程序执行与终止语义、对象解码及模型解码唯一性、原 codegen 条件具体实例；证明了初始内存/IO 对应、执行确定性、字符/整数/指针加载模拟、存储后初始化字节模拟、终止目标的输出观察等。原契约仍要求任意解码对象上的语义保持性；只得到模型字节或本批辅助定理都不足以满足它。

新增公共成本单列：276 项定义/数据类型、108 条引理；定义 1069 行，proof 370 行（含引理陈述，另含 2 行判定证明）。复用 24 个原库不改源码、不重复计入新增成本。12 项执行回归单列为验证，不计入公共证明。完整公共依赖闭包尚未结束，最终成本和两边比率仍为 null。

| 顶层案例指标 | C* 基线 | QCP 最终成本 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行／2 条 | 未完成 |
| Specification + annotation | 14 行 | 未完成 |
| 函数内 proof | 435 行 | 未完成 |
| 私有 proof 支持 | 64 行 | 未完成 |
| 案例 proof 合计 | 499 行 | 未完成 |
| 同文件公开 success bridge | 42 行 | 未完成 |
| 新增外部公共依赖 | 完整闭包尚未测完 | 当前定义 1069 行／proof 370 行，非最终值 |

源 proof 的 541 行合计只含案例和同文件 bridge，不含外部保持性闭包；getter 3 行、其他初始化/审计 29 行仍另列。历史源开发时间与人工活跃时间未知。

下一段连接仍是：annotation 更新与擦除 → 原 18 项不变量的 initial/step/iter → 成功源执行模拟 → cmc_preservation → cmc_compile_success_bridge → 顶层 C 资源标注、VC 和终检。详细源定位与完成状态见 [剩余义务](semantics/metrics/remaining-obligations.json)。这些缺口没有用假定公理、加强 Require 或弱化 Ensure 替代。

原 controller run 为 `cmc_compile_migration-20261019230022`，annotation owner 为 `/root/compile_annotation`。初始 pre-VC dependency-gap 报告仍作为历史证据保存；其中“所有语义定义均不存在”的描述已被本批进展取代。当前 C run 仍未生成 VC。依赖连接齐全后，需修复 retry-round 对不存在的历史 manual 文件做摘要的 FileNotFoundError，再恢复同一 owner。公共数学支持的迁移属于用户已授权范围，可以独立推进；先前报告用角色边界解释无法继续公共依赖工作，现已纠正。

源 C* 完整重放此前已通过：1040.281 秒，退出码 0，verification_conditions、axioms、strategies 均为空。原 600 秒外部超时已通过可配置超时/心跳/进程组清理修复，日志见 `metrics/cstar-verification.json` 与 `logs/20261019T151758968928Z-cstar-source/`。本批核对了 518 个源文件和 185 个既有目标源码哈希均未变。迁移 skill、完成清单和 MIGRATION_PLAN 也未改动，顶层通过后再更新。

初始阶段记录已保留为 `REPORT-before-semantics.md`；最新状态以此文件、`metrics/status.json` 和 `semantics/metrics/checkpoint.json` 为准。
''')
print(json.dumps({k:summary[k]for k in ('status','public_modules','public_cost','public_lemma_count','assumption_audits','canonical_publication_all_passed','top_level_qcp_verified','skill_updated')},ensure_ascii=False))
