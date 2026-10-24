#!/usr/bin/env python3
"""Render the final report only after complete verification and measurement."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text())
assert E['verification']['phase']=='done'
assert E['verification']['qcp_final_check']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries']
rows=[]
for source in E['source_effort']['function_counts']:
 name=source['function'];t=E['target_per_function'][name]
 rows.append(f"| `{name}` | {source['specification']} | {source['annotation']} | {source['inline_proof']} | {t['specification']} | {t['annotation']} | {t['case_proof']} |")
text=f'''# cmc_concrete_layout.c：C* → QCP 迁移与工作量

2026-10-15。整个文件的 **39 个运行时函数**及必要公共模型已完成迁移。原 C* 证明重放通过；QCP run `cmc_layout_migration-20261015200400` 最终为 `done`，final-check 为 `passed`。原 ABI 头文件逐字不变，全部函数及前向声明的运行时 token 与去除证明层的原源码一致。

**{N['manual_top_level']} 条顶层手工义务及 {N['manual_splits']} 个 split 子目标完成；另有 {N['automatic_witnesses']} 条自动结果以 `Admitted` 导出，作为 QCP 自动层的信任边界。** 手工证明及新增公共库没有 `Admitted`、`Axiom` 或 `Parameter`。采用整体证明路线的顶层义务，其 {len(E['unused_split_drafts_aborted'])} 个未使用拆分草稿保留 `Abort`，不计入已完成 proof；顶层目标均已证明，路线由 final-check 核查。

## 交付与证据

- [QCP 标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_layout_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_layout_migration_proof_manual.v)
- [公共模型及引理](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_layout_migration_lib.v)
- [逐区间、逐函数计量](metrics/effort.json)、[契约语义核对](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 结果](metrics/cstar-verification.json)、[QCP 控制器记录](logs/qcp-controller/controller_state.json)、[目标快照和哈希](target/manifest.json)
- 验证后已更新 [迁移 skill](/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md) 与 [layout 迁移指导](/Users/nizitong/.codex/skills/qcp-cstar-migration/references/cmc-layout-case.md)，校验记录为 [skill-update.json](metrics/skill-update.json)。

范围是 layout 文件的实现验证，覆盖尺寸、地址、偏移、类型/数组判定、表达式/参数/语句临时空间计算。没有把结果扩大为整个 CMC/TVM 编译保持性定理，也没有建立两个证明内核之间的机械翻译器。

## 原契约含义

| 部分 | 保留的条件与结果 |
|---|---|
| 基础算术与编码 | pointer 编码阈值 1024；叶尺寸 8/1/0；slot count 为所有 signed int，包括负数；count=0 按单值处理 |
| 描述符列表 | 原始空表/非空节点表示、字段类型和递归所有权；未擅自增加 index < length |
| 尺寸和前缀 | 精确对应原模型；保留 1048576 或 1048560 上界及前缀不超过总大小 |
| 地址 | global/string 起点为 16；string 地址含 globals 大小及 string 前缀；保留组合容量约束 |
| binding/member | 原 validity、类型编码与成员编号条件；仅拥有被读取的 program/function 字段 |
| AST 临时空间 | 14 个表达式和 11 个语句构造子；原 tpair/apair/stemps 方程及每个子节点安全界 |
| frame/offset | 仅 params/locals/body 等原指定字段；精确保留 8 字节头与 8 倍临时空间的公式和溢出前提 |

HOL `fact(P)` 映射为 QCP 纯命题，分离资源映射为相应字段 data_at 与递归表示。仅调整合取顺序、逻辑参数语法及等式替换，不削弱后置性质。AST 递归按原语法结构定义，未用额外的 C 解释器替代原规格。对应关系由逐函数人工审计及相关 Rocq 引理支持；这不是跨内核自动等价证书。

### 不得遗漏的总列表查询语义

原 binding 契约没有 `fid` 合法范围限制。固定默认函数会改变负数/越界查询含义。实际检查固定版本 HOL 内核得到：`inth n l = NTH (num_of_int n) l`；`NTH_DEF` 仅规定两个非空列表方程；`num_of_int x` 使用 Hilbert choice，负数时结果未指定。

目标用显式 `cm_lookup_policy` 保留负数转换的任意自然数，以及 `NTH n []` 随残余下标变化的任意函数值。两个 binding 契约对该 policy 全称量化，前置的 f 选择与后置模型使用同一 policy。没有加入 fid 上界、非负条件或新公理。原 HOL 选择是这一更一般定理的一个实例。新增的结构对应引理和有效索引独立性引理在公共库编译验证。

其他默认 descriptor 仅在原 validity 保证的合法下标上使用，不影响原契约。原查询证据保存在 `logs/20261015T121956Z-cstar-lookup-probe/stdout.txt` 和固定工具链 theorem catalogue。

## Annotation 与 proof 工作量

计数为最终非空物理行，包含语法包装，排除纯注释、独立 QCP `*/` 与自动生成 VC 文本。前向声明的重复契约另记，不重复计入 specification。类型、Record 与递归定义按声明项计数，不把自动生成的投影或归纳原理另算新手写定义。同一行上的多个导入只计一次物理行。行数明显受排版影响，尤其目标契约更紧凑；`effort.json` 还保留区间、字符和 token 数以便复核，不能把行数比当作耗时或难度比。

| 最终规模 | C* | QCP |
|---|---:|---:|
| 39 函数 specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| Specification + annotation | {C['specification_plus_annotation']} | {Q['specification_plus_annotation']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 文件内原公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |
| 上两项 proof 合计 | {C['proof_including_shared']} | {Q['proof_including_shared']} |

C* 案例 proof 包含 {C['inline_proof']} 行内联 proof 和 {C['private_case_proof_support']} 行私有辅助证明；{C['exported_shared_proof_closure']} 行是文件中公开引理及其共享构造器的去重闭包。目标案例 proof 含 {E['proof_body_lines']} 行证明体与 {E['proof_wrapper_lines']} 行声明/Proof/Qed 等包装，不能全部称为新手写 tactic。新增公共库的模型定义、公共引理和导入分别计量，不混入案例 proof。

本文件没有运行时循环。QCP 有 35 个资源/递归调用断言（562 行）及 2 处 where（2 行）；C* 的 10 行辅助标注均为 where。QCP 将多个逻辑参数放在同一条 where 内，行数差异不等于绑定数量减少。新增中间断言用于打开描述符/AST 资源并准备递归调用。既有源证明主要在内联 proof 中操作同类资源，因此不能只比较 annotation 一列。

### 每个函数的明细

以下 C* proof 是该函数内联部分；文件级私有辅助与公共闭包在上表单列，避免重复摊派。

| 函数 | C* spec | C* ann | C* inline proof | QCP spec | QCP ann | QCP case proof |
|---|---:|---:|---:|---:|---:|---:|
{chr(10).join(rows)}

## 新增公共依赖与复用

目标新增公共定义 {len(N['new_model_declarations'])} 项、{Q['new_common_definitions']} 行；新增公共引理 {len(N['new_helpers'])} 条、{Q['new_common_proof']} 行。类型/记录、原数学模型、安全谓词、堆表示、总查询策略以及必要证明均可供后续文件复用。本次全额记录新建成本，后续直接导入时应仅计增量。

| 新增公共部分 | 声明项／引理数 | 非空行 |
|---|---:|---:|
| 类型、模型、安全谓词和堆表示 | 96 | 261 |
| 标注阶段的基本、语义对应及结构桥接引理 | 12 | 57 |
| 证明阶段追加的查询引理 | 3 | 50 |
| 证明阶段追加的安全性投影引理 | 2 | 6 |
| 导入和作用域设置 | 按物理行去重 | 10 |

公共 proof 总计 17 条、113 行，其中 8 条在最终 manual 直接引用；其余包括源语义对应、有效索引独立性、缓冲区等价等检查用或预备引理，仍完整计入新增成本，不称为当前案例实际复用收益。[逐条引用计数](metrics/shared-helper-usage.json) 可复核。Controller 公共候选池只有 3 条，不能用池大小代替最终库成本。

另外，C 层新增 Extern 声明 108 行、Coq 导入 1 行、前向声明重复契约 3 行均单列，不混入主契约或 proof。

直接复用先前已验证 `cmc_copy_bytes_migration_lib` 的 `cmc_uint8_buffer_nonnull`。本次新增的 `cm_uint8_buffer` 空/非空空间包装及其等价引理仍计新增，不能冒充已有成果。数组所有权、整数、列表、分离逻辑基础库也直接复用。此前 byte/word 的编码引理不适用此文件，没有为减少表面成本而牵强导入。

源公共模型的依赖声明及原始区间保存在 `metrics/source-model-definitions.json`。这些是 C* 已有库，不是本次新写；原文件内公共引理 208 行也不等于全部源依赖的历史开发成本。两边已有基础库不重复全额计入迁移成本。

本次识别到的源公共模型闭包为 107 项声明、1041 行；它与目标 96 项声明组织方式不同，不能按名称数量认定漏迁移。每个模型与堆表示的含义、声明哈希及边界情况记录在语义审计中。

## 验证与局限

C* 在隔离副本上重放原源码，exit 0，verification_conditions/axioms/strategies 均为空，用时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 经标注重放、依赖准备、独立 VC 检查、各组验证、合并后完整检查、final-apply 及 final-check。39 个函数均有验证义务覆盖；最终运行时、ABI、接受版本与最终证明哈希都由计量脚本检查。

自动文件的 {N['automatic_witnesses']} 个 `Admitted` 保留原样，并在 `effort.json` 逐名列出；手工剩余义务为 0。最终结果仍依赖 QCP 自动推理与现有逻辑基座，不能称为完全没有信任假设的独立内核证书。导入 copy-bytes 的纯定义库，不导入该函数的 auto/manual 证明。

过程失败、修订及运行时长以 `metrics/process-notes.json` 与控制器原始日志为准。历史 C* 作者工时、人工活跃工时及无法测量的代理活跃时间均为 null。此对照是阅读既有 C* 成品后迁移到 QCP 的成本，不是两套工具从零证明的公平竞赛。

本轮 QCP 从初始化到 done 的墙钟时间为 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编写、调度与等待；不能与 C* 成品重放时间作速度比。37 个组均在第一个 controller attempt 通过验收，controller 组验收失败次数为 {E['process']['notes']['proof_development']['controller_group_repair_count']}。同一标注 attempt 内有 4 次解析／符号执行反馈失败、2 次库证明反馈失败，VC 报告另修正 1 次格式；逐次 tactic 探索失败总数未完整保留，记为 null，不推断为零。
'''
(R/'REPORT.md').write_text(text)
print(R/'REPORT.md')
