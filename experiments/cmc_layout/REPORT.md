# cmc_concrete_layout.c：C* → QCP 迁移与工作量

2026-10-15。整个文件的 **39 个运行时函数**及必要公共模型已完成迁移。原 C* 证明重放通过；QCP run `cmc_layout_migration-20261015200400` 最终为 `done`，final-check 为 `passed`。原 ABI 头文件逐字不变，全部函数及前向声明的运行时 token 与去除证明层的原源码一致。

**148 条顶层手工义务及 234 个 split 子目标完成；另有 332 条自动结果以 `Admitted` 导出，作为 QCP 自动层的信任边界。** 手工证明及新增公共库没有 `Admitted`、`Axiom` 或 `Parameter`。采用整体证明路线的顶层义务，其 22 个未使用拆分草稿保留 `Abort`，不计入已完成 proof；顶层目标均已证明，路线由 final-check 核查。

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
| 39 函数 specification | 421 | 109 |
| 函数体 annotation | 10 | 564 |
| Specification + annotation | 431 | 673 |
| 案例 proof | 4568 | 2753 |
| 文件内原公共 proof／目标新增公共 proof | 208 | 113 |
| 上两项 proof 合计 | 4776 | 2866 |

C* 案例 proof 包含 4394 行内联 proof 和 174 行私有辅助证明；208 行是文件中公开引理及其共享构造器的去重闭包。目标案例 proof 含 1607 行证明体与 1146 行声明/Proof/Qed 等包装，不能全部称为新手写 tactic。新增公共库的模型定义、公共引理和导入分别计量，不混入案例 proof。

本文件没有运行时循环。QCP 有 35 个资源/递归调用断言（562 行）及 2 处 where（2 行）；C* 的 10 行辅助标注均为 where。QCP 将多个逻辑参数放在同一条 where 内，行数差异不等于绑定数量减少。新增中间断言用于打开描述符/AST 资源并准备递归调用。既有源证明主要在内联 proof 中操作同类资源，因此不能只比较 annotation 一列。

### 每个函数的明细

以下 C* proof 是该函数内联部分；文件级私有辅助与公共闭包在上表单列，避免重复摊派。

| 函数 | C* spec | C* ann | C* inline proof | QCP spec | QCP ann | QCP case proof |
|---|---:|---:|---:|---:|---:|---:|
| `cm_max` | 2 | 0 | 14 | 2 | 0 | 20 |
| `cmc_is_pointer` | 3 | 0 | 14 | 2 | 0 | 24 |
| `cmc_is_pointer_value` | 3 | 0 | 4 | 2 | 0 | 0 |
| `cmc_pointee` | 3 | 0 | 0 | 2 | 0 | 0 |
| `cmc_leaf_size` | 2 | 0 | 33 | 2 | 0 | 50 |
| `cmc_code_slot_size` | 3 | 0 | 70 | 2 | 0 | 23 |
| `cmc_members_size` | 6 | 0 | 95 | 3 | 11 | 68 |
| `cmc_struct_size_at` | 8 | 0 | 89 | 3 | 14 | 62 |
| `cmc_nonzero` | 2 | 0 | 12 | 2 | 0 | 21 |
| `cmc_global_array_at` | 6 | 0 | 80 | 3 | 13 | 58 |
| `cmc_slot_array_at` | 6 | 0 | 78 | 3 | 11 | 60 |
| `cmc_slot_type_at` | 6 | 0 | 76 | 3 | 11 | 50 |
| `cmc_member_array_at` | 6 | 0 | 78 | 3 | 11 | 48 |
| `cmc_type_size_at` | 8 | 0 | 53 | 3 | 0 | 42 |
| `cmc_slots_size` | 8 | 0 | 90 | 3 | 11 | 79 |
| `cmc_slots_prefix` | 12 | 0 | 222 | 3 | 13 | 112 |
| `cmc_members_prefix` | 11 | 0 | 218 | 3 | 13 | 111 |
| `cmc_member_offset_at` | 10 | 0 | 105 | 3 | 16 | 63 |
| `cmc_struct_member_array_at` | 9 | 0 | 97 | 3 | 16 | 60 |
| `cmc_globals_size` | 7 | 0 | 95 | 3 | 13 | 72 |
| `cmc_globals_prefix` | 11 | 0 | 218 | 3 | 15 | 116 |
| `cmc_strings_size` | 7 | 0 | 94 | 3 | 12 | 57 |
| `cmc_strings_prefix` | 11 | 0 | 229 | 3 | 14 | 97 |
| `cmc_global_address` | 9 | 0 | 19 | 3 | 0 | 9 |
| `cmc_string_address` | 19 | 0 | 51 | 3 | 0 | 9 |
| `cmc_binding_array_value` | 26 | 0 | 69 | 3 | 0 | 36 |
| `cmc_binding_array` | 25 | 6 | 0 | 3 | 1 | 0 |
| `cmc_member_array` | 27 | 0 | 50 | 3 | 0 | 45 |
| `cmc_member_array_value` | 29 | 4 | 6 | 3 | 1 | 0 |
| `cm_args_length` | 6 | 0 | 85 | 3 | 9 | 56 |
| `cmc_args_tpair` | 11 | 0 | 112 | 3 | 12 | 63 |
| `cm_expr_temps` | 11 | 0 | 1209 | 3 | 222 | 741 |
| `cm_expr_rtemps` | 8 | 0 | 0 | 3 | 0 | 0 |
| `cmc_stmt_temps` | 10 | 0 | 613 | 3 | 125 | 481 |
| `cmc_frame_size` | 31 | 0 | 36 | 3 | 0 | 0 |
| `cmc_param_offset` | 12 | 0 | 13 | 3 | 0 | 0 |
| `cmc_local_offset` | 20 | 0 | 24 | 3 | 0 | 0 |
| `cmc_temp_offset` | 24 | 0 | 31 | 3 | 0 | 0 |
| `cm_normalize_count` | 3 | 0 | 12 | 2 | 0 | 20 |

## 新增公共依赖与复用

目标新增公共定义 96 项、261 行；新增公共引理 17 条、113 行。类型/记录、原数学模型、安全谓词、堆表示、总查询策略以及必要证明均可供后续文件复用。本次全额记录新建成本，后续直接导入时应仅计增量。

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

C* 在隔离副本上重放原源码，exit 0，verification_conditions/axioms/strategies 均为空，用时 49.967 秒。QCP 经标注重放、依赖准备、独立 VC 检查、各组验证、合并后完整检查、final-apply 及 final-check。39 个函数均有验证义务覆盖；最终运行时、ABI、接受版本与最终证明哈希都由计量脚本检查。

自动文件的 332 个 `Admitted` 保留原样，并在 `effort.json` 逐名列出；手工剩余义务为 0。最终结果仍依赖 QCP 自动推理与现有逻辑基座，不能称为完全没有信任假设的独立内核证书。导入 copy-bytes 的纯定义库，不导入该函数的 auto/manual 证明。

过程失败、修订及运行时长以 `metrics/process-notes.json` 与控制器原始日志为准。历史 C* 作者工时、人工活跃工时及无法测量的代理活跃时间均为 null。此对照是阅读既有 C* 成品后迁移到 QCP 的成本，不是两套工具从零证明的公平竞赛。

本轮 QCP 从初始化到 done 的墙钟时间为 208.18 分钟，包含编写、调度与等待；不能与 C* 成品重放时间作速度比。37 个组均在第一个 controller attempt 通过验收，controller 组验收失败次数为 0。同一标注 attempt 内有 4 次解析／符号执行反馈失败、2 次库证明反馈失败，VC 报告另修正 1 次格式；逐次 tactic 探索失败总数未完整保留，记为 null，不推断为零。
