# cmc_concrete_counts.c：C* → QCP 迁移与工作量

整个文件的 **15 个运行时函数**及 1 个前向声明已迁移。原 C* 证明重放通过；QCP run `cmc_counts_migration-20261015235041` 为 `done`，final-check 为 `passed`。去除证明层和导入 helper 声明后，所有运行时 token 与原源码相同；复用的 ABI 头和已验证公共库哈希未变。

**完成 150 条顶层手工义务、375 个已证明 split；另有 184 条自动 witness 以 `Admitted` 导出。** 后者是 QCP 自动层的信任边界。手工证明及本轮新增公共库没有 `Admitted`、`Axiom` 或 `Parameter`。未采用的 split 草稿 8 个不计入已完成 proof，其顶层目标已证明并通过路线检查。

## 交付与范围

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_counts_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_counts_migration_proof_manual.v)
- [公共模型和引理](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_counts_migration_lib.v)
- [逐函数和逐区间计量](metrics/effort.json)、[契约/模型审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 验证](metrics/cstar-verification.json)、[QCP 控制器记录](logs/qcp-controller/controller_state.json)、[快照哈希](target/manifest.json)

覆盖表达式左右值计数、参数计数、语句计数、函数序言/整体/前缀计数、函数 PC 以及整个程序的代码/数据长度。文件末尾供后续 emitter 使用的 `cm_concrete_function_ready`、`cm_concrete_functions_ready`、其 getter/export 不在本轮运行时证明依赖闭包，单独列为未迁移支持定义；不能据此宣称整个 CMC/TVM 或编译保持性定理已完成。

## 契约与模型对应

逐函数保留原始纯条件、堆所有权与结果。`cm_expr_counts` 仍输出两个精确计数、类型有效性和编码值界限；语句契约保留循环标志及 return-type 字段。所有计数及子结构的 representability 条件均保留。`cmc_function_pc` 的 `fid <= length` 是闭区间，末尾位置仍合法；prefix 保留 index 与完整列表/后缀长度关系、remaining 及组合上界。`cmc_model_data_length` 中模型长度等于表示尺寸的等式原本就是源前提，目标没有新增该条件。

复用 layout 的统一全称 `cm_lookup_policy`，保留 HOL 越界/负数函数查询语义，不增加源契约没有的 fid 范围。数学定义按 AST/列表结构递归，不引入 runtime 状态解释器替代源规格。类型、作用域、声明次数、frame、stack bound 及数据字节模型直接翻译，`cm_wf_program` 的各个原合取均保留。

**显式参数化边界：** `cm_codegen_fields_representable` 中四项 emitter/TVM 条件保留为全称 `cm_codegen_obligations` 的独立字段；源实例分别是 `tvm_code_shape(cm_model_code p)`、`tvm_targets_valid(cm_model_code p)`、`tvm_patches_valid(cm_model_patches p)` 和 `tvm_target_valid(cm_model_code p, 0)`。本轮证明对这些字段的任意取值成立，并未丢掉原合取。库中的合取对应引理仅是参数化定义恒等式；**尚未提供这些 emitter/TVM 模型的 Rocq 实例化定理，也不是完整 HOL/Rocq 等价证书**。后续迁移 emitter 时应补上具体实例及对应关系。

## Annotation 与 proof 工作量

以最终非空物理行计量，包含语法包装，排除纯注释、独立 `*/` 和自动生成 VC 文本。前向声明重复契约另计；辅助函数接入契约计入 annotation，既有 helper 实现 proof 不重复计。目标规格有很长的单行，因此同时提供词法 token 和字符数；行数不能作为耗时、难度或工具优劣结论。

| 最终规模 | C* | QCP |
|---|---:|---:|
| 15 函数 specification | 426 | 44 |
| 函数体 annotation | 243 | 1020 |
| 既有 helper 契约的接入 annotation | 0（原 include） | 19 |
| annotation 含接入 | 243 | 1039 |
| specification + annotation 含接入 | 669 | 1083 |
| 案例 proof | 3939 | 4807 |
| 文件内原公共 proof／目标新增公共 proof | 375 | 355 |
| proof 合计 | 4314 | 5162 |
| specification 词法 token | 4004 | 3619 |
| 函数体 annotation 词法 token | 5167 | 13490 |

C* 案例 proof = 3651 行内联 + 288 行私有辅助。公开 proof 及共享构造器的去重闭包为 375 行；其中公开但本轮运行时未直接调用的包装仍计原文件成本，清单见 source-effort.json。源文件另有 3 行必要模型 `cm_args_tail_slots`；末尾两项 readiness 模型 43 行、getter 6 行另列，不混入本轮迁移成本。

QCP 案例 proof 含证明体 3232 行、声明/Proof/Qed 等包装 1575 行；不能将全部包装都称为新写 tactic。完整词法指标与标注条目见 [source-text-size.json](metrics/source-text-size.json)、[annotation-entry-counts.json](metrics/annotation-entry-counts.json)。

| 函数 | C* spec | C* ann | C* inline proof | QCP spec | QCP ann | QCP case proof |
|---|---:|---:|---:|---:|---:|---:|
| `cmc_expr_type_code_value` | 6 | 0 | 10 | 3 | 13 | 24 |
| `cm_expr_lvalue_count` | 40 | 9 | 0 | 3 | 1 | 0 |
| `cm_expr_rvalue_count` | 40 | 9 | 0 | 3 | 1 | 0 |
| `cmc_args_code_count` | 44 | 18 | 170 | 3 | 34 | 93 |
| `cm_binding_address_count_value` | 7 | 0 | 32 | 2 | 0 | 33 |
| `cm_expr_counts` | 50 | 105 | 1614 | 3 | 449 | 3111 |
| `cmc_stmt_code_count` | 43 | 95 | 544 | 3 | 287 | 778 |
| `cmc_param_stores_count` | 9 | 0 | 124 | 3 | 12 | 91 |
| `cmc_function_prologue_count` | 15 | 0 | 44 | 3 | 12 | 60 |
| `cmc_function_code_count` | 23 | 7 | 111 | 3 | 32 | 96 |
| `cmc_function_prefix_count` | 42 | 0 | 364 | 3 | 58 | 158 |
| `cmc_function_pc` | 25 | 0 | 67 | 3 | 31 | 68 |
| `cmc_functions_code_size_count` | 38 | 0 | 307 | 3 | 50 | 156 |
| `cmc_model_code_length` | 17 | 0 | 141 | 3 | 25 | 105 |
| `cmc_model_data_length` | 27 | 0 | 123 | 3 | 15 | 34 |

文件级私有辅助和公共闭包不重复摊派到每个函数。

## 新增公共依赖

本轮新增 **91 项定义、255 行；32 条引理、355 行 proof**。新增导入/作用域 11 行，公共自动化/配置 0 行，分别记录。以实际最终合并库计数，不用 controller 候选池大小替代。

直接复用已验证的 `cmc_layout_migration_lib`（AST、descriptor、类型编码、查询策略、安全和堆谓词）及其 `cmc_copy_bytes_migration_lib` 依赖；这些库本轮新增成本为 0。调用 layout 已验证 helper 通过显式契约接入，不重证其实现、不导入其 auto/manual 函数证明。实际依赖编译快照与基线哈希匹配。各新增 helper 的当前引用次数见 [shared-helper-usage.json](metrics/shared-helper-usage.json)；新增但未被 manual 直接引用的支持引理仍计成本，不冒称复用收益。

首轮各组受 round-start frozen 公共快照限制，不能复用同轮后来晋升的候选；若多个组独立新增同义类型编码引理，均按最终库实际产物计入，不做去重减免。这是本轮并行迁移的实际成本，可在后续案例中通过预先准备公共桥接引理改进。

C 层 Extern 声明 152 行、Coq 导入 1 行、前向声明重复契约 3 行另列。源模型依赖清单 [source-model-definitions.json](metrics/source-model-definitions.json) 是 CMC 源文件中已有声明的闭包清单，包含 emitter 参数化边界的源依赖，不代表每个名字都已直接翻译，也不是源库历史开发成本。

## 验证与过程

C* 原源码在隔离副本重放，exit 0，verification_conditions/axioms/strategies 均为空，用时 116.728 秒。QCP 标注验收复用了 owner 的符号执行 receipt，并检查 sealed bytes 与输出新鲜度（该步没有再次运行 symexec）；随后经过依赖准备、独立 VC 审核、分组证明、合并完整检查、final-apply 和 final-check；15 函数均有义务覆盖，手工剩余为 0。所有完整命令、退出结果和重试保存在控制器/源验证日志。

QCP 初始化到 done 墙钟时间 129.73 分钟，包含编写、调度和等待，不能与 C* 成品重放时间比较速度。历史 C* 作者工时、人工活跃时间、无法独立测量的代理活跃时间均为 null。此实验是阅读既有 C* 证明后的迁移，不能视为两套工具从零证明的公平比较。

自动 witness 的 `Admitted` 原样保留并逐名记录；最终结果依赖 QCP 自动推理及现有逻辑基座，不是完全没有信任项的独立内核证书。
