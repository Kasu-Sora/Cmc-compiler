---
name: qcp-cstar-migration
description: 在 C*（HOL）与 QCP（Rocq/Coq）之间迁移 C 程序规约、标注和证明，比较 annotation/proof 成本并单列公共依赖。用于跨体系证明迁移，包括 CMC/TVM 证明向 QCP/Rocq 的迁移；区分实现验证、逻辑模型和编译保持性定理。
---

# QCP ↔ C* 证明迁移

## 确定范围

确认迁移方向、准确的源函数、要保持的性质及目标验证工具版本。先从会话和仓库推断，缺失且影响正确性时再询问。若仅请求分析，输出映射与工作计划，不把分析说成验证通过。

以用户最后澄清的方向为准。本机 CMC 项目的当前方向是 **C* → QCP**，源是 `/Users/nizitong/cmc`，目标是 QCP 标注 C 与 Rocq 证明。不要因为用户提供了 QCP 仓库就把其中示例当作迁移源。原 `arr_sum` 反方向实验已被用户弃用，不作为当前候选或迁移模板。

区分 C* 验证的 C 实现、CMC 编译器本身的证明、CMC 的 Tower C− 输入程序三层。迁移到 C* 不等于已经证明对应 Tower C− 程序正确，也不自动获得 TVM 层面的保证。

读取作用域内的 AGENTS.md。QCP 仓库若要求 verification-orchestrator，实际开展其单个 C 验证任务时按该入口及其必读文档执行；本 skill 不替代其 controller 或角色分工。只读案例分析不启动验证 run。实际命令必须来自本机工具文档、帮助或仓库流程，不能假设存在统一的迁移命令。

## 固定基线

- 记录源/目标版本、源文件哈希、工作树状态和验证命令。以用户选定的函数或整个文件为单位，明确其依赖闭包。请求整文件时清点所有运行时函数及前向声明，不能缩减为少数 helper；仅请求单函数时不把无关函数一起计入。
- 在隔离的实验目录保存输入快照与目标产物；不要改写参考答案。要变更基准代码或契约时记录原因并保留原版。
- 建立语义对照：整数宽度及溢出、char 符号性、指针和别名、结构体布局、求值顺序、库函数契约、终止性，以及前后置条件中的资源与纯事实。
- 默认保持运行时代码与契约含义。必要的代码改写单独列 diff；不能为减少 VC 而削弱后置条件、增强输入前提或删除安全条件。
- 按 references/effort.md 建立计量记录。已有基线的历史耗时未知时记录 null，不估造。

## 迁移过程

1. **契约映射**：建立原定义/新定义/含义/依赖/验证状态表。区分自然语言规格、数学模型、堆表示、函数契约、循环不变式和证明脚本。
2. **数学层**：先迁移用到的整数、列表、集合与递归函数及辅助引理。Coq 的 Z、nat、Prop 与 HOL 的相应类型需要检查语义；保留关键定理陈述，不能把同名库函数当成相同定义。
3. **内存层**：核对数组长度和元素宽度、结构体字段、所有权、初始化及别名约束。重建表示谓词和拆分/合并引理。
4. **标注层**：迁移逻辑参数、前后置条件、不变式及中间断言。QCP With/Require/Ensure/Inv 与 C* param/require/ensure/invariant 是概念对应，不是字符串替换。C* 不变式需按其引擎规则保留所需局部内存和事实；反向迁移也检查 QCP 的实际保留规则。
5. **证明层**：由目标工具重新生成义务，按数学意义匹配旧证明思路。Coq 的 lia/rewrite/cancel 与 C* 的推理 API/证明块不作机械替换。优先重建可复用引理，再证明案例义务。
6. **验证与审计**：运行目标完整检查；核对函数体是否实际被验证，不能仅检查导入或契约声明。记录未解决 VC、假定规约、新增公理与自动化信任边界。检查通过后再总结工作量。

纯 `PROOF` 支持文件没有运行时函数时，按数学库交付并记录 Rocq 编译、内核检查、定理签名和实际假设；不制造 C wrapper 或把纯证明模块计入运行时函数数。已有定义直接复用，核验完成与新增成本分开记录。

QCP 导出的 proof_auto 中可能使用 Admitted 表示自动求解器结果。应检查本案例文件及其验证模型，不把它一概认定为未完成手工任务，也不当成 Coq 内核检查过的证明。在 C* 目标中重新证明对应义务，或明确保留的信任差异；不得静默用公理替代证明。反向迁移要分别报告 QCP 自动结果和内核检查的手工结果。

## 双向与 CMC 扩展

QCP → C* 和 C* → QCP 共用以上阶段，但各自重新生成和完成目标义务。方向经验分开记录；只做过单向案例时不声称双向验证成熟。测试反向迁移时不要复制已知目标答案；使用隔离目录并记录可见的参考资料。回译一致性不等于独立的公平效率实验。

先区分两种 CMC/TVM 请求。若迁移编译器本身的证明，分别迁移 HOL 数学定义与操作语义到 Rocq、具体 C 实现的契约到 QCP、模拟关系和保持性定理到 Rocq，并重建模型输出与具体缓冲区的连接。`tvm_model.c` 是逻辑模型，不自动等于一个待验证的普通 C 解释器；解释器实现需要单独确定源码。

若仅应用已有编译正确性结果到一个输入程序，则构造合法 `cm_program`、证明所需合法性和源程序成功终止条件，再应用保持性定理。保留原有 admissibility 前提，包括模型生成代码的目标有效性条件；公开保证针对输入/输出/退出状态，不能扩大为任意堆断言、双向行为等价或发散保持。额外工作单独计量。

## 交付与验收

交付源/目标路径、原性质及目标对应、必要改写、验证日志、信任差异、工作量统计与已知限制。把“草稿”“语法通过”“部分义务完成”“完整验证通过”明确区分。

成功标准：目标证明通过其完整检查，规格含义和语义差异已经交代，新增假设和所有未完成义务已披露，计量可追溯。环境缺失时保存现有产物和准确诊断，不将缺少输出解释为通过。

## 本机会话的参考材料

使用本机资料时先检查是否仍存在：

- QCP 工具仓库：`/Users/nizitong/QCP/qcp-binary-democases`；实际验证入口为其 `AGENTS.md`。
- 当前已验证案例：CMC 的 `cmc_write_byte`、`cmc_write_zeroes`、`cmc_copy_bytes`、`cmc_write_word`、`cmc_write_char`，以及整个 layout 文件的 39 个函数、counts 的 15 个运行时函数、count-context 的 4 个包装函数、function-pc-total 的 2 个函数、emit-globals 和 emit-strings 的递归函数及 emit-data 的组合函数、emit-core 的九个指令生成函数、emit-resolved 与 emit-plan 各八个包装函数及 emit-ast 的两个地址生成函数及 emit-expr-leaf 的九个函数（含两个 static helper）及 emit-expr-var、emit-expr-dispatch、emit-expr-simple 各一个函数及 emit-expr-call、emit-binary-finish 各三个函数及 emit-expr 的七个函数及 emit-return 的一个函数及 emit-stmt 的两个函数（含必要 stmt proof 支持）及 emit-function 的三个函数（含必要 function proof 支持）及 emit-functions 的一个函数（含必要 proof 支持）及 emit-prelude、emit-code 各一个函数及 patch-calls 的两个函数；QCP 正式文件在 `QCP_examples/QCP_demos_human/`，前五例文件名为函数名加 `_migration.c`，layout 为 `cmc_layout_migration.c`，counts 为 `cmc_counts_migration.c`，count-context 为 `cmc_count_context_migration.c`，function-pc-total 为 `cmc_function_pc_total_migration.c`，emit-globals 为 `cmc_emit_globals_migration.c`，emit-strings 为 `cmc_emit_strings_migration.c`，emit-data 为 `cmc_emit_data_migration.c`，emit-core 为 `cmc_emit_core_migration.c`，emit-resolved 为 `cmc_emit_resolved_migration.c`，emit-plan 为 `cmc_emit_plan_migration.c`，emit-ast 为 `cmc_emit_ast_migration.c`，emit-expr-leaf 为 `cmc_emit_expr_leaf_migration.c`，emit-expr-var 为 `cmc_emit_expr_var_migration.c`，emit-expr-dispatch 为 `cmc_emit_expr_dispatch_migration.c`，emit-expr-simple 为 `cmc_emit_expr_simple_migration.c`，emit-expr-call 为 `cmc_emit_expr_call_migration.c`，emit-binary-finish 为 `cmc_emit_binary_finish_migration.c`，emit-expr 为 `cmc_emit_expr_migration.c`，emit-return 为 `cmc_emit_return_migration.c`，emit-stmt 为 `cmc_emit_stmt_migration.c`，emit-function 为 `cmc_emit_function_migration.c`，emit-functions 为 `cmc_emit_functions_migration.c`，emit-prelude 为 `cmc_emit_prelude_migration.c`，emit-code 为 `cmc_emit_code_migration.c`，patch-calls 为 `cmc_patch_calls_migration.c`。
- 基准：`/Users/nizitong/QCP/PV-bench`；信任说明为 `docs/VERIFICATION.md`。
- C* 源案例：`/Users/nizitong/cmc/cmc_concrete_emit_bytes.c`；CMC 保证范围为 `CMC_SPEC.md`。

## 已验证案例

C* → QCP 的 `cmc_write_byte` 于 2026-10-15 完成 controller 全流程，最终 `done`；原 C* 证明也重放通过。处理 unsigned-byte 数组片段、QCP 自动结果或本例计量时，读取 [references/cmc-write-byte-case.md](references/cmc-write-byte-case.md)。本例 QCP 两条自动结果以 `Admitted` 导出，不能称为全部义务均有独立 Rocq 内核证明证书。

`cmc_write_zeroes` 同日完成完整验证及公共引理的补充独立检查。涉及数组循环、整数长度重复列表、共享引理可见性或编译闭包时，读取 [references/cmc-write-zeroes-case.md](references/cmc-write-zeroes-case.md)。本例完成 3 条顶层手工义务，另有 6 条可信自动结果；公共引理虽已独立验证，目前未被案例 manual 引用，计量时单独列成本。

`cmc_copy_bytes` 同日完成完整验证。处理可为空的缓冲区、源数组保持、复制前缀、QCP @pre 分支歧义及私有辅助证明计量时，读取 [references/cmc-copy-bytes-case.md](references/cmc-copy-bytes-case.md)。本例新增一个两行纯定义，未新增公共引理；4 条顶层手工义务完成，另有 7 条可信自动结果。

`cmc_write_word` 同日完成完整验证。处理 signed/unsigned 64 位转换、负数的字节编码、C 的 quot/rem 与数学 div/mod、连续 helper 调用及公共桥接计量时，读取 [references/cmc-write-word-case.md](references/cmc-write-word-case.md)。本例新增 3 个定义和 3 条实际使用的公共引理，15 条顶层手工义务完成，另有 37 条可信自动结果。

`cmc_write_char` 同日完成完整验证，并实际复用 word 的公共模型与桥接引理，公共定义和 proof 新增均为 0。处理跨案例库复用、低字节截取、absent case-lib 和增量计量时，读取 [references/cmc-write-char-case.md](references/cmc-write-char-case.md)。本例完成 1 条顶层手工义务，另有 3 条可信自动结果。

`cmc_concrete_layout.c` 同日完成整文件 39 个运行时函数的验证。涉及 AST／链表递归、总列表查询的未指定行为、整文件覆盖或共享模型计量时，读取 [references/cmc-layout-case.md](references/cmc-layout-case.md)。本例完成 148 条顶层手工义务及 234 个 split，另有 332 条可信自动结果；新增 96 项定义和 17 条公共引理，实际复用 copy-bytes 的纯定义库。

`cmc_concrete_counts.c` 于 2026-10-16 完成 15 个运行时函数的验证。处理精确计数、上下文表示、无关 codegen 条件的显式参数化、冻结公共库下的复用或增量计量时，读取 [references/cmc-counts-case.md](references/cmc-counts-case.md)。本例完成 150 条顶层手工义务、375 个 split，另有 184 条可信自动结果；新增 91 项定义和 32 条公共引理。当时未迁移的 readiness 定义已在 function-pc-total 案例中补齐计数形式；emit-core 的基础指令片段与双数组表示已迁移；完整 emitter 语义及 readiness 桥仍待迁移。

`cmc_concrete_count_context.c` 随后自动推进并完成四个包装函数验证。涉及完整上下文开合、helper 契约接入、where 存在量见证范围和已有库增量复用时，读取 [references/cmc-count-context-case.md](references/cmc-count-context-case.md)。本例完成 8 条顶层手工义务、4 个 split，另有 6 条可信自动结果；新增公共定义 0 项、引理 0 条。

`cmc_concrete_function_pc_total.c` 于 2026-10-16 完成两个函数验证。涉及任意 target 的总前缀查询、无条件长度界和完整 readiness 归一化时，读取 [references/cmc-function-pc-total-case.md](references/cmc-function-pc-total-case.md)。本例完成 12 条顶层手工义务、16 个 split，另有 11 条可信自动结果；新增公共定义 5 项、引理 8 条。

`cmc_concrete_emit_globals.c` 于 2026-10-16 完成递归全局数据区生成验证。涉及精确字节输出、初始化分支、语义/表示大小桥及跨库字节编码一致性时，读取 [references/cmc-emit-globals-case.md](references/cmc-emit-globals-case.md)。本例完成 9 条顶层手工义务、8 个 split，另有 9 条可信自动结果；新增公共定义 1 项、引理 9 条。

`cmc_concrete_emit_strings.c` 于 2026-10-16 完成递归字符串数据区生成验证。涉及空字符串、源数组保持、零终止字节和跨 helper 表示转换时，读取 [references/cmc-emit-strings-case.md](references/cmc-emit-strings-case.md)。本例完成 3 条顶层手工义务、4 个 split，另有 12 条可信自动结果；新增公共定义 0 项、引理 0 条。

`cmc_concrete_emit_data.c` 于 2026-10-16 完成数据区组合函数验证。涉及 helper 串联、资源端点/字节列表归一化和完整后置纯事实保留时，读取 [references/cmc-emit-data-case.md](references/cmc-emit-data-case.md)。本例完成 4 条顶层手工义务、5 个 split，另有 7 条可信自动结果；新增公共定义 0 项、引理 0 条。

`cmc_concrete_emit_core.c` 于 2026-10-17 完成全部九个运行时函数验证。涉及 TVM 指令片段、双数组 emitter 表示、分支事实保留、任意 int 默认映射和临时槽偏移桥时，读取 [references/cmc-emit-core-case.md](references/cmc-emit-core-case.md)。本例完成 50 条顶层手工义务、54 个 split，另有 83 条可信自动结果；新增公共定义 16 项、引理 4 条。

`cmc_concrete_emit_resolved.c` 于 2026-10-17 完成八个包装函数验证。涉及 raw 缓冲区与 resolved 逻辑视图、CALL 编号的总映射、patch 长度/拼接和 core 契约复用时，读取 [references/cmc-emit-resolved-case.md](references/cmc-emit-resolved-case.md)。本例完成 16 条顶层手工义务、8 个 split，另有 16 条可信自动结果；新增公共定义 3 项、引理 10 条。

`cmc_concrete_emit_plan.c` 于 2026-10-17 完成八个计划包装函数验证。涉及 resolved 计划容量、任意 tail、片段消费/追加及模块调用后预算恢复时，读取 [references/cmc-emit-plan-case.md](references/cmc-emit-plan-case.md)。本例完成 16 条顶层手工义务、32 个 split，另有 16 条可信自动结果；新增公共定义 1 项、引理 1 条。

`cmc_concrete_emit_ast.c` 于 2026-10-17 完成两个地址生成函数验证。涉及绑定地址、整数索引前缀、布局/语义偏移桥及双上下文保持时，读取 [references/cmc-emit-ast-case.md](references/cmc-emit-ast-case.md)。本例完成 9 条顶层手工义务、14 个 split，另有 14 条可信自动结果；新增公共定义 7 项、引理 2 条。

`cmc_concrete_emit_expr_leaf.c` 于2026-10-17完成九个运行时函数验证。涉及leaf模型特化、static helper覆盖、声明/实现契约差异、结构体大小和成员偏移桥时，读取 [references/cmc-emit-expr-leaf-case.md](references/cmc-emit-expr-leaf-case.md)。本例完成27条顶层手工义务、37个split，另有49条可信自动结果；新增公共定义10项、引理14条。

`cmc_concrete_emit_expr_var.c` 于 2026-10-17 完成唯一运行时函数验证。涉及变量左/右值、数组判定、地址与加载计划组合及上下文恢复时，读取 [references/cmc-emit-expr-var-case.md](references/cmc-emit-expr-var-case.md)。本例完成 9 条顶层手工义务、9 个 split，另有 22 条可信自动结果；新增公共定义 3 项、引理 1 条。

`cmc_concrete_emit_expr_dispatch.c` 于 2026-10-17 完成唯一运行时函数验证。涉及叶子 kind 分派、表示见证覆盖、helper 前提派生及完整上下文保持时，读取 [references/cmc-emit-expr-dispatch-case.md](references/cmc-emit-expr-dispatch-case.md)。本例完成 13 条顶层手工义务、8 个 split，另有 28 条可信自动结果；新增公共定义 1 项、引理 2 条。

`cmc_concrete_emit_expr_simple.c` 于 2026-10-18 完成唯一运行时函数验证。涉及 leaf/var 视图组合、域覆盖与已有 helper 接入时，读取 [references/cmc-emit-expr-simple-case.md](references/cmc-emit-expr-simple-case.md)。本例完成 7 条顶层手工义务、4 个 split，另有 14 条可信自动结果；新增公共定义 4 项、引理 2 条。

`cmc_concrete_emit_expr_call.c` 于 2026-10-18 完成三个运行时函数的模块化验证。涉及任意表达式参数、嵌套递归代码模型、临时槽和参数链表恢复时，读取 [references/cmc-emit-expr-call-case.md](references/cmc-emit-expr-call-case.md)。本例完成 21 条顶层手工义务、43 个 split，另有 60 条可信自动结果；新增公共定义 12 项、引理 10 条。通用 `cm_emit_expr` 的原外部契约保留，其实现规约已由后续 emit-expr 案例验证并核对契约衔接。

`cmc_concrete_emit_binary_finish.c` 于 2026-10-18 完成三个运行时函数验证。涉及指针缩放、任意二元 op、类型编码衔接及 opaque 计划分支匹配时，读取 [references/cmc-emit-binary-finish-case.md](references/cmc-emit-binary-finish-case.md)。完成 40 条顶层手工义务、59 个 split，另有 127 条可信自动结果；新增公共定义 0 项、引理 0 条。

`cmc_concrete_emit_expr.c` 于 2026-10-19 完成七个运行时函数验证。涉及通用表达式递归、短路跳转、PC/临时槽界和相互递归模块契约衔接时，读取 [references/cmc-emit-expr-case.md](references/cmc-emit-expr-case.md)。完成 176 条顶层手工义务、333 个 split，另有 449 条可信自动结果；新增公共定义 8 项、引理 23 条。

`cmc_concrete_emit_return.c` 于 2026-10-19 完成唯一运行时函数验证。涉及固定指令片段、命名列表展开、逐调用计划与前缀重结合时，读取 [references/cmc-emit-return-case.md](references/cmc-emit-return-case.md)。完成 2 条顶层手工义务、10 个 split，另有 24 条可信自动结果；新增公共定义 1 项、引理 0 条。

`cmc_concrete_emit_stmt.c` 于 2026-10-19 完成两个运行时函数及必要 stmt proof 支持验证。涉及语句互递归、if/while 跳转、构造子投影、局部资源开闭及增量计量时，读取 [references/cmc-emit-stmt-case.md](references/cmc-emit-stmt-case.md)。完成 120 条顶层手工义务、296 个 split，另有 224 条可信自动结果；新增公共定义 4 项、引理 4 条。

`cmc_concrete_emit_function.c` 于 2026-10-19 完成三个运行时函数及必要 function proof 支持验证。涉及参数反向发射、prefix/offset 关系、序言栈帧与完整函数组合时，读取 [references/cmc-emit-function-case.md](references/cmc-emit-function-case.md)。完成 41 条顶层手工义务、84 个 split，另有 106 条可信自动结果；新增公共定义 5 项、引理 3 条。

`cmc_concrete_emit_functions.c` 于 2026-10-19 完成唯一运行时函数及必要 proof 支持验证。涉及函数列表递归、readiness 展开、函数 PC 推进、链表资源恢复及单函数发射复用时，读取 [references/cmc-emit-functions-case.md](references/cmc-emit-functions-case.md)。完成 12 条顶层手工义务、29 个 split，另有 20 条可信自动结果；新增公共定义 2 项、引理 0 条。

`cmc_concrete_emit_prelude.c` 于 2026-10-19 完成唯一运行时函数及必要 proof 支持验证。涉及固定序列计划展开、程序上下文保持、任意 main_id 的总 PC 查询及无额外合法性前提时，读取 [references/cmc-emit-prelude-case.md](references/cmc-emit-prelude-case.md)。完成 3 条顶层手工义务、7 个 split，另有 41 条可信自动结果；新增公共定义 1 项、引理 0 条。

`cmc_concrete_emit_code.c` 于 2026-10-19 完成唯一运行时函数及必要 proof 支持验证。涉及 prelude/functions 组合、PC-zero 桥、完整资源及纯事实保持时，读取 [references/cmc-emit-code-case.md](references/cmc-emit-code-case.md)。完成 3 条顶层手工义务、3 个 split，另有 5 条可信自动结果；新增公共定义 1 项、引理 0 条。

`cmc_concrete_patch_calls.c` 于 2026-10-19 完成两个运行时函数及必要 proof 支持验证。涉及双数组递归、CALL immediate 总查询、数组头尾拆并及 resolved 逻辑视图实体化时，读取 [references/cmc-patch-calls-case.md](references/cmc-patch-calls-case.md)。完成 6 条顶层手工义务、4 个 split，另有 14 条可信自动结果；新增公共定义 2 项、引理 2 条。

`cmc_concrete_data_ready.c` 与 `cmc_concrete_program_ready.c` 于 2026-10-19 完成两个纯支持单元。前者完整复用既有定义；后者新增 1 项定义、9 条内核核验且无公理依赖的定理。涉及 typed → data-ready、原始容量界、实际字节长度或纯证明模块计量时，读取 [references/cmc-data-readiness-case.md](references/cmc-data-readiness-case.md)。这两个支持单元不增加运行时函数数。

`cmc_concrete_code_ready.c` 于 2026-10-19 完成纯支持迁移。复用既有 structs-ready 定义，新增 6 条定理、63 行 proof，均经内核核验且无公理依赖；额外公共依赖新增成本为 0。处理 getter 导出的 static 定理、成员尺寸三种表示的桥接、1048576 上界或递归结构体环境时，读取 [references/cmc-code-readiness-case.md](references/cmc-code-readiness-case.md)。readiness 纯支持累计完成 data_ready、program_ready、code_ready 三项，运行时函数总数不变。

`cmc_concrete_temp_ready.c` 于 2026-10-19 完成纯支持迁移。保留四条公开定理，新增目标定理共 13 条、146 行 proof，全部经内核核验且无公理依赖；新增定义与额外公共依赖成本为 0。处理计数到临时槽安全、嵌套表达式／参数列表递归、严格尾部界或 stmt 临时槽界时，读取 [references/cmc-temp-readiness-case.md](references/cmc-temp-readiness-case.md)。readiness 纯支持累计四项，运行时函数总数不变。

这些结果覆盖三十个具体实现迁移单元的运行时部分、131 个运行时函数及必要依赖；不能外推为整个 CMC/TVM 证明已完成迁移。新的函数、其他数据结构和不同方向仍需各自验证。
