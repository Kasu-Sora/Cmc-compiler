# CMC / TVM：C* → QCP / Rocq 待迁移范围

清点更新：2026-10-19。目标是重建 CMC 具体实现验证、Tower C−/TVM 逻辑模型及编译保持性证明。当前完成 `cmc_write_byte`、`cmc_write_zeroes`、`cmc_copy_bytes`、`cmc_write_word`、`cmc_write_char`、layout 整文件 39 个函数和 counts 的 15 个运行时函数、count-context 的 4 个包装函数、function-pc-total 的 2 个函数、emit-globals 和 emit-strings 的递归函数及 emit-data 组合函数、emit-core 的九个指令生成函数及 emit-resolved、emit-plan 各八个包装函数及 emit-ast 的两个地址生成函数及 emit-expr-leaf 的九个函数及 emit-expr-var、emit-expr-dispatch、emit-expr-simple 各一个函数及 emit-expr-call、emit-binary-finish 各三个函数及 emit-expr 的七个函数，共二十三个具体实现迁移单元的运行时部分、120 个运行时函数的 QCP 流程验证；各案例分别有 2、6、7、37、3、332、184、6、11、9、12、7、83、16、16、14、49、22、28、14、60、127、449 条可信自动 witness 以 `Admitted` 导出，详见 [write_byte 报告](experiments/cmc_write_byte/REPORT.md)、[write_zeroes 报告](experiments/cmc_write_zeroes/REPORT.md)、[copy_bytes 报告](experiments/cmc_copy_bytes/REPORT.md)、[write_word 报告](experiments/cmc_write_word/REPORT.md)、[write_char 报告](experiments/cmc_write_char/REPORT.md)、[layout 报告](experiments/cmc_layout/REPORT.md)、[counts 报告](experiments/cmc_counts/REPORT.md)、[count-context 报告](experiments/cmc_count_context/REPORT.md)、[function-pc-total 报告](experiments/cmc_function_pc_total/REPORT.md)、[emit-globals 报告](experiments/cmc_emit_globals/REPORT.md)、[emit-strings 报告](experiments/cmc_emit_strings/REPORT.md)、[emit-data 报告](experiments/cmc_emit_data/REPORT.md)、[emit-core 报告](experiments/cmc_emit_core/REPORT.md)、[emit-resolved 报告](experiments/cmc_emit_resolved/REPORT.md)、[emit-plan 报告](experiments/cmc_emit_plan/REPORT.md)、[emit-ast 报告](experiments/cmc_emit_ast/REPORT.md)、[emit-expr-leaf 报告](experiments/cmc_emit_expr_leaf/REPORT.md)、[emit-expr-var 报告](experiments/cmc_emit_expr_var/REPORT.md)、[emit-expr-dispatch 报告](experiments/cmc_emit_expr_dispatch/REPORT.md)、[emit-expr-simple 报告](experiments/cmc_emit_expr_simple/REPORT.md)、[emit-expr-call 报告](experiments/cmc_emit_expr_call/REPORT.md)、[emit-binary-finish 报告](experiments/cmc_emit_binary_finish/REPORT.md)、[emit-expr 报告](experiments/cmc_emit_expr/REPORT.md)。

[migration_inventory.csv](migration_inventory.csv) 逐项列出 `/Users/nizitong/cmc` 根目录全部 254 个 `.c` 文件、249 个存在的同名头文件、类别、迁移状态、直接依赖和源码哈希。

从 `cmc.c` 同时沿本地 `#include`、`#require` 扫描，覆盖 253 个根目录 `.c`；只有 `tasm_model.c` 不在该静态闭包。该数字包含示例和辅助逻辑，且未裁剪条件编译或未使用定理，因此不能等同于待独立验证的 C 程序数量。头文件也可能包含 `#require`，仅扫描 `.c` 会漏掉 `cmc_concrete_emit_core.c`。

## 迁移方式

- 普通 C 函数：保持运行行为，将契约和标注转换为 QCP，生成义务并验证；头文件中的类型与调用契约同步处理。
- `PROOF` 数学定义、引理、操作语义和模拟关系：重建为 Rocq 定义与定理。它们虽然存放在 `.c` 中，却不是应交给 QCP 作为运行时代码验证的程序。
- 混合文件：拆分实现、逻辑模型与证明，不要求维持一源文件对应一目标文件。
- 现有 QCP/Rocq 库已提供同义内容时优先复用；新定义和公共引理成本单独统计。不要翻译 HOL 证明 API 本身。

## 建议分批顺序

| 批次 | 源文件/文件组 | 目标交付与验收重点 |
|---|---|---|
| 已完成 | `cmc_concrete_emit_bytes.c` | `cmc_write_byte` 的字节前缀/未初始化后缀契约；保留自动结果信任说明 |
| 已完成 | `cmc_concrete_emit_zeroes.c` | `cmc_write_zeroes` 的原契约、循环及重复列表；3 条手工义务完成，6 条可信自动结果；新增公共引理单列 |
| 已完成 | `cmc_concrete_copy_bytes.c` | 源数组保持、空缓冲区、精确复制前缀；4 条手工义务完成，7 条可信自动结果；新增纯定义 2 行 |
| 已完成 | `cmc_concrete_emit_word.c` | 全 signed64 输入及原小端编码契约；15 条手工义务、37 条可信自动结果；新增 3 个定义和 3 条公共引理 |
| 已完成 | `cmc_concrete_emit_char.c` | 原低字节契约及全部 signed64 输入；1 条手工义务、3 条可信自动结果；实际复用 word 公共库，新增定义／引理均为 0 |
| 已完成 | `cmc_concrete_layout.c` | 全部 39 个运行时函数；148 条手工义务、234 个 split、332 条可信自动结果；新增 96 项定义和 17 条公共引理，复用 copy-bytes 纯定义 |
| 已完成运行时部分 | `cmc_concrete_counts.c` | 15 个函数；150 条手工义务、375 个 split、184 条可信自动结果；readiness 定义已在 function-pc-total 中补齐计数形式，emitter 桥接待迁移，四项 TVM 条件保留参数化边界 |
| 已完成 | `cmc_concrete_count_context.c` | 四个包装函数；8 条手工义务、4 个 split、6 条可信自动结果；复用 counts/layout/copy-bytes，公共定义新增 0 项、引理 0 条 |
| 已完成 | `cmc_concrete_function_pc_total.c` | 两个函数；12 条手工义务、16 个 split、11 条可信自动结果；保留任意 target，新增公共定义 5 项、引理 8 条 |
| 3：表示与尺寸的剩余部分 | `cmc_abi.c/.h`、`cmc_rep.c/.h`、`cmc_concrete_defs.c/.h`中尚未迁移的定义与引理 | 复用 layout 已迁移的必要模型/表示闭包；尚未覆盖的定义、计数和上下文计算仍须逐项迁移 |
| 已完成 | `cmc_concrete_emit_globals.c` | 递归生成精确全局字节；9 条手工义务、8 个 split、9 条可信自动结果；新增公共定义 1 项、引理 9 条 |
| 已完成 | `cmc_concrete_emit_strings.c` | 原字符串字节和零终止输出、源数组保持；3 条手工义务、4 个 split、12 条可信自动结果；新增公共定义 0 项、引理 0 条 |
| 已完成 | `cmc_concrete_emit_data.c` | 八个零字节、globals、strings 的精确组合；4 条手工义务、5 个 split、7 条可信自动结果；新增公共定义 0 项、引理 0 条 |
| 已完成 | `cmc_concrete_emit_core.c` | 九个指令生成函数；50 条手工义务、54 个 split、83 条可信自动结果；新增公共定义 16 项、引理 4 条 |
| 已完成 | `cmc_concrete_emit_resolved.c` | 八个 resolved 包装函数；16 条手工义务、8 个 split、16 条可信自动结果；新增公共定义 3 项、引理 10 条 |
| 已完成 | `cmc_concrete_emit_plan.c` | 八个计划包装函数；16 条手工义务、32 个 split、16 条可信自动结果；新增公共定义 1 项、引理 1 条 |
| 已完成 | `cmc_concrete_emit_ast.c` | 两个绑定地址函数；9 条手工义务、14 个 split、14 条可信自动结果；新增公共定义 7 项、引理 2 条 |
| 已完成 | `cmc_concrete_emit_expr_leaf.c` | 九个运行时函数（含两个static helper）；27条手工义务、37个split、49条可信自动结果；新增公共定义10项、引理14条；保留实现契约并披露const头文件差异 |
| 已完成 | `cmc_concrete_emit_expr_var.c` | 一个变量表达式生成函数；9 条手工义务、9 个 split、22 条可信自动结果；新增公共定义 3 项、引理 1 条 |
| 已完成 | `cmc_concrete_emit_expr_dispatch.c` | 一个叶子表达式分派函数；13 条手工义务、8 个 split、28 条可信自动结果；新增公共定义 1 项、引理 2 条 |
| 已完成 | `cmc_concrete_emit_expr_simple.c` | 一个简单表达式生成函数；7 条手工义务、4 个 split、14 条可信自动结果；新增公共定义 4 项、引理 2 条 |
| 已完成模块化验证 | `cmc_concrete_emit_expr_call.c` | 三个运行时函数；21 条手工义务、43 个 split、60 条可信自动结果；新增公共定义 12 项、引理 10 条；通用 cm_emit_expr 实现已由 emit-expr 案例补齐 |
| 已完成 | `cmc_concrete_emit_binary_finish.c` | 三个运行时函数；40 条手工义务、59 个 split、127 条可信自动结果；复用 binary-finish/scale 模型；新增公共定义 0 项、引理 0 条 |
| 已完成 | `cmc_concrete_emit_expr.c` | 七个运行时函数；176 条手工义务、333 个 split、449 条可信自动结果；补齐 call 的通用表达式实现依赖；新增公共定义 8 项、引理 23 条 |
| 5：指令与程序生成 | `cmc_concrete_emit_return.c`、`cmc_concrete_emit_stmt*.c`、`cmc_concrete_emit_function*.c`、`cmc_concrete_emit_prelude.c`、`cmc_concrete_emit_code.c`、`cmc_concrete_patch_calls.c` | 指令列表与实际缓冲区一致；表达式/语句/调用的递归验证；跳转地址和回填 |
| 贯穿各批：模型和支持引理 | `tower_base.c`、`cmc_lang.c`、`tvm_model.c`、`cmc_codegen.c`、`cmc_sim*.c`、`cmc_annotate*.c`、`cmc_stack*.c`、`cmc_temp_algebra.c`、`cmc_list_selectors.c`、`cmc_concrete_*ready.c`、`cmc_concrete_emit_stmt_proof.c` | 在 Rocq 重建各案例实际需要的定义和定理，逐渐覆盖完整源/目标语义和代码生成模型 |
| 6：编译保持性 | `cmc_preservation_*.c`、`cmc_correct.c` | 在 Rocq 重建模拟不变式、执行保持、调用/返回、类型与栈条件，得到同样前提下的终止观察保持与无目标错误结论 |
| 7：顶层组合 | `cmc.c`、`cmc.h` | QCP 验证 `cmc_compile`；把模型保持性与具体输出解码连接起来，恢复成功/容量不足的完整契约 |
| 回归 | `cmc_examples.c`、`cmc_examples_calls.c`、`cmc_examples_conversion.c`、`cmc_examples_struct.c` | 检查迁移后的模型与定理对现有示例的适用性；示例不能代替一般保持性证明 |

表中批次是增量推进路线，不是严格的全部文件拓扑顺序。模型和表示层应按每个案例所需的依赖提前迁移。完整文件名以 CSV 为准。

## 规模与不必逐字迁移的内容

- `cmc_concrete_*.c` 共 38 个文件，混合普通实现与支持证明；已验证的运行时部分见上表。必要模型闭包已进入目标公共库，源模型文件其余内容尚未全量迁移。
- `cmc_preservation_*.c` 共 188 个文件，主要是证明模块。应按实际定理依赖在 Rocq 中组织，可以合并或复用等价库，不要求保留 188 个目标文件。
- `/Users/nizitong/cmc/userlib/` 中被加载的数组、列表及证明工具，应区分可复用数学内容与 HOL 特定证明构造 API。只迁移目标缺少且确实用到的内容，不能把所有工具代码算成公共迁移量。
- `proof/` 是 C* 证明基础库，不作为本项目重新实现 HOL 的任务。
- `tasm_model.c/.h` 是独立汇编器解析后模型与 resolver 证明。CMC 直接生成 resolved TVM object，不依赖该 resolver；当前范围可排除。
- `tvm_model.c` 是逻辑模型，覆盖加载、状态、28 条指令转换及执行结果；它不是一个待验证的普通 C VM 解释器。若要验证独立解释器，还需另行提供其源码。
- `_verif/`、生成日志及旧 `arr_sum` 反方向实验不属于迁移源。

## 推荐下一单元

五个基础写入/复制实现、layout、counts、count-context、function-pc-total、emit-globals、emit-strings、emit-data、emit-core、emit-resolved、emit-plan、emit-ast、emit-expr-leaf、emit-expr-var、emit-expr-dispatch、emit-expr-simple、emit-expr-call、emit-binary-finish 与 emit-expr 的运行时部分已完成模块化验证，call 的通用表达式实现依赖已补齐。下一候选为 `cmc_concrete_emit_return.c`；开始前仍须审查其完整依赖闭包。继续复用已验证公共库，新增成本单列；已迁移的一般表达式代码模型及代码长度／count 定理在本轮直接复用，完整指令 emitter 的其余语义、readiness 桥及具体 TVM 实例化仍待后续迁移。

每个单元均记录 source/target 契约、annotation、手写 proof、自动结果信任项及新增公共工作。必须分别验证普通 helper 函数体；仅让顶层 `cmc_compile` 通过，不能替代其所调用 helper 的实现验证。
