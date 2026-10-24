# cmc_compile 逐步模拟支持：第二批验证记录

本批 8 个公共模块已通过 Rocq 编译、独立 coqchk 和 67 条逐项假设审计，并已接入 QCP 正式库。**完整逐步模拟、cmc_preservation、原签名的 cmc_compile_success_bridge 和顶层 C 验证尚未完成；skill 未更新。**

已完成：

- 按原 C* 有限方程表迁移 cm_update_r/l/s/v/c 的 85 个构造分支，以及 annotation_step、annotated_step/iter。显式保留 HOL 的 HD [] 解释参数，未用固定默认值消除非法分支。逐条映射保存在 metrics/update-equations.json；生成脚本遇到未覆盖语法会失败。
- 证明五类更新的栈擦除和根约束保持、annotation_step 的保持，以及任意步数迭代的源执行对应、擦除、根约束和成功性。这里只闭合了原 18 项不变量中的四个分量（成功性、擦除、根约束、坐标），完整合取尚未迁移。
- 补齐任意整数的八字节编码/解码、word 写后读、写入不相交字节范围不改变 word、存储后旧/新指针来源标记的数值模拟。沿用既有初始化字节模拟，未增加顶层输入条件。
- 迁移代码片段位置谓词及拼接/嵌套/头指令查找，连接实际 TVM 单步执行；验证 push/pop/load/store 四类基础步骤。
- 证明循环/调用坐标不变量的 initial/step/iter，保留临时槽、父游标以及 break/continue 目标之间的原始关系。
- 完成从“已证明不变量”到终止观察的组合引理，以及模型终止到解码对象终止的组合引理。初始化、逐步保持和模拟投影仍是这些通用引理的显式参数；**它们不是已证明的 cmc_preservation，也没有作为 cmc_compile 的 Require 使用。**

新增公共工作量按非空非注释物理行计；Proof 包含引理陈述和 Proof/Qed，以及局部 Ltac 自动化。定义与 proof 分列；生成的检查文件、回归和 Python 工具不计入公共 proof。85 个模型分支由保留的脚本转写，其最终定义仍全计入定义规模，不能将物理行数当成人工耗时。

| 本批公共模块 | 定义 | 引理 | 定义行 | Proof 行 |
|---|---:|---:|---:|---:|
| `cmc_annotation_execution_migration_lib.v` | 7 | 7 | 22 | 14 |
| `cmc_annotation_helpers_migration_lib.v` | 30 | 7 | 67 | 14 |
| `cmc_annotation_invariant_migration_lib.v` | 0 | 13 | 0 | 94 |
| `cmc_annotation_updates_migration_lib.v` | 5 | 0 | 180 | 0 |
| `cmc_simulation_code_migration_lib.v` | 1 | 16 | 1 | 51 |
| `cmc_simulation_composition_migration_lib.v` | 0 | 6 | 0 | 50 |
| `cmc_simulation_coordinate_migration_lib.v` | 7 | 9 | 23 | 74 |
| `cmc_simulation_memory_migration_lib.v` | 0 | 9 | 0 | 78 |

本批增量：50 项定义、67 条引理；定义 293 行，proof 375 行（引理 349 + 7 个 Ltac 共 26 行）。此前 9 个公共模块原样复用，新增源码成本为 0。两批累计 326 项定义、175 条引理，定义 1362 行、proof 745 行。最终依赖闭包仍未完成，最终成本和比率保持 null。

C* 顶层既有规模不变：specification 12 行、annotation 2 行/2 条、案例 proof 499 行、成功桥接 proof 42 行另列；完整外部保持性依赖成本尚未完成。metrics/source-reference-cost.json 给出本批可精确定位的同名源定义和直接 proof 构造器行区间，不能把该不完整切片与全部目标 proof 作比率。

验证证据：metrics/checkpoint.json、metrics/checks.json、metrics/publication.json。67 条新证明的 Print Assumptions 均 closed，没有新增 Axiom/Parameter/Admitted/Abort。传递 QCP 环境仍包含历史公理；不能将新证明审计结果扩大为整个环境无公理。独立内核检查用时 280.41 秒，退出 0。9 项回归覆盖带 annotation 的常量、短路、双参数调用/I/O、循环赋值、全局字符、负数/溢出 word 和相邻/重叠写入，均通过；有限回归不替代全称模拟证明。

metrics/invariant-components.json 和 metrics/remaining-obligations.json 列出未完成连接。后续仍需布局/上下文/运行时/类型/函数编号/临时槽/代际/静态地址/标签/预算/短路/代码位置不变量及保持，构造完整 initial/step/iter，之后才能得到原 cmc_preservation 和成功桥接，恢复原 controller run 完成顶层 C 的 VC 与终检。

重放：按 publish.py 依赖序执行 check.py development；audit.py 生成逐项签名和成本审计；check.py development PreservationAudit 与 check.py kernel PreservationAudit 执行独立审计。所有命令、失败尝试、退出码和哈希均保存。C* 原始重放此前已通过，本批未重复运行。
