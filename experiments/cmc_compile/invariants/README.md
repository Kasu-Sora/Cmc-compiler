# cmc_compile 模拟不变量：第三批公共支持

本批 6 个公共库通过 Rocq 编译、独立 coqchk 和 47 条逐项假设审计，并接入 QCP。**这不是顶层完成记录：完整目标模拟、cmc_preservation、原签名 cmc_compile_success_bridge 及顶层 C 验证仍未完成；skill 未更新。**

## 已证明的内容

- 临时槽一致性：保留反序参数暂存、阶段拥有的半开临时槽区间、调用时保存/恢复调用者临时槽等原定义。证明 remove/put 不覆盖其他槽、staged/phase/cursor 保持性及任意成功执行的 annotation spill 一致性。
- 控制上下文：保留语句父阶段、循环/函数作用域屏障和 return 条件。函数体作用域从已有 cm_stmt_wf/cm_typed_program 推出，覆盖表达式、语句、值返回和控制返回，证明 step/iter。
- 函数编号：保留 cm_frame_fid_ready/cm_frames_fid_ready/cm_task_fid_ready 原定义。增加并证明局部 active-fid 分量：R/L/S 阶段处于有效函数，V/C 可回到根编号 -1。进入调用由 cm_call_ok 推出被调函数编号范围；错误路径不可能成功的引理已证明。
- 具体合取 cm_control_support_invariants 包含原 18 项中的 7 项及上述局部分量，有直接 initial/step/iter 证明。cm_source_termination_support_invariants 从原良构条件和实际源终止谓词推出任意 n 步后的这些性质，**不以待证保持性或模拟作为假设，也不声称 TVM 终止**。

此前 17 个公共语义/annotation/坐标/存储/取指模块原样复用，新增源码成本为 0。原 C 契约、源程序和旧目标文件未修改。

## 签名和语义对应

cm_annotation_step_spill_coordinate 使用成功性、擦除和坐标分量；没有冒充源侧只以 layout-ready 为前提的同名引理。cm_task_context_step_coordinate 使用已有类型良构、擦除、坐标分量。cm_task_fid_step_coordinate 使用已证明 active-fid 分量。上述局部前提均在七分量 initial/step/iter 中得到证明，未加入 cmc_compile 的 Require。

源 bool 命题迁移为 Prop，23 个 phase 构造分支采用等价合并分支。context 的公共两分量提到外层，非 S/C 分支的额外 True 合取不改变命题。spill 保存帧的 hd 默认值继续由任意 cm_annotation_policy 表示，且保存帧非空要求保持。详细源文件哈希、同名声明行区间及签名审计分别见 metrics/source-reference-manifest.json、source-reference-cost.json、signature-audit.json。

## 新增公共成本

按非空非注释物理行计；proof 包含引理陈述、Proof/Qed 和 Ltac。定义另列；工具和生成的审计文件不计入数学 proof；未知历史人工耗时保持 null。紧凑分支和自动化会影响行数，不能将行数直接解释为人工难度。

| 本批公共模块 | 定义 | 引理 | 定义行 | Proof 行 |
|---|---:|---:|---:|---:|
| `cmc_simulation_context_migration_lib.v` | 13 | 5 | 40 | 20 |
| `cmc_simulation_context_step_migration_lib.v` | 0 | 9 | 0 | 108 |
| `cmc_simulation_fid_migration_lib.v` | 6 | 9 | 10 | 71 |
| `cmc_simulation_spill_migration_lib.v` | 5 | 10 | 17 | 47 |
| `cmc_simulation_spill_update_migration_lib.v` | 0 | 10 | 0 | 105 |
| `cmc_simulation_support_invariants_migration_lib.v` | 1 | 4 | 9 | 25 |

本批 25 个定义、47 条引理：定义 76 行，proof 376 行（引理 346 + 9 个 Ltac 共 30 行）。三批累计 351 个定义、222 条引理，定义 1438 行、proof 1121 行；所有辅助引理均计费，不只统计被最终定理使用的子集。

C* 同名参照切片：定义 611 行、直接 proof 构造器 1074 行、常量装配 30 行。它不含完整传递依赖，也不涵盖本批改用局部前提的组合证明，**不可与全部 QCP proof 相除得出迁移比率**。C* 顶层基线仍是 specification 12 行、annotation 2 行/2 条、案例 proof 499 行；成功桥接公共 proof 42 行另列。QCP 顶层最终成本尚未产生。

## 验证和剩余工作

47 条 Print Assumptions 均 Closed under the global context，独立内核检查退出 0，用时 291.61 秒；正式目录 6 个库编译均通过。没有新增 Axiom/Parameter/Admitted/Abort。传递 QCP 环境含历史公理，新证明的闭合审计不代表整个环境无公理。未因公共追加而重复旧的有限回归；本批验证对象是全称 initial/step/iter 定理。所有开发失败和检查时序失败如实保存在 metrics/checks.json 与 development-failures.json。

518 个原源文件、185 个先前目标文件、17 个已验证公共库以及 skill/计划/完成清单哈希不变。C* 完整原始重放此前通过，本批未重跑。

尚缺 11 项：layout-ready、runtime、type、generation、static-valid、static-bases、tagged-valid、budget、short-ready、code-layout、完整 task-target-sim。其后还需完整 cm_preservation_initial/step/iter、cmc_successful_exec_simulation、cmc_preservation、原 cmc_compile_success_bridge，以及原 controller run 的顶层符号执行、手工 VC 和终检。见 metrics/invariant-components.json 与 remaining-obligations.json。skill 更新门槛仍是顶层验证通过。

重放顺序见 publish.py：先按依赖序运行 check.py development，再 source_reference_cost.py、check.py development InvariantAudit，等待结束后运行 check.py kernel InvariantAudit。publish.py 会核对审计和哈希；record_checkpoint.py 仅在全部检查通过后写入本记录。
