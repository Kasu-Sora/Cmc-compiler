# cmc_compile：第九批类型不变量公共支持

本批保持原 cm_task_type_ready 的定义含义：表达式/左值结果类型、零常量例外、续延输入与结果、参数求值进度及控制返回值类型。24 个模块提供初始、真实 R/L/S/V/C 转移、任意步迭代，以及 cm_source_termination_type_ready。没有改变 C 契约，也没有假定目标程序终止。最终发布状态以 metrics/checkpoint.json 为准；顶层仍未完成，skill 不更新。

复用前八批 58 个已验证公共库及既有实现证明中的类型引用、代码模型和查找事实。新增定义 25 个，其中 24 个对应原类型支持定义，1 个为组织迭代的本地组合不变量。HOL 的 HD [] 在参数 slot 列表上的任意解释保留为显式 nilslot 参数；所有定理对其任意取值成立，没有添加关于该参数的公理。

新公共成本：24 库、25 定义、88 引理；定义 100 行，proof 691 行（引理声明与证明 687 行，4 个 Ltac 共 4 行）。新增 C 和 annotation 成本为 0。所有辅助引理计入成本，工具与自动生成审计不计入。C* 同名部分参照为定义 857 行、直接证明构造器 3730 行、常量包装 93 行；这不包含完整原依赖闭包，不能计算整体迁移比率。完整顶层成本及人工时间仍未确定。

实际路径包括：空参数调用、参数逐个求值和反向累积列表、短路二元求值、指针空值兼容、非空偏移、成员查找、带标签内存读取、局部初始化、循环/分支和调用返回。成员与绑定查找复用已有边界下默认值无关的等式；数组左值保持原“元素地址类型”规则。

审计命令：source_reference_cost.py；check.py development TypesAudit；check.py kernel TypesAudit。发布命令 publish.py 只接受审计与独立内核均通过且源/.vo 哈希固定的内容；record_checkpoint.py 再检查原源文件、前批依赖、skill 和成功清单。失败尝试完整保留在 metrics/checks.json。

验证结果：88/88 Print Assumptions 闭合，独立 coqchk 通过（310.89 秒），24 个正式库编译通过，record_checkpoint.py 所有冻结输入检查通过。现累计 16/18 项，本轮原剩余 11 项完成 9 项；code-layout 与完整 target-sim、原 cmc_preservation、成功桥和顶层 QCP 尚未完成。skill 与迁移成功清单保持未更新。
