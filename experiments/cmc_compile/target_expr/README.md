# 第十三批：表达式及结构转移的目标模拟

完成全部左值任务；右值任务除空参数直接调用外均已接通（非空参数调用的初始转移已覆盖）。另完成 S 的结构转移（不含声明/初始化）、V 的 return 续延、C 的 sequence/exit，以及 Done。这里证明的是实际 `cm_step`、`cm_annotation_step` 与 `tvm_iter` 的对应，仍未宣称全部目标模拟成立。

新增公共 1 定义（4 行）、30 引理（proof 289 行），8 个正式公共库编译通过。30 条 `Print Assumptions` 全部闭合，独立 coqchk 通过（309.21 秒）。C/annotation 新增为 0；保持原输入契约，没有将局部证明前提加入 C Require。

累计 480 定义、785 引理，定义 1935 行、proof 5093 行；原完整模拟分量保持 17/18，最后一项的部分分支不能算作整项完成。

C* 同名参考子集为 constructor 356 行、声明脚手架 6 行。这不是完整可比闭包，不计算比率。具体分支边界见 [覆盖清单](metrics/transition-coverage.json)，验证与工作量见 [检查点](metrics/checkpoint.json) 和 [成本](metrics/effort.json)。

后续仍需调用/函数序言、局部激活和恢复、其余 V/C 操作，再完成总模拟、原 cmc_preservation、成功桥及顶层 QCP。skill 未更新。
