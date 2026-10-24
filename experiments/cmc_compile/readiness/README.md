# cmc_compile：第七批公共证明支持

原 cm_task_layout_ready 已在初始状态、实际步进以及任意步数上证明。累计 14/18 项，本轮原剩余 11 项完成 7 项。仍缺 type、tagged-valid、code-layout、完整 target-sim；原 cmc_preservation、成功桥、顶层 QCP 未完成，skill 未更新。

10 个原定义保留所有 guard、空列表分支和全称条件。新增两个本地定义：cm_task_statement_control 限制非 exit/error 控制流出现于语句续延；cm_readiness_support_invariants 组织归纳。局部性质通过实际 R/L/S/V/C 步进证明，没有增加 C Require。复用 44 个已验证公共库，新增复用源码成本为 0。

调用就绪、输入字节有效性、左值地址、load/store/binary/pointer guards 从成功源执行推出；控制流分支通过已证 coordinate/context 和新局部控制流性质连接。最终 cm_source_termination_layout_ready 只要求原 semantic_wf 和 source_terminates，不假定未完成的类型或目标模拟定理。

新增公共成本：5 个库、12 定义、24 引理；定义 49 行、proof 190 行（引理 185 行、4 个 Ltac 共 5 行）。所有新增辅助项计入，工具和审计文件除外；新增 C/annotation 为 0。同名 C* 定义参照 292 行；本批证明采用新分解，不存在同名证明构造器切片，记录 0 不代表源证明成本为 0。完整可比成本、历史人工耗时仍未确定，不计算比率。

24/24 Print Assumptions 闭合；独立 coqchk 通过，303.17 秒；5 个正式目录公共库编译通过。失败和两次主动终止的策略分支展开尝试均保留。源语义、前 44 库、skill、成功清单哈希保持。计划文件的外部阅读链接增补沿用前批记录；顶层 VC 尚未生成。

七批累计 433 定义、521 引理，定义 1659 行、proof 3012 行。本轮第四至第七批新增 82 定义、299 引理，定义 221 行、proof 1891 行。重放顺序与门禁见 publish.py、record_checkpoint.py、metrics/kernel-input-manifest.json。
