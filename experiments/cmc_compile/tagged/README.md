# cmc_compile：第八批公共证明支持

原 cm_task_tagged_valid 已在初始状态、实际 R/L/S/V/C 步进及任意步数上证明，累计 15/18 项，本轮原剩余 11 项完成 8 项。仍缺 type-ready、code-layout 和完整 target-sim；原 cmc_preservation、成功桥、顶层 QCP 未完成，skill 未更新。

复用此前 49 个已验证公共库，复用源码新增成本为 0。保持原 tagged-valid 的条件含义：标签地址本身活跃时，其 8 字节跨度必须全部活跃；没有将它改成“所有标签地址必须活跃”。分别证明 store、IO、局部区域激活、作用域/调用恢复和参数写入保持性。

参数证明直接沿原 cm_enter_call 的正向 cm_store_params 递归进行。局部 cm_tagged_span_except 允许尚未填充的参数后缀暂含旧标签，每次写入缩短这个后缀，最终后缀为空得到原有效性。这是证明归纳谓词，没有修改调用实现、C Require 或最终不变量，也未迁入原证明采用的反向写入全状态等价支持。第二个本地定义 cm_tagged_support_invariants 组织迭代；另一个定义是原 cm_task_tagged_valid。

新增公共成本：9 库、3 定义、48 引理，定义 6 行、proof 395 行（引理 392 行、3 个 Ltac 共 3 行）。新增 C/annotation 为 0。所有辅助项均计入；工具与自动生成审计除外。C* 同名参照切片：定义 34 行，直接 proof 构造器 875 行，常量包装 27 行。这只是部分同名映射，不能作为完整成本分母；历史人工耗时、最终可比成本和比率仍未确定。

48/48 Print Assumptions 闭合，独立 coqchk 通过（304.15 秒），9 个正式公共库编译通过。没有新增 Axiom/Admitted/Parameter；失败尝试保留。源 518 文件、旧依赖、前批公共库、skill、成功清单哈希均通过检查。计划文件已有外部函数索引链接增补按前批记录保留。顶层 VC 尚未生成。

八批累计 436 定义、569 引理，定义 1665 行、proof 3407 行。本轮第四至第八批新增 85 定义、347 引理，定义 227 行、proof 2286 行。类型支持在 ../types 独立开发，未计入这些完成数。复核门禁见 publish.py、record_checkpoint.py 与 metrics/kernel-input-manifest.json。
