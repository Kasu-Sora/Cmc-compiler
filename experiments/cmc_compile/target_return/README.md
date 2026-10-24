# 第十八批：函数返回和完整控制分派

7 个公共模块新增 13 条引理、197 行 proof，定义及 C/annotation 增量为 0。13 条假设审计全部闭合，独立 coqchk 通过（318.35 秒），正式库编译通过。

覆盖 return epilogue、显式 return 和 fallthrough 的恢复。cm_target_c_task_step 统一 C 分派；cm_code_support_c_target_step 从原 17 项支持不变量提取全部局部前提，仅要求原语义 WF 和当前目标模拟，没有新增输入前提。

累计公共依赖 481 定义、938 引理、1941 行定义和 6897 行 proof。C* 同名参考子集 constructor 503 行、声明脚手架 2 行，不是完整可比成本。完整原不变量仍为 17/18；启动、调用入口及参数顺序、其余总分派接线、总模拟归纳、原保持性、成功桥和顶层 QCP 未完成。skill 未更新。

详见 [检查点](metrics/checkpoint.json)、[覆盖边界](metrics/transition-coverage.json)、[工作量](metrics/effort.json)。调用入口在 target_call 继续。
