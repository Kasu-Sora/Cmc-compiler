# 第十四批：值续延与作用域恢复的目标模拟

新增 42 条公共引理，proof 476 行，定义与 C/annotation 增量均为 0。13 个公共模块已编译并发布；42 条假设审计全部闭合，独立 coqchk 通过（329.29 秒）。

覆盖 unary、load、putc/puti、expr-statement、if/while-guard、halt/exit，以及 block/while-body 恢复与跳转。证明操作语义的实际转移，保留原契约；分支引理的局部前提还需由总分派从已有不变量中提取。

累计公共依赖为 480 定义、827 引理、1935 行定义、5569 行 proof；完整原不变量仍为 17/18。C* 同名参考子集 constructor 755 行、声明脚手架 16 行，不是完整可比闭包，故不计算比率。

详见 [检查点](metrics/checkpoint.json)、[覆盖边界](metrics/transition-coverage.json) 与 [工作量](metrics/effort.json)。后续在 target_state 继续；原 cmc_preservation、成功桥、顶层 QCP 与 skill 更新仍未完成。
