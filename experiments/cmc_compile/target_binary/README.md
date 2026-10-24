# 第十七批：普通二元运算的目标模拟

8 个公共模块新增 1 项定义（6 行）、29 条引理（383 行 proof）。29 条假设审计全部闭合，独立 coqchk 通过（328.52 秒），正式库编译通过。C/annotation 增量为 0。

完整普通二元运算分派覆盖比较、整数算术、指针加减及指针差值；复用此前已验证的短路分支。指针差值的 signed-size 和非零条件由原类型及 cm_binary_ok 推出，没有新增顶层前提。

累计公共依赖 481 定义、925 引理、1941 行定义和 6700 行 proof。C* 同名参考子集 constructor 63 行、声明脚手架 2 行，不是完整可比成本。完整原不变量仍为 17/18；完整模拟归纳、原保持性、成功桥和顶层 QCP 未验证，skill 未更新。

详见 [检查点](metrics/checkpoint.json)、[覆盖边界](metrics/transition-coverage.json)、[工作量](metrics/effort.json)。函数返回在 target_return 继续。
