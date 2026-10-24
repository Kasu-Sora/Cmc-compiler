# 第十六批：初始化和赋值的目标模拟

6 个公共模块新增 23 条引理、231 行 proof，定义和 C/annotation 增量为 0。23 条假设审计全部闭合，独立 coqchk 通过（310.69 秒），正式库编译通过。

证明源内存写入保持初始化字节和指针 provenance 对应，并由原运行时内存布局推出调用帧、帧指针和临时槽不被覆盖。完整 V-init 和 V-assign-right 分支覆盖实际字符转换、地址计算、写入及赋值结果的重新加载。

累计公共依赖 480 定义、896 引理、1935 行定义和 6317 行 proof。C* 同名参考子集 constructor 855 行、声明脚手架 9 行，不是完整可比成本，故不计算比率。完整原不变量仍为 17/18；原保持性、成功桥和顶层 QCP 未验证，skill 未更新。

详见 [检查点](metrics/checkpoint.json)、[覆盖边界](metrics/transition-coverage.json)、[工作量](metrics/effort.json)。二元运算在 target_binary 继续。
