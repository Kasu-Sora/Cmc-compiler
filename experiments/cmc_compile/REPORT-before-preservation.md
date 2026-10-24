# cmc_compile：公共语义支持已推进，顶层 QCP 尚未完成

本批新增 9 个公共 Rocq 模块，已通过编译、独立内核检查和逐项假设审计，并已接入 `/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/`。具体产物、命令、语义边界与工作量见 [公共支持记录](semantics/README.md)。**尚未证明完整 cmc_preservation，未完成顶层 cmc_compile 的 QCP 验证，skill 未更新。**

已补入实际 TVM/源程序执行与终止语义、对象解码及模型解码唯一性、原 codegen 条件具体实例；证明了初始内存/IO 对应、执行确定性、字符/整数/指针加载模拟、存储后初始化字节模拟、终止目标的输出观察等。原契约仍要求任意解码对象上的语义保持性；只得到模型字节或本批辅助定理都不足以满足它。

新增公共成本单列：276 项定义/数据类型、108 条引理；定义 1069 行，proof 370 行（含引理陈述，另含 2 行判定证明）。复用 24 个原库不改源码、不重复计入新增成本。12 项执行回归单列为验证，不计入公共证明。完整公共依赖闭包尚未结束，最终成本和两边比率仍为 null。

| 顶层案例指标 | C* 基线 | QCP 最终成本 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行／2 条 | 未完成 |
| Specification + annotation | 14 行 | 未完成 |
| 函数内 proof | 435 行 | 未完成 |
| 私有 proof 支持 | 64 行 | 未完成 |
| 案例 proof 合计 | 499 行 | 未完成 |
| 同文件公开 success bridge | 42 行 | 未完成 |
| 新增外部公共依赖 | 完整闭包尚未测完 | 当前定义 1069 行／proof 370 行，非最终值 |

源 proof 的 541 行合计只含案例和同文件 bridge，不含外部保持性闭包；getter 3 行、其他初始化/审计 29 行仍另列。历史源开发时间与人工活跃时间未知。

下一段连接仍是：annotation 更新与擦除 → 原 18 项不变量的 initial/step/iter → 成功源执行模拟 → cmc_preservation → cmc_compile_success_bridge → 顶层 C 资源标注、VC 和终检。详细源定位与完成状态见 [剩余义务](semantics/metrics/remaining-obligations.json)。这些缺口没有用假定公理、加强 Require 或弱化 Ensure 替代。

原 controller run 为 `cmc_compile_migration-20261019230022`，annotation owner 为 `/root/compile_annotation`。初始 pre-VC dependency-gap 报告仍作为历史证据保存；其中“所有语义定义均不存在”的描述已被本批进展取代。当前 C run 仍未生成 VC。依赖连接齐全后，需修复 retry-round 对不存在的历史 manual 文件做摘要的 FileNotFoundError，再恢复同一 owner。公共数学支持的迁移属于用户已授权范围，可以独立推进；先前报告用角色边界解释无法继续公共依赖工作，现已纠正。

源 C* 完整重放此前已通过：1040.281 秒，退出码 0，verification_conditions、axioms、strategies 均为空。原 600 秒外部超时已通过可配置超时/心跳/进程组清理修复，日志见 `metrics/cstar-verification.json` 与 `logs/20261019T151758968928Z-cstar-source/`。本批核对了 518 个源文件和 185 个既有目标源码哈希均未变。迁移 skill、完成清单和 MIGRATION_PLAN 也未改动，顶层通过后再更新。

初始阶段记录已保留为 `REPORT-before-semantics.md`；最新状态以此文件、`metrics/status.json` 和 `semantics/metrics/checkpoint.json` 为准。
