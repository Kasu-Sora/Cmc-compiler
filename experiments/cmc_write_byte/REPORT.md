# cmc_write_byte：C* → QCP 迁移与工作量记录

2026-10-15。`cmc_write_byte` 已完成 QCP 流程验证，controller 的最终状态为 `done`、`final_check.status` 为 `passed`。原 C* 证明也在隔离副本中重新验证通过。

**验证结论有明确的信任边界：QCP 自动解决本例两条 witness，生成文件用 `Admitted` 表示这些可信自动结果。本次没有为它们另写 Rocq 内核证明证书。** 新增手工证明和公共库均没有 `Admitted` 或 `Axiom`。不能将本结果表述为“两边都获得了不含自动结果假设的内核证明”。

## 交付

- 正式 QCP 源码：[cmc_write_byte_migration.c](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_write_byte_migration.c)。
- 便于查看的完整快照：[target/](target/)，包括 C、goal、auto、manual、goal_check 和 case lib；[manifest.json](target/manifest.json) 记录正式路径及哈希。
- 原始 C* 源码快照：[baseline/cmc_concrete_emit_bytes.c](baseline/cmc_concrete_emit_bytes.c)。
- 机器可读计量：[metrics/effort.json](metrics/effort.json)，包含逐文件、逐区间分类和时间记录。
- 验证证据：[QCP controller state](logs/qcp-controller/controller_state.json)、[QCP 过程日志](logs/qcp-controller/run_logs.json)、[C* 复核结果](metrics/cstar-verification.json)。

此次范围只有这个单字节写入函数及其必要依赖。不代表 CMC 编译器、TVM 语义或编译保持性定理整体已迁移。

## 契约保持

运行时代码仍然只有 `data[cursor] = byte;`，函数参数类型完全不变。去掉验证语法后，C* 与 QCP 版本的函数 token 序列一致；提取结果保存在 `metrics/runtime-cstar.c` 和 `metrics/runtime-qcp.c`。

| 原 C* | QCP | 含义 |
|---|---|---|
| `prefix:(int)list`、`model_byte:int` | `prefix:list Z`、`model_byte:Z` | 两个逻辑参数 |
| `0 <= cursor < capacity` | 同样的纯条件 | 写入位置在容量范围内 |
| `byte == model_byte` | 同样的纯条件 | 实际写入值等于逻辑值 |
| `tower_byte_value model_byte` | `0 <= model_byte < 256` | 展开相同字节范围定义 |
| `store_uint8_array data cursor prefix` | `UCharArray::seg(data,0,cursor,prefix)` | 精确内容的已初始化前缀 |
| 从 `data+cursor*sizeof(Tuchar)` 开始、长为 `capacity-cursor` 的未初始化数组 | `UCharArray::undef_seg(data,cursor,capacity)` | 独占未初始化后缀 |
| 写后前缀为 `prefix ++ [model_byte]`，后缀从 `cursor+1` 开始 | 同样的前后缀分割 | 原前缀保留，恰好初始化一个新元素 |

没有增加整个数组已经初始化、额外非空指针或额外机器整数界限等入口条件；也没有把后置条件削弱成只描述写入单元。

`UCharArray` 由 `ArrayLib(StoreUCharAsElement)` 构造，使用 `store_uchar`、`undef_store_uchar` 和 `sizeof(UCHAR)`。`seg` 保存精确列表；`undef_seg` 描述未初始化区间。已检查的源定义、目标依赖与哈希见 `baseline/` 和 `effort.json`。这是在各自原生内存逻辑中的语义对应审查，没有声称证明了两个验证器内存模型之间的形式等价定理。

## Annotation 与 proof 规模

采用非空物理行数；包括验证语法包装，排除独立的 QCP 注释结束行。函数契约计为 specification；函数体的辅助断言、不变式计为 annotation；C* 内联 proof 块计为 proof。源 `.h` 重复的契约不再计一次。所有区间均在 `effort.json` 中记录。

| 案例最终产物 | 原 C* | 新 QCP |
|---|---:|---:|
| Specification | 14 行 | 8 行 |
| Annotation：函数体辅助标注 | 0 行 | 0 行 |
| Specification + annotation | 14 行 | 8 行 |
| 手写案例 proof | 19 行，2 个 proof 块 | 0 行，0 个手工 Lemma |
| 逻辑参数 / 契约条目 | 2 / 3 | 2 / 3 |
| 自动导出的可信 witness | 最终报告无额外公理 | 2 条 `Admitted` |

另列脚手架：C* 的导入和常量导出有 8 行；QCP 有 3 行外部谓词声明（2 个谓词）。自动生成的导入、VC、auto/manual/goal_check 文件体量不计为手写 proof。QCP 的 manual 文件只有生成的导入和作用域声明。

这个案例没有循环。QCP 的现有数组规则能自动完成打开未初始化单元、写入以及扩展前缀，因此无须添加中间断言。这里的 0 行 proof 是**手写成本**，不是没有逻辑义务，也不是证明完全不依赖可信自动化。

## 公共迁移成本，单独统计

| 本次新建公共内容 | 条目数 | 代码行 |
|---|---:|---:|
| 数学模型定义 | 0 | 0 |
| 内存表示谓词 | 0 | 0 |
| 公共辅助引理及证明 | 0 | 0 |
| controller 自动创建的 case-lib 导入脚手架 | — | 3 |

没有为了“迁移”而重复定义 QCP 已有的字节数组模型。`tower_byte_value` 直接展开为整数范围；C* 的 `cm_open_uint8_fill`、`cm_close_uint8_fill` 所承担的资源变换由 QCP 现有数组机制完成，因此也无须逐个重写同名引理。

原 C* 中直接相关的现有公共片段另作依赖参考：字节范围定义 2 行、fill 包装函数和 uint8 实例化 24 行、通用 open/close 引理构造 11 行。这些是已存在的源库片段，**不是本次新增工作，也不是完整传递依赖库的规模**。QCP 复用的 `ArrayLib.v`、`ArrayLibCore.v` 原文和哈希保存在 `baseline/qcp-reused/`；两边原有库的历史建设成本未知。

## 验证与过程记录

QCP run：`cmc_write_byte_migration-20261015151544`。版本、源码快照及 dirty 工作树信息见 [baseline/manifest.json](baseline/manifest.json)。过程遵循仓库 `verification-orchestrator`：

1. 一轮 annotation 设计，第一次候选即通过 design check、symexec、case-lib check。
2. controller 接纳并 clean replay；人工待证 witness 数为 0，因此不启动 VC 分组证明。
3. Makefile 后端准备固定依赖快照，parent full check 通过。
4. final-apply 和 final-check 通过，controller 进入 `done`。最终检查包括生成文件新鲜度、Rocq 检查、来源封存和清理。

两条自动 witness 是：

- `proof_of_cmc_write_byte_return_wit_1`：用 `byte = model_byte` 改写扩展后的前缀。
- `proof_of_cmc_write_byte_partial_solve_wit_1`：从未初始化后缀中分离可写单元并保留其他资源。

它们由 QCP 自动生成，未手工篡改；对应 `VC_Correct` 模块接口也有两条 Axiom 声明。最终 Rocq 检查允许这些自动结果，并不将其转换为独立证明项。本次没有新增手工公理、删除义务或放宽目标契约。

| 可测过程指标 | 结果 |
|---|---:|
| QCP annotation 候选 / 修订 | 1 / 0 |
| QCP 验证工具失败 / 同轮重试 | 0 / 0 |
| QCP owner symexec | 0.042 秒 |
| QCP clean replay | 0.019 秒 |
| QCP controller run 墙钟时间 | 395.406 秒，约 6.6 分钟 |
| C* 成功复核的工具执行时间 | 30.556 秒 |
| C* 环境失败尝试 | 1 次：缺少 `proof/proof.h` |

C* 的原仓库没有标准库头文件。在隔离副本补入固定版本的 C* 标准库后，未修改源文件即验证通过，`verification_conditions`、`axioms`、`strategies` 均为空。工具链为 C* 0.5.7；标准库版本见 `baseline/cstar-stdlib.json`。QCP 首次入口另有一次 Python 版本拒绝，按提示切换仓库要求的 Python 3.12 后正常启动；未计为标注失败。

时间指标不构成速度比较：C* 是已有证明的重放，QCP 墙钟时间还包含阅读、设计、编排与等待；最终报告整理时间也不在该 run 内。人工活跃时间、模型活跃时间、原 C* 历史开发时间均为 `null`。这是一例读过原证明后的迁移，不能据此判断两套工具从零证明的总体优劣。

## 复查与后续使用

```sh
cd /Users/nizitong/Documents/ChatGPT/Cmc
python3 experiments/cmc_write_byte/measure.py
```

这条命令核对正式文件与 controller 接纳版本的内容/哈希，重新生成快照和统计；它不是再次运行验证器。完整验证命令、工具路径及状态保存在 controller 报告中。重新开展 QCP 验证应通过仓库 controller 的新 run 和返回的 action，不直接修改已完成 run 的 seal/state。

`verify_source.py` 可重放隔离 C* 复核；目前复用本机已有 C* 工具链，工具路径见结果 JSON。工具链复用不依赖旧 `arr_sum` 的源代码、规约或证明。

原反方向 `arr_sum` 实验已经标记弃用，只保留历史记录。迁移 skill 在本次 `done` 后更新，以本例作为 C* → QCP 的已验证流程经验，同时保留上述自动化信任限制。
