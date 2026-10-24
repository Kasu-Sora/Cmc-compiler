# cmc_write_word：C* → QCP 迁移与工作量

2026-10-15。`cmc_concrete_emit_word.c` 中的 `cmc_write_word` 已完成迁移。原 C* 文件重放通过；QCP run `cmc_write_word_migration-20261015190516` 完成全流程，最终状态 `done`，终检 `passed`。原契约、全部有符号 64 位输入以及运行时代码均保留。

**15 条顶层手工义务、45 个 split 子目标全部完成；另外 37 条自动结果以 `Admitted` 导出。** 新增公共库有 3 个定义、3 条已证明且实际使用的引理。manual/lib 没有新增公理或未完成证明。整体结果仍信任 QCP 自动求解器及既有逻辑库，不能称为所有义务均具有独立内核证明证书。

## 交付

- [正式 QCP C 文件](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_write_word_migration.c)
- [案例证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_write_word_migration_proof_manual.v)
- [编码定义和公共引理](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_write_word_migration_lib.v)
- [基线与源码哈希](baseline/manifest.json)、[目标快照与哈希](target/manifest.json)
- [逐区间工作量](metrics/effort.json)、[过程记录](metrics/process-notes.json)
- [C* 重放结果](metrics/cstar-verification.json)、[QCP 最终状态](logs/qcp-controller/controller_state.json)

范围是此写字函数及其必要依赖，不表示整个 CMC/TVM 编译正确性已经迁移。源文件中的头文件契约已对应到目标契约，不机械复制 HOL 的证明构造 API。

## 契约与语义保持

| 项目 | 保留的含义 |
|---|---|
| 入口算术 | `0 <= cursor`、`cursor + 8 <= capacity`、`capacity <= 2147483647` |
| 输入字 | `long long` 全部有符号 64 位值，包括负数；未增加 `word_value >= 0` 等前提 |
| 入口资源 | 初始化前缀 `prefix` 与从 `cursor` 到 `capacity` 的未初始化后缀分离 |
| 出口资源 | 初始化前缀扩展为 `prefix ++ tower_word_bytes(word_value)`，其后仍是未初始化后缀 |
| 字节顺序 | 小端顺序，第 0 字节先写，第 7 字节最后写 |
| 运行时实现 | 原始转换、ULL 常量、局部变量、8 次 `cmc_write_byte` 调用及参数表达式全部保留 |

数组表示沿用已验证案例的 `UCharArray::seg(data,0,cursor,prefix)` 和 `UCharArray::undef_seg(data,cursor,capacity)`。没有要求整个数组已初始化，没有加入额外的非空或别名条件。`measure.py` 从原源文件移除 C* 标注和 proof 块，再与目标移除 QCP 标注后的函数比较，C token 完全一致。

源 `tower_base.c` 的三个数学定义被直接翻译：`tower_u8 z` 是 `Z.modulo z 256`；`tower_encode_byte z k` 保留 k=0..7 的分支和逐次除以 256，其他 k 返回 0；`tower_word_bytes` 保留同序的八元素列表。目标没有用运行时的 wrapped bits 偷换规格。

源 HOL 正除数整数除法对应 `Z.div`，而生成 VC 的 C 运算是 `Z.quot`／`Z.rem`。QCP `IntLib.v` 的 `unsigned_last_nbits x n` 定义为 `x mod 2^n`；生成 VC 中 `word_value` 为 `Int64`，`bits` 为 `UInt64`，转换明确是按 `2^64` 取模。包装后的数非负，因此运行时截断除法、余数可转换为数学除法、模。

新增桥接证明对任意 `z : Z` 成立，而不仅是非负输入。它证明对 `0 <= k <= 7`：

```text
((z mod 2^64) quot 256^k rem 256) mod 2^8
= tower_encode_byte z k
```

先证明移除 `d*256*q` 的整数倍不改变第 d 位的 byte，再证明 `2^64 = 256^k * 256 * 256^(7-k)`，最后连接 `quot/rem` 和 `div/mod`。负数没有被排除：例如 -1 的结果是八个 255；最小有符号 64 位值的结果是七个 0 后接 128。这些例子只是解释，实际验收是通用定理与函数义务。

这里完成的是两边原生逻辑内的证明和源模型对应审查，没有另建 HOL 与 Rocq 两套完整内存语义的等价定理。

## 已验证 helper 的模块化复用

目标保留 `cmc_write_byte` 声明，其完整 With/Require/Ensure 注释与前例逐字相等，并由计量脚本再次断言。前例 run `cmc_write_byte_migration-20261015151544` 已验证实现体；本例不重复验证或重复计算其实现证明成本。

本例的 8 次调用证明各自的字节值、范围、容量和资源前提；该 helper 的输出契约逐步给出新的数组前缀。原 helper 的两条自动结果仍是模块化依赖中的可信项，不能因为复用而忽略。它们与本例新增的 37 条自动结果分开记录。依赖源码、哈希及已完成状态在 [baseline/verified-byte](baseline/verified-byte/manifest.json)。

## Annotation 与 proof 工作量

以最终非空物理行为尺度，排除纯注释；包含语法包装，但不计独立的 QCP `*/`。头文件重复契约只计一次。数学定义单列，C* 内联 proof 归 proof，`where` 实例化归 annotation。自动生成的 VC 文本不计 proof。

| 最终规模 | C* | QCP |
|---|---:|---:|
| 主函数 specification | 13 | 8 |
| 函数体 annotation | 59 | 100 |
| 目标中显式复用的 helper 契约 | 导入依赖，未重复抄写 | 8 |
| Annotation 总计（含显式 helper 契约） | **59** | **108** |
| Specification + annotation | **72** | **116** |
| 案例 proof 区域 | **219** | **435** |
| 公共桥接 proof 区域 | **98** | **51** |
| 案例 + 公共 proof 区域 | **317** | **486** |

C* 案例 proof 是 162 行内联证明（9 块）加 57 行私有辅助证明。另将公开的 `cmc_unsigned_byte0_bridge` 及其通用证明构造器代码单列为公共桥接 98 行；该通用构造器也服务 byte1..7，只计一次，不再加进案例私有成本。源既有三个编码定义共 23 行，列为模型依赖参考。

QCP 的函数体 annotation 为 16 行调用实例化（8 次调用，每次传入两个逻辑参数）和 84 行中间断言（6 处）。断言用于归一化数组端点，并在验证器的 cut 处保留所有局部字节绑定及资源。加上逐字复用的 8 行 helper 契约，共 108 行；若比较时排除显式 helper 接入，QCP `specification + body annotation` 为 108 行。

QCP 的 435 行 proof 区域包括 **255 行证明体和 180 行 Lemma／Proof／Qed 声明包装**；后者主要来自生成框架，不能全部称为新手写 tactic。60 个 Lemma 是 15 条顶层义务加其 45 个子目标，不是 60 条独立顶层义务。分组结果为：编码 3／15、范围 6／24、端点 5／5、返回 1／1（顶层／子目标）。

此次目标的案例证明和标注规模高于源版，包含反复的范围子目标、证明路由及局部状态保持。行数受生成方式和排版影响，不等于工具耗时、证明难度或两种系统的总体优劣；这是读取源证明后的迁移实验，不是独立从零公平对比。

## 本次新增公共成本

| 新增项 | 数量 | 非空行 |
|---|---:|---:|
| `tower_u8`、`tower_encode_byte`、`tower_word_bytes` | 3 个定义 | **16** |
| 取模／字节编码桥接 | 3 条引理 | **51** |
| `Lia` 官方库导入 | 1 | 1 |
| C 中的 case-lib 导入标注 | 1 | 1 |
| controller 库 seed | — | 3，单列脚手架 |

三条引理是 `tower_mod_div_byte__byte_encoding`、`tower_machine_byte__byte_encoding`、`tower_machine_rem_byte__byte_encoding`。后者被 manual 直接调用，前两者在其依赖链中使用；不是新增但未用的装饰性证明。3 个定义也由规格和证明引用。整个库由 goal/manual 导入，经过设计检查、group 编译、合并检查和 final-check，无需另做未引用库的补充编译。

现有 `Z.div_mod`、`Z.div_add`、`Z.mod_add`、`Z.quot_div_nonneg`、`Z.rem_mod_nonneg`、数组表示及列表结合律直接复用，没有把底层库计为新增工作。公共文件放在本案例 lib 中，后续 char 案例可按仓库允许的依赖方式引用；迁移到独立公共模块是后续组织调整，不应再次计为从零证明。

## 验证与信任项

C* 0.5.7 使用隔离项目副本验证未改动的原文件，退出码 0，`verification_conditions`、`axioms`、`strategies` 均为空，耗时 32.866 秒。源哈希为 `750d957def960d1a104f3bcb43135d251f49182a6972ec13a7ef1c114e5e7980`。

QCP 完成 annotation 接纳及 clean replay、依赖快照、独立 VC 审查、四组 proof 检查、机械合并后的完整验证、事务写回及最终新鲜度／Rocq／结构检查。正式产物哈希与接纳、合并版本一致。最终 manual/lib 不含 `Admitted`、`Axiom`、`Parameter` 或 `Abort`。

本例 proof_auto 的 **37 条 `Admitted`** 为 29 条 safety 和 8 条 partial-solve；它们是未改动的 QCP 自动结果。总计 52 条顶层义务中，15 条由本次手工证明区域完成、37 条信任自动结果。`VC_Correct` 接口不重复计数；helper 已有的 2 条可信自动结果单列为依赖。新建的纯数学桥接库只导入官方 Coq 库，没有通过导入本案例 auto 来证明数学引理。

## 过程成本与失败记录

| 过程 | 记录 |
|---|---|
| Annotation attempt／因证明缺口返回 annotation | 1／0 |
| 同一 attempt 的候选／修订 | 3／2 |
| Owner symexec | 3 次，前两次标注失败，第三次通过 |
| VC 报告格式修复 | 1 次 |
| 证明开发检查失败 | 5 次：2 次未完成模板检查、1 次导入合同、2 次 coqc |
| 另一次 debug 查询失败 | 1 次，查询的标准库引理名不存在 |
| 工具／环境故障 | 0 |
| 最终 group、parent、final | 全部通过 |
| QCP controller 墙钟时间 | 1206.657 秒，约 20.1 分钟 |
| Owner symexec 总计／clean replay | 0.600／0.523 秒 |
| C* 成功重放 | 32.866 秒 |

标注第一版在第三次调用遇到 `(cursor+1)+1` 与 `cursor+2` 的资源形状不匹配；第二版增加断言但遗漏仍需读取的局部字节变量；第三版保留局部状态并通过。没有修改运行时或入口契约。

证明期两次 coqc 失败分别是 destruct 模式语法和空间／纯事实分支顺序。导入合同拒绝了公共引理中的项目 `IntLib` 导入；改为定义上相同的 `z mod 2^n` 表达并使用官方数学库，未引入新假设。报告格式修复只调整 Structural Blocker Scan 标题和字段，不重做证明分析。

初始化另有 2 次未成功调用：problem 文件初次写入使用了错误的相对工作目录，init 拒绝缺失文件但留下空 seed；下一次 create 因该 seed 已存在而拒绝。检查其仅含三行标准脚手架后，以 present 建立当前唯一有效 run。失败的初始化目录未被冒充成有效验证结果。此开销在 controller 墙钟统计之前，另列在过程记录中。

原 C* 历史开发时间、人工活跃时间、模型活跃时间均未知，记录为 `null`。QCP 墙钟包含阅读、设计、等待、分组、修复和验证，不与 C* 单次重放工具时间作性能比值。报告和 skill 整理不在 controller run 计时内。

## 复查

在 `/Users/nizitong/Documents/ChatGPT/Cmc` 执行 `python3 experiments/cmc_write_word/measure.py`，可复核正式产物哈希、成功验证记录、原运行时 token、helper 契约一致性及逐区间计数。这是审计脚本，不重新运行证明。`verify_source.py` 可重放原 C* 文件；QCP 重验按仓库 controller 启动新 run，不修改已封存 run。

Skill 在本次完整验证通过后更新。下一候选是 `cmc_concrete_emit_char.c`，可先检查其低字节转换是否能直接复用本次 bridge 在 k=0 的实例，仍须独立迁移并验证其完整契约。
