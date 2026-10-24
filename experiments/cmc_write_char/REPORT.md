# cmc_write_char：C* → QCP 迁移与增量工作量

2026-10-15。`cmc_concrete_emit_char.c` 中的 `cmc_write_char` 已完成迁移。原 C* 证明重放通过；QCP run `cmc_write_char_migration-20261015193338` 最终为 `done`，`final_check.status` 为 `passed`。原契约、全部 signed long long 输入及运行时代码均保留。

**1 条顶层手工义务及其 3 个 split 子目标完成；另有 3 条自动结果以 `Admitted` 导出。公共定义和引理新增成本均为 0。** 本例实际复用了前例的公共编码库，没有复制或重证其定义、引理。manual 没有新增公理或未完成证明。

## 交付

- [正式 QCP C 文件](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_write_char_migration.c)
- [案例证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_write_char_migration_proof_manual.v)
- [复用的公共编码库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_write_word_migration_lib.v)
- [源基线](baseline/manifest.json)、[目标快照和哈希](target/manifest.json)、[复用依赖](baseline/reused-dependencies.json)
- [逐区间计量](metrics/effort.json)、[过程记录](metrics/process-notes.json)
- [C* 验证结果](metrics/cstar-verification.json)、[QCP 最终状态](logs/qcp-controller/controller_state.json)

范围是写入低字节的函数实现及其必要依赖；没有扩大为整个 CMC/TVM 的编译正确性迁移。

## 原契约与运行语义

| 项目 | 原 C* 与目标 QCP 保留的含义 |
|---|---|
| 算术前提 | `0 <= cursor`、`cursor + 1 <= capacity`、`capacity <= 2147483647` |
| 输入域 | `long long char_value` 的全部 signed64 值；不要求非负或小于 256 |
| 前置资源 | 初始化前缀 `prefix` 与未初始化后缀分离 |
| 后置内容 | `prefix ++ [tower_u8(char_value)]`，初始化端点为 `cursor+1` |
| 后置剩余资源 | `[cursor+1, capacity)` 仍未初始化 |
| 原运行时 | 转 unsigned long long；取 `% 256ULL` 后转 unsigned char；调用一次 `cmc_write_byte` |

`tower_u8 z` 是数学意义的 `z mod 256`，取值 0～255。该函数写出一个低字节，不是 Unicode 编码函数。负数也合法，例如 -1 写入 255；256 写入 0。证明覆盖所有合法输入，不依赖这些举例。

目标用 `UCharArray::seg(data,0,cursor,prefix)` 和 `UCharArray::undef_seg(data,cursor,capacity)` 表达相同初始化边界与分离资源。没有额外要求整个目标已初始化，没有添加输入范围、全局非空或指针不等条件。

C* 的数学模对应 `Z.modulo`；运行时 C 余数在生成 VC 中对应 `Z.rem`。`unsigned_last_nbits char_value 64` 先按 `2^64` 取模，包装后的值非负。目标证明直接实例化已有 `tower_machine_rem_byte__byte_encoding char_value 0`，归约 `256^0`、`Z.quot _ 1` 与 `tower_encode_byte _ 0`，得到：

```text
unsigned_last_nbits
  (Z.rem (unsigned_last_nbits char_value 64) 256) 8
= tower_u8 char_value
```

另两个子目标通过已有 `Z.mod_pos_bound` 得到非负与严格小于 256。原输入域没有缩小，原规格也没有换成只描述 wrapped bits 的新定义。

`measure.py` 从原 C* 文件移除 proof/标注，再与目标去掉注释后的函数做 C token 比较，结果一致。原始类型转换、常量、局部变量、helper 调用和实参均保留。

## 公共依赖的实际复用与成本

本例没有 `cmc_write_char_migration_lib.v`，controller 使用 absent 策略。C 通过一行 `Import Coq` 接入已验证的 `cmc_write_word_migration_lib.v`。当前目标没有新建同名模型、包装引理或公理。

实际使用链为：

1. 规格引用已有 `tower_u8`。
2. manual 直接使用已有 `tower_machine_rem_byte__byte_encoding`，并归约已有 `tower_encode_byte` 的 k=0 分支。
3. 该引理内部依赖已有 `tower_machine_byte__byte_encoding` 和 `tower_mod_div_byte__byte_encoding`。
4. 范围证明复用标准库 `Z.mod_pos_bound`。

`word` 库源码 SHA-256 为 `86fa9e40c7960d2469a767fd58da08c301d0f4f138f4dff06d60b827345d6660`，与前例正式产物一致。依赖准备重建了它的 `.vo`，并把源和编译产物哈希封存在本例 selected dependency snapshot；最终证明通过该依赖检查。复用不仅是写了一个导入名称，确实进入编译和证明链。

只复用纯数学 lib，不导入 `cmc_write_word_migration_proof_auto` 或 word 函数证明；因此本例不继承 word 函数的 37 条自动结果。库中的 `tower_word_bytes` 虽随模块可见，本例没有用到，不把它说成本例的实际逻辑依赖。

`cmc_write_byte` 仍是模块化运行时依赖。目标声明的完整 With/Require/Ensure 与前例逐字相等，计量脚本再次检查。其实现已在 run `cmc_write_byte_migration-20261015151544` 验证；本例证明调用前提与组合结果，不重复计算该实现证明成本。原 helper 的 2 条可信自动结果仍单列为依赖信任项。

| 公共新增项 | 数量／非空行 |
|---|---:|
| 新模型或表示定义 | **0／0** |
| 新公共引理及证明 | **0／0** |
| 新公共库文件／seed 脚手架 | **0／0** |
| 接入既有公共库的 C 导入标注 | 1／1 |
| 显式复用的 byte helper 契约 | 1／8，归 annotation |

上次 word 的 16 行定义和 51 行公共 proof 是已付成本，本次不重新计为新增。源 char 也复用已有 `cmc_unsigned_byte0_bridge`、`tower_u8` 和 `tower_u8_range`，其公共新增成本同样为 0。不要为了让本例“有公共迁移量”而复制这些内容。

## Annotation 与 proof 工作量

统计最终非空物理行，包含语法包装，排除纯注释、独立 QCP `*/` 和自动生成 VC 文本。头文件重复契约只计一次；proof 块计 proof，`where` 实例化计 annotation。详细区间和文件哈希在 `metrics/effort.json`。

| 最终规模 | C* | QCP |
|---|---:|---:|
| 主函数 specification | 13 | 8 |
| 函数体 annotation | 3 | 1 |
| 目标显式复用的 helper 契约 | 由依赖导入，未重复抄写 | 8 |
| Annotation 总计（含显式 helper 契约） | **3** | **9** |
| Specification + annotation | **16** | **17** |
| 案例 proof 区域 | **10** | **33** |
| 公共定义／proof 新增 | **0／0** | **0／0** |

源 10 行 proof 是一块内联证明，无本例私有 helper。目标 33 行包含 **21 行证明体和 12 行 Lemma／Proof／Qed 声明包装**。包装主要由生成框架给出，不能将全部 33 行都称为新手写 tactic。4 个 Lemma 是 1 条顶层义务加 3 个子目标，不是 4 条独立手工顶层义务。

QCP 只有一处 `where` 注释，含 prefix 与 model_byte 两个实例化绑定；没有循环或 Assert。不计复用 helper 的显式接入时，目标主函数 specification + body annotation 为 9 行。外部声明 4 行、库导入 1 行另列，不混入数学定义成本。

这些是最终产物和增量迁移规模，不是两种证明器从零开发的公平效率对比。公共引理复用已实际发生，但单个案例不能据此量化一般性的时间节省。

## 验证结果与信任边界

C* 0.5.7 在隔离项目副本上验证未改动源码，退出码 0；verification_conditions、axioms、strategies 列表均为空，耗时 36.128 秒。源哈希 `5462ed664ef2bd32849b77a187764acb56ee1caaf323e85c9a61ff6206b29753` 与基线一致。

QCP 完成 annotation 接纳和 clean replay、既有依赖准备、独立 VC 检查、group 验证、合并后完整验证、final-apply 和 final-check。正式 C／goal／auto／goal-check 与接纳版本一致，manual 与最终候选哈希一致；复用的 word 库和 byte C 文件保持不变。

本例自动导出 3 条可信 `Admitted`：`cmc_write_char_safety_wit_1`、`cmc_write_char_return_wit_1`、`cmc_write_char_partial_solve_wit_1` 的 proof。它们未被修改或当成内核已证结论掩盖。手工完成的 pure witness 对应字节值及范围，剩余手工义务为 0。整体仍信任 QCP 自动结果和既有逻辑基座，不是无信任假设的完整内核证书。

## 过程记录

| 指标 | 结果 |
|---|---:|
| Annotation attempt／候选 | 1／1 |
| Owner symexec／失败 | 1／0 |
| 因证明缺口返回 annotation | 0 |
| VC 报告格式修复 | 1 |
| 开发／exact group 检查 | 各 1 次，首次通过 |
| 证明失败／debug 调用／环境故障 | 0／0／0 |
| 最终 group／parent／final | 全部通过 |
| Owner symexec／clean replay 时间 | 0.036／0.040 秒 |
| QCP controller 墙钟 | 625.722 秒，约 10.4 分钟 |
| C* 成功重放 | 36.128 秒 |

唯一修复是 VC 报告的 Structural Blocker Scan 字段格式，在同一 owner/attempt 中完成，没有修改正式规格或证明义务。无新增标注轮次，也无证明期回退。

C* 历史开发时间、人工活跃时间和模型活跃时间未知，记录为 null。QCP 墙钟包含阅读、编排、等待和验证，不能与 C* 重放时间直接作性能比；报告和 skill 更新在该计时之外。

## 复查与 skill

在 `/Users/nizitong/Documents/ChatGPT/Cmc` 执行 `python3 experiments/cmc_write_char/measure.py`，可复核验证状态、文件哈希、运行时 token、helper 契约、既有公共库在依赖快照中的身份及计量区间。它是审计脚本，不重新运行证明。`verify_source.py` 可重放 C*；QCP 重验按仓库 controller 新建 run，不改既有封存记录。

迁移 skill 在完整验证通过后更新，记录本例的实际零新增公共成本、k=0 引理实例化和跨案例依赖快照复用。
