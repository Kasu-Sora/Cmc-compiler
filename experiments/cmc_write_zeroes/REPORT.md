# cmc_write_zeroes：C* → QCP 迁移与工作量

2026-10-15。原 C* 证明重放通过；QCP controller run `cmc_write_zeroes_migration-20261015180614` 完成，最终 `phase: done`、`final_check.status: passed`。运行时代码的 token 序列相同，保持原契约的输入域、精确列表内容和未初始化后缀。

**QCP 的 3 条手工义务已完成，另有 6 条自动结果以 `Admitted` 导出，仍依赖 QCP 自动求解器的可信结果。** 新增 manual 和公共引理没有手写 `Admitted` / `Axiom`。不能把整个案例称为不含自动结果假设的独立 Rocq 内核证明。

## 交付与证据

- [正式 QCP C 文件](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_write_zeroes_migration.c)
- [正式案例 proof](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_write_zeroes_migration_proof_manual.v)
- [正式公共引理](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_write_zeroes_migration_lib.v)
- [目标快照及哈希](target/manifest.json)、[原始基线及版本](baseline/manifest.json)
- [逐区间工作量](metrics/effort.json)、[C* 验证](metrics/cstar-verification.json)、[QCP 最终状态](logs/qcp-controller/controller_state.json)、[公共引理独立验证](metrics/shared-verification.json)

这次只完成 `cmc_write_zeroes` 及其所需映射，不代表 CMC/TVM 的整体编译保持性证明已迁移。

## 原契约的对应

| 项目 | 原 C* | QCP |
|---|---|---|
| 逻辑参数 | `prefix:(int)list` | `prefix:list Z` |
| 入口纯条件 | `0 <= cursor`、`0 <= count`、`cursor + count <= capacity`、`capacity <= 2147483647` | 原样保留 |
| 初始化前缀 | `store_uint8_array data cursor prefix` | `UCharArray::seg(data,0,cursor,prefix)` |
| 未初始化后缀 | 起点 `data + cursor * sizeof Tuchar`，长度 `capacity - cursor` | `UCharArray::undef_seg(data,cursor,capacity)` |
| 写后内容 | `prefix ++ ireplicate count 0` | `app(prefix,zeros(count))` |
| 写后资源 | 精确前缀终点 `cursor + count`；剩余后缀仍未初始化 | 相同区间分割 |

`IREPLICATE_DEF` 在实际 C* 工具中输出 `ireplicate n v == REPLICATE (num_of_int n) v`，见 [定义探测日志](logs/20261015T100932Z-cstar-model-probe/stdout.txt)。QCP 现有 `ListLib.v` 第 819 行定义 `zeros n := repeat 0 (Z.to_nat n)`。在本契约的非负长度范围，两者描述同样数量的零；没有把负长度截断规则引入新的允许输入域。

字节资源沿用已验证的 `cmc_write_byte` 映射：`UCharArray.seg` 保存精确内容，`undef_seg` 保存独占的未初始化区域。这里是两套原生逻辑中的语义对应审查，未建立 HOL 与 Rocq 内存模型间的形式等价定理。

保留 `count = 0`；当 `capacity = 0` 时允许 `cursor = count = 0` 的空资源情况。没有添加全数组初始化、正长度或额外非空指针要求，也没有削弱为仅描述新写入的单元。

运行时代码仍是从 `index = 0` 开始的直接写零循环，**没有改成调用 `cmc_write_byte`**。去掉验证语法后 token 对照通过，提取结果见 `metrics/runtime-cstar.c` 和 `metrics/runtime-qcp.c`。

## Annotation 与 proof 规模

统计非空物理行，包括验证语法包装；排除纯注释及独立的 QCP `*/`。契约算 specification，循环不变式算 annotation，C* 内联 proof 块算 proof；源头文件中重复的契约只计一次。Proof 的最终区域包括声明、`Proof/Qed` 和证明路由，不等同于键盘输入量；自动生成的 VC 文本、文件导入和空模板不另计手工 proof。

| 最终产物规模 | 原 C* | 新 QCP |
|---|---:|---:|
| Specification | 14 行 | 8 行 |
| Annotation | 15 行 | 9 行 |
| Specification + annotation | 29 行 | 17 行 |
| 案例 proof 区域 | 81 行，4 块 | 39 行，6 个 Lemma |
| 循环不变式 | 1 个 | 1 个 |
| 逻辑参数 | 1 个 | 1 个 |

QCP 的 6 个 Lemma 对应 **3 个顶层义务和各自的 1 个空间子目标**，不能算成 6 条独立顶层 VC。39 行中，证明体 tactic 为 21 行，其余 18 行为声明及 `Proof/Qed`。三项内容是：

1. 初始化：`zeros 0 = []`、`prefix ++ [] = prefix`、`cursor + 0 = cursor`。
2. 循环保持：合并地址加法，并证明写入单个零后，列表等于 `prefix ++ zeros(index + 1)`。
3. 退出：用 `index = count` 将不变式转成原后置条件。

另列脚手架：源 imports 6 行；目标外部声明 4 行（3 个名字）；case-lib 原有 seed 3 行。这些不混入 annotation/proof。行数会受语法和排版影响，不能据此声称某体系耗时或难度减少相同比例。

## 公共定义和引理的新增成本

| 本次新增公共内容 | 数量 | 非空行 |
|---|---:|---:|
| 数学模型定义 | 0 | 0 |
| 堆表示谓词 | 0 | 0 |
| `zeros_snoc__zero_step` 引理及证明 | 1 | 8 |
| 新增官方库 `Lia` import | 1 | 1 |
| 自动生成的 case-lib seed | — | 3 |

引理陈述为：`0 <= n -> repeat 0 (Z.to_nat (n + 1)) = repeat 0 (Z.to_nat n) ++ [0]`。8 行包含声明及证明包装，证明体为 4 行。加上公共引理，本次最终 proof 区域为 **39 + 8 = 47 行**；公共 import 另计。

**当前 manual 没有导入此 helper，循环保持证明直接使用现有 `Z2Nat.inj_add`、`repeat_app` 和 `app_assoc`。** 因而这 8 行是本次实际形成的可复用额外产物，并非当前案例通过的必要依赖，也没有使本例 manual 缩短。不能把 controller 的公共池条目数当作引理数：本例推广了 import 和 Lemma 两项，实际只有一个新引理。

终检不能单凭未引用库的存在证明其已编译。为补足证据，`verify_shared.py` 在实验目录编译正式 lib 的哈希一致副本，再运行 `Print Assumptions zeros_snoc__zero_step`，结果为 `Closed under the global context`。两条命令均退出 0；它是独立的纯 Rocq 补充检查，不修改 QCP run 或替代 C 验证流程。

复用而非新建的目标依赖包括 `zeros`、`UCharArray.seg/undef_seg`、`Z2Nat.inj_add`、`repeat_app`、`app_assoc` 及数组拆分/合并机制。相关目标库快照与哈希在 `baseline/qcp-reused/`。源侧既有 `mk_ireplicate_empty` 为 6 行、`mk_ireplicate_snoc` 为 9 行；仅作直接依赖片段参考，不把它们算成本次新增成本，也不代表完整源公共库规模。

## 验证、信任与过程

C* 0.5.7 在隔离副本中复核原始文件，退出 0，结果中的 `verification_conditions`、`axioms`、`strategies` 均为空。标准库采用固定版本，未修改源证明。

QCP 流程依次完成 annotation 接纳和 clean replay、依赖快照、VC 检查、两组证明检查、合并后完整检查、final-apply 与 final-check。3 条顶层手工义务均已完成，manual/lib 无 `Admitted`、`Axiom` 或 `Abort`。目标文件与接纳版本的内容/哈希一致。

自动文件仍有 **5 条 safety witness 和 1 条 partial-solve witness 的 `Admitted`**。前者涵盖常量及 `cursor + index`、`index + 1` 的整数范围，后者处理可写单元的资源拆分。goal 中的 `VC_Correct` Axiom 声明是接口，不能再算一份自动结果，但也不能掩盖自动结果仍受信任这一事实。既有逻辑库的基础假设仍属于 QCP 的信任基座。

| 可测过程指标 | 结果 |
|---|---:|
| Annotation 候选 / 修订 | 1 / 0 |
| Annotation 工具失败 | 0 |
| VC 分组 | 2 组 |
| VC 报告格式修复 | 2 次 |
| 证明开发期导入合同失败 | 1 次，未进入 coqc |
| 证明开发期 coqc 失败 | 1 次，helper 名未导入 |
| 最终 group / parent / final 检查 | 全部通过 |
| QCP owner symexec / clean replay | 0.047 / 0.052 秒 |
| QCP controller 墙钟时间 | 1020.140 秒，约 17 分钟 |
| 原 C* 成功重放工具时间 | 31.620 秒 |
| 公共引理补充编译 / assumptions 检查 | 0.259 / 0.282 秒 |

失败修复没有改变契约或不变式：导入限制通过将 helper 陈述展开为官方库 `repeat` 解决；manual 无 helper 导入通过直接证明列表等式解决。VC 报告的两次修复仅涉及解析器要求的章节和字段格式。详细来源见 [process-notes.json](metrics/process-notes.json)，证明开发失败细节来自 owner 在本会话的回报；controller 保存了阶段耗时和最终接受结果，未单独持久化每次失败命令输出。

时间不构成工具速度比较：C* 是现成证明的重放，QCP run 包括阅读、设计、并行工作、报告修复、等待和编排；补充 helper 检查及最终报告整理不在该 run 内。原 C* 历史开发时间、人工活跃时间、模型活跃时间均未知，记录为 `null`。

## 复查与后续

在 `/Users/nizitong/Documents/ChatGPT/Cmc` 执行：

```sh
python3 experiments/cmc_write_zeroes/measure.py
```

重新核验接纳产物哈希、函数 token 和已有验证结果，并生成快照及计量；这不是重新证明 C 函数。`verify_source.py` 可重新执行隔离 C* 重放；`verify_shared.py` 可重放纯公共引理的独立检查。重新验证 QCP C 函数应启动仓库 controller 新 run，不能编辑已完成 run 的封存结果。

本次完成验证后才更新 migration skill。下一单元可迁移 `cmc_concrete_copy_bytes.c`，复用字节数组和列表经验，同时核对源数组保持、别名/分离资源条件及空长度分支。
