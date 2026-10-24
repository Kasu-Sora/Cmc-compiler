# cmc_copy_bytes：C* → QCP 迁移与工作量

2026-10-15。`cmc_concrete_copy_bytes.c` 中的 `cmc_copy_bytes` 已完成迁移。原 C* 证明重放通过；QCP run `cmc_copy_bytes_migration-20261015183239` 最终为 `done`，`final_check.status` 为 `passed`。原契约含义、零长度早退和运行时代码均保留。

**4 条顶层手工义务及其 6 个子目标全部完成；另外 7 条自动结果以 `Admitted` 导出，仍信任 QCP 自动求解器。** 本次 manual 和 case lib 没有新增 `Admitted`、`Axiom` 或未完成证明。不能把完整结果表述为没有可信自动结果假设的独立 Rocq 内核证明。

## 交付

- [正式 QCP C 文件](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_copy_bytes_migration.c)
- [正式案例 proof](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_proof_manual.v)
- [公共纯定义](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_lib.v)
- [目标快照与哈希](target/manifest.json)、[原始版本和基线](baseline/manifest.json)
- [逐区间工作量数据](metrics/effort.json)、[C* 验证结果](metrics/cstar-verification.json)、[QCP 最终状态](logs/qcp-controller/controller_state.json)

范围覆盖本复制函数及其必要依赖，不代表 CMC/TVM 的整体模型和编译保持性证明已经迁移。

## 契约与运行行为保持

| 项目 | 原 C* | QCP |
|---|---|---|
| 逻辑参数 | `prefix`、`bytes`，整数列表 | 两个 `list Z` |
| 长度与容量条件 | `0 <= length`、`ilength bytes = length`、`0 <= cursor`、`cursor + length <= capacity`、`capacity <= 2147483647` | 对应条件全部保留，长度用 `Zlength` |
| 源缓冲区 | `cm_uint8_buffer source bytes` | `cmc_uint8_buffer_nonnull(source,bytes)` 与 `UCharArray::full(source,length,bytes)` |
| 目标初始化前缀 | 长度 `cursor`、内容 `prefix` | `UCharArray::seg(data,0,cursor,prefix)` |
| 目标未初始化后缀 | 从 `data + cursor * sizeof Tuchar` 开始，长度 `capacity - cursor` | `UCharArray::undef_seg(data,cursor,capacity)` |
| 后置源资源 | 源指针与完整 `bytes` 内容保持 | 保留相同纯条件和完整源数组 |
| 后置目标资源 | 前缀变为 `prefix ++ bytes`；剩余后缀仍未初始化 | 相同内容及 `[0,cursor+length)` / `[cursor+length,capacity)` 分割 |

源 `cmc_rep.c:961–965` 的真实定义是：空 `bytes` 对应 `emp`；非空时要求源指针非零并拥有完整初始化数组。目标新增纯定义：

```coq
Definition cmc_uint8_buffer_nonnull (p : Z) (bytes : list Z) : Prop :=
  bytes = [] \/ p <> 0.
```

在 `Zlength(bytes)=length` 下，`UCharArray.full(source,0,[])` 展开为恒真的长度等式及 `emp`，不限制源指针。因此目标组合恰好保留空／非空两种资源情况：**零长度允许空或任意源指针，不占用源单元；非空时明确要求非空源指针**。目标后置的 `full` 保留了原长度事实，这一事实与未修改的参数、逻辑列表及入口条件一致，不增加调用者负担。

源和目标各区域之间继续使用分离合取。不额外加入 `source != data`，也不把原分离资源契约扩大成支持重叠的 `memmove` 契约。没有要求整个目标数组已初始化，没有添加正长度前提。

原函数的 `length == 0` 早退、if 后的分号、`index < length` 循环、局部 `unsigned char byte` 读取、写入和递增全部保留。`measure.py` 从原 C* 源文件移除证明语法后，与目标移除标注后的 C token 比较相等；提取结果在 `metrics/runtime-cstar.c`、`metrics/runtime-qcp.c`。没有改成 `memcpy` 或调用 `cmc_write_byte`。

## 列表和数组语义核对

实际 C* 模型探测见 [日志](logs/20261015T103348Z-cstar-model-probe/stdout.txt)：

- `sublist lo hi l = SKIPN (num_of_int lo) (FIRSTN (num_of_int hi) l)`。
- `ilength [] = 0`，`ilength (h::t) = 1 + ilength t`。
- `inth n l = NTH (num_of_int n) l`。

目标 `Rocq/listlib/Base/Positional.v` 的 `sublist` 同样先 `firstn` 再 `skipn`，索引用 `Z.to_nat`；`Znth n l default` 使用 `nth (Z.to_nat n)`。本循环保证非负索引且读取位置在列表长度内，因此默认元素不影响读取结果。生成义务中的局部 `byte` 确实绑定到 `Znth index bytes 0`，而不是无约束符号。

目标 `ArrayLibCore.v` 的 `full` 经 `store_array` 展开为从 0 开始的 `store_array_rec`；后者空列表分支为端点相等等式和 `emp`。相关库、字节元素实例及哈希保存在 `baseline/qcp-reused/`。

以上是原生逻辑中的语义对应审查；本次没有构造两套证明器的内存模型等价定理。

## Annotation 与 proof 工作量

口径为最终非空物理行，含语法包装，排除纯注释和独立的 QCP `*/`。头文件中重复契约只计一次。Specification 与函数体 annotation 分开，C* 内联 proof 块计 proof；目标 proof 区域包括 Lemma 陈述、`Proof/Qed`、证明路由和实际证明体，自动生成的 VC 定义、文件导入及空模板不另计手写 proof。

| 最终规模 | C* | QCP |
|---|---:|---:|
| Specification | 16 行 | 12 行 |
| Annotation | 25 行 | 12 行 |
| Specification + annotation | 41 行 | 24 行 |
| 案例 proof | **232 行** | **75 行** |
| 循环不变式 | 1 个 | 1 个 |
| 逻辑列表参数 | 2 个 | 2 个 |

C* 的 232 行由 **215 行内联 proof（6 块）+ 17 行案例私有辅助证明**组成。后者包括列表零长度引理及缓存结果、源缓冲区展开的证明包装，不能遗漏，也不应误计成新建公共库。

QCP 的 75 行包含 4 个顶层 Lemma 与 6 个 split Lemma；其中证明体 45 行，声明及 `Proof/Qed` 30 行。这是 **4 条独立顶层手工义务**，不是 10 条。三个证明组分别完成：

1. 入口：从非零长度和纯定义推出非空源指针；建立空复制前缀。
2. 循环步骤：使用现有 `sublist_split`、`sublist_single`、`app_assoc` 和线性算术完成前缀扩展。
3. 返回：空长度推出 `bytes=[]`；正常退出推出 `index=length`，用 `sublist_self` 还原完整输出，并恢复纯源条件。

原 C* 导入/常量导出另列 10 行；QCP 外部声明 5 行（4 个名字）、case-lib 导入标注 1 行、库 seed 3 行。原头文件同步表达的逻辑契约已经体现在目标函数契约中，不要求一源文件对应一个目标文件。

这些是最终产物规模和读过原证明后的迁移记录，不是两套工具从零证明的公平耗时实验。

## 公共定义和引理新增成本

| 本次新增公共内容 | 数量 | 非空行 |
|---|---:|---:|
| 纯规格定义 `cmc_uint8_buffer_nonnull` | 1 | **2** |
| 新堆表示或递归数学模型 | 0 | 0 |
| 公共辅助引理及证明 | 0 | **0** |
| C 中接入 case-lib 的 Import Coq 标注 | 1 | 1 |
| controller 创建的库 seed | — | 3 |

新增定义只提取原缓冲区表示的纯非空条件；现有 `UCharArray.full` 负责堆资源。定义被前后置条件引用，manual 在入口/退出证明中实际展开；目标 goal/manual 均导入该库，库设计编译和完整依赖检查通过。它进入了本例编译闭包，未像前例的未引用 helper 那样需要独立补充编译。

源侧既有 `cm_uint8_buffer` 定义 5 行单列为依赖参考，不算本次新建成本。目标已有数组策略、`Zlength`、`sublist` 和相关引理直接复用，没有为增加迁移量而重写。上例 `zeros_snoc__zero_step` 不适用于任意字节复制，本例没有使用它。

## 验证与信任边界

C* 0.5.7 在隔离副本中验证原始文件，退出 0，`verification_conditions`、`axioms`、`strategies` 三个列表为空。工具链和标准库固定版本见 `baseline/cstar-stdlib.json`；未修改原证明。

QCP 完成 annotation 接纳及 clean replay、固定依赖准备、VC 分组、三组检查、合并后完整验证、final-apply 和 final-check。正式文件与接纳版本、合并版本的哈希一致；manual/lib 无手写公理或未完成证明。

自动导出共 **7 条 `Admitted`**：5 条 safety 和 2 条 partial-solve。前者验证常量及地址/计数加法范围；两条 partial-solve 分别拆出源读取单元和目标可写单元，源资源的恢复由现有数组策略完成。它们属于 QCP 可信自动结果，未改写或删除。goal 中的 `VC_Correct` 接口声明不再重复计数。既有 QCP/Rocq 逻辑库仍属于其信任基座。

## 过程与失败记录

| 过程指标 | 结果 |
|---|---:|
| Controller annotation attempt | 1 |
| Owner symexec 调用 | 2，第一次失败、第二次通过 |
| Annotation 修订 | 同一 attempt 内 1 次语义等价表达调整 |
| 因证明缺口返回 annotation 的轮次 | 0 |
| VC 报告格式修复 | 1 次 |
| 证明期 coqc 失败 | 2 次 |
| 结构/导入合同失败、工具故障 | 0 / 0 |
| 最终 group / parent / final 检查 | 全部通过 |
| QCP owner symexec 总时间 / clean replay | 0.099 / 0.081 秒 |
| QCP controller 墙钟时间 | 1119.972 秒，约 18.7 分钟 |
| C* 成功重放工具时间 | 31.589 秒 |

首轮入口直接写纯析取时，QCP 产生多个未命名前置分支，`@pre` 报不明确。修复为等价的命名纯定义并合法导入，未改变允许输入域、资源或运行时代码。不要将 controller 的 `annotation_repair_count=0` 解释为“没有修订”：它只表示没有因 VC 缺口新建 annotation round。

VC 报告修复为添加解析器要求的 `Structural Blocker Scan` 章节。两次 coqc 失败分别发生在入口组、返回组，均因顶层 `Goal_apply` 分支顺序不匹配；调整为空间分支先行后通过。未新增证明假设，未改 VC 陈述。

[过程记录](metrics/process-notes.json) 包含失败原因与修复。Annotation 失败另有 owner 报告和 controller generation receipt；两次证明失败的具体原因来自 owner 在本会话的终态回报，controller 保存阶段耗时和最终接纳状态，未逐次持久化失败 coqc 的完整输出。

原 C* 历史开发时间、人工活跃时间、模型活跃时间未知，记录为 `null`。C* 重放时间不能与包含阅读、设计、分组、等待、修复和编排的 QCP 墙钟时间作速度比较；报告整理及 skill 更新也不在 controller run 内。

## 复查与下一步

在 `/Users/nizitong/Documents/ChatGPT/Cmc` 执行：

```sh
python3 experiments/cmc_copy_bytes/measure.py
```

这会重新核对正式产物哈希、已有验证结果、运行时 token 和计量区间；不会重新运行 QCP 证明。`verify_source.py` 可重放隔离 C* 验证，`probe_model.py` 可复核源列表定义。重新验证 QCP C 函数应启动仓库 controller 新 run，不改已封存 run 的结果。

迁移 skill 在完整验证通过后更新，加入空缓冲区语义、`@pre` 分支歧义的本例修复、case-lib 实际导入以及私有辅助证明计量经验。下一单元可按路线检查 `cmc_concrete_emit_word.c`，先核对 64 位整数和字节编码支持。
