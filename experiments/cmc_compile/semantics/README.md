# cmc_compile 公共语义支持进度

已完成本批 9 个纯 Rocq 公共模块的编译、独立内核检查与假设审计，并已接入 QCP 仓库。**顶层 cmc_compile 的 QCP 验证尚未完成，skill 未更新。**

本批包含实际对象/解码、codegen 条件具体化、数值与字节内存、TVM 28 条指令与执行/终止关系、源值/指针来源/初始化标签/调用/作用域/逐步执行/终止语义，以及内存模拟和终止输出观察支持。复用原 AST、指令、布局、代码/数据模型和已有字节编码证明；未假定 cmc_preservation，也未修改顶层原契约。

新增公共成本按非空非纯注释物理行统计。Proof 包含引理陈述和 Proof/Qed，定义单列；两项可执行相等性判定的证明体另计 2 行。生成的审计代码、测试和工具脚本不计入公共 proof。尚未被顶层 C 案例引用的辅助引理也计入本批成本。

| 模块 | 定义/数据类型 | 引理 | 定义行 | Proof 行 |
|---|---:|---:|---:|---:|
| `cmc_preservation_observation_migration_lib.v` | 26 | 5 | 50 | 14 |
| `cmc_simulation_state_migration_lib.v` | 25 | 17 | 39 | 101 |
| `cmc_source_call_migration_lib.v` | 24 | 9 | 74 | 26 |
| `cmc_source_execution_migration_lib.v` | 30 | 9 | 140 | 36 |
| `cmc_source_initial_migration_lib.v` | 22 | 11 | 45 | 30 |
| `cmc_source_state_migration_lib.v` | 60 | 10 | 142 | 31 |
| `cmc_tower_semantics_migration_lib.v` | 20 | 15 | 243 | 30 |
| `cmc_tvm_execution_migration_lib.v` | 30 | 12 | 268 | 31 |
| `cmc_tvm_object_migration_lib.v` | 39 | 20 | 68 | 71 |

合计：276 项定义/数据类型，108 条引理；定义 1069 行，proof 370 行（引理 368 + 判定证明 2）。这些是目前已完成的公共增量，最终公共闭包成本仍未知。源同名/同类型声明链接见 `metrics/source-matched-declarations.json`；它不包括对应证明构造器完整闭包，不能拿其行数计算 proof 比率。

验证证据：

- `metrics/checkpoint.json`：本批验收状态；顶层完成标志明确为 false。
- `logs/028-development-SemanticsAudit.log`：逐项签名和 Print Assumptions；110 项均 closed。
- `logs/029-kernel-SemanticsAudit.log`：coqchk 退出 0，耗时约 291.9 秒，无 unsafe fixpoint、type-in-type 或 assumed positivity。
- `metrics/publication.json`：QCP 正式目录中的 9 个模块全部编译通过。
- `metrics/canonical-reused-checks.json`：24 个原样复用库的重编译，新增源代码成本为 0。
- `target/SemanticsRegression.v`：12 项执行回归，覆盖常量、短路、调用/I/O、循环、全局字节和错误分支；不替代通用保持性证明。

QCP 传递导入环境含原有逻辑/分离逻辑公理，coqchk 的环境清单会列出它们；新证明的逐项假设审计均不依赖这些公理。没有新增 Axiom、Parameter、Admitted 或 Abort。

语义边界：总列表查询保留 HOL 的 NIL/负索引解释参数，并证明合法索引与原有查找的一致性；没有通过新增合法输入前提抹去非法索引分支。TVM 用 Forall 的地方给出与受界索引谓词的等价证明。源执行保留原最小闭包定义，并证明等价有限步见证与确定性。源初始内存与 TVM 装载内存直接证明相等。字符/整数/指针加载和初始化字节存储模拟是带明确局部模拟前提的辅助引理，不是顶层保持性结论。

仍需迁移的连接见 `metrics/remaining-obligations.json`：实际 annotation 更新/擦除、18 项保持性不变量及 initial/step/iter、成功执行模拟、cmc_preservation、cmc_compile_success_bridge，再恢复原 annotation owner 完成 C 资源标注/VC/终检。当前仍不具备这些根定理；不能把本批结果解释成编译器或顶层 C 验证通过。

重放公共库：按 publish.py 中的依赖序，运行 `python3 check.py development <模块名>`；`audit.py` 生成签名/成本审计；`python3 check.py development SemanticsAudit` 与 `python3 check.py kernel SemanticsAudit` 执行独立验证。所有完整命令、退出码和开发失败尝试保存在 metrics/checks.json。完整源 C* 重放此前已经通过，本批未重复运行。
