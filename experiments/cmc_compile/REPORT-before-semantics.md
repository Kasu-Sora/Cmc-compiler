# cmc_compile：迁移已启动，尚未验证通过

方向为 C* → QCP，范围是顶层 `cmc_compile` 及保持其完整原契约所需的支持。controller run：`cmc_compile_migration-20261019230022`。当前结果是 annotation 阶段的 `dependency-gap`；尚未生成 VC、未执行目标 symexec／Rocq 验证。`target/` 中只有未验证的运行时代码种子和空库脚手架，不能作为可用的 QCP 迁移成品。

## 已确认的契约

输入是原 `cm_program_rep` 与 `cm_output_pre`。容量失败时仍先设置所需 code/data 长度和 entry=-1，返回 1，保留完整程序及缓冲区资源。成功时返回 0、entry=0，输出模型的精确代码／数据前缀并保留未使用的缓冲区尾部。

原成功后置条件还包含：对任意解码对象、输入、输出和退出状态，源程序正常终止蕴含解码对象上的 TVM 正常终止且观察一致。仅证明缓冲区等于模型，不能替代这项性质。

## 阻塞与恢复顺序

1. 迁移实际 TVM 对象、装载、状态及执行／终止语义，以及源程序运行状态与执行／终止语义；复用既有 AST 和指令类型。
2. 为现有参数化 codegen 条件提供原定义的具体实例，迁移 `cm_compile_model`、`cm_output_decodes`、解码唯一性及模型解码定理。
3. 迁移必要执行模拟／保持性依赖，证明 `cmc_preservation`，再重建 `cmc_compile_success_bridge`。
4. 恢复原 annotation owner，完成资源标注、VC 证明和 controller 终检。

精确源位置、缺失符号、恢复边界与依赖清单见 [annotation 审计](logs/agent_output.md)。现有所有 Rocq 源中未找到上述语义与保持性声明；这是尚未迁移的逻辑支持，不是缺少已编译文件。

当前 annotation owner 的授权文件范围是案例 C/lib/generated，且不负责手工 proof 或公共第二库；`verification-orchestrator` 要求 main “只编排”，不能以主代理越过角色边界补写这些证明。遵循迁移 skill 的“不得静默用公理替代证明”，本轮保留未完成状态，不加强输入、不削弱输出、不引入假定的保持性。

controller 已接受 blocked 报告，随后返回的 `retry-round` 命令发生 `FileNotFoundError`：pre-VC 阶段没有 `cmc_compile_migration_proof_manual.v`，重试逻辑却要求该文件。命令、路径及状态见 [机器记录](metrics/status.json)。没有伪造 manual、修改 controller 状态或重开 run 来绕过检查。公共依赖完成后，还需处理这一恢复入口问题。

## 工作量：仅源基线已测，目标最终成本未知

按非空、非纯注释物理行统计。头文件重复契约不重复计入。源数据可由 `extract_source.py` 和 `measure_source.py` 重建。

| 分类 | C* 源基线 | 本次 QCP 已验收产物 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行／2 条 | 未完成 |
| Specification + annotation | 14 行 | 未完成 |
| 函数内 proof | 435 行 | 未完成 |
| 同文件私有 proof 支持 | 64 行 | 未完成 |
| 案例 proof 小计 | 499 行 | 未完成 |
| 同文件公开 success bridge proof | 42 行 | 未完成 |
| getter 脚手架，单列 | 3 行 | 未完成 |
| 其他初始化／审计支持，单列 | 29 行 | 未完成 |
| 新增外部公共依赖完整成本 | 尚未完成定理级闭包计量 | 未完成 |

541 行是案例 proof 与同文件公开 bridge 的合计，不含外部 preservation 等公共支持，不能作为完整证明总成本。已记录部分外部根声明大小于 `metrics/preservation-root-source-size.json`，它明确不代表完整公共增量成本。

本次没有新增已验证的 QCP 定义／引理，没有完成的目标 annotation/proof。最终成本以 null 表示，不能把尚未开展的工作记为零成本，也不计算两边比率。源历史开发时间、人工活跃时间均未知。

`#require` 装载闭包包含 257 个源条目，其中可能含示例及未用定理；它只用于依赖审计，不等于 257 个新增待迁移模块，也不作为 proof effort。既有 185 个目标文件和 518 个源 C/H 文件的哈希基线已保存并核对无变化。

## 验证与文档状态

源 C* 首次重放达到 600 秒外部时限后超时；修复包装器并将本轮时限设为 1800 秒后，完整重放在 1040.281 秒通过，退出码 0，verification_conditions、axioms、strategies 均为空。最新结果见 `metrics/cstar-verification.json`，首轮超时证据仍保存在原日志目录。QCP 目标尚未验证。skill、迁移计划及完成状态清单均未更新；验证通过后再更新。

初始基线建立曾因相对路径 cwd 错误失败，随后改用绝对路径成功；controller 初始 Python 3.9 调用被版本检查拒绝，随后使用要求的 Python 3.12；一次 step 使用了错误参数 `--run-id`，改为公开参数 `--run` 后成功。这些是准备／命令错误，不计为证明失败或 annotation 修订。

## 超时排查与重试（2026-10-19）

首轮 600 秒是实验 Python 包装器的 `subprocess.run(timeout=600)`，不是 C* 的逻辑失败。原终止栈位于 `cmc_preservation_ready_semantic.c` 的规则去重／语义 readiness 证明。关闭 prover 后产生的 RPC 断连不能当作先行根因。

`verify_source.py` 已增加 `--timeout-seconds`（默认 3600）、30 秒心跳、CPU／RSS 记录、每次独立 attempt.json、自动保存超时状态和整个客户端进程组清理。先终止客户端，再清理服务器，避免孤立子进程以及误导性的断连日志。保留编译对象，但不把对象缓存视为已证明定理缓存；每次仍由新 HOL 服务器重放。验证前检查全部 518 个源 C/H 哈希。

当前重试命令：

```sh
python3 /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile/verify_source.py --timeout-seconds 1800
```

重试已通过：验证耗时 1040.281 秒（约 17 分 20 秒），含服务器启动／清理总耗时 1045.464 秒；退出码 0，verification_conditions、axioms、strategies 均为空。此次问题确认为 600 秒外部预算不足，1800 秒预算足以完成本次完整重放。日志位于 `logs/20261019T151758968928Z-cstar-source/`。采样记录显示从 readiness 推进到执行保持性、semantic readiness，再到 budget preservation，未修改任何源证明。该结果不意味着 QCP 顶层迁移已完成。
