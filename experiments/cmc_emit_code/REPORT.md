# cmc_concrete_emit_code.c：C* → QCP

完成唯一运行时函数 `cmc_emit_code` 及必要 proof 支持。C* 隔离重放通过；QCP run `cmc_emit_code_migration-20261019112556` 为 `done`，完整终检通过。运行体 token、共享 ABI、518 个源 C/H 文件和此前验证依赖保持不变。

## 原契约与目标对应

保留原 wf/typed、从 fid 0 开始的完整 functions readiness、结构体/全局/字符串表示安全以及数据总大小不超过 1048560 的事实，并在后置条件中恢复这些事实。程序上下文与整个 program-functions 链表资源均保留。输出精确为 `cm_emit_prelude p ++ cm_emit_functions p 0 (cm_program_functions p)`，追加到任意 done，保留任意 tail。

运行时读取 functions 指针后调用两个已有 helper：先 prelude，再以 fid=0、function_pc=11 发射完整函数列表。接入契约均与已验证 BODY 契约核对一致。PC-zero 在证明内部推导，没有新增调用方前提。沿用既有 lookup-policy/codegen-obligations 参数化边界。

复用 prelude/functions、上下文、readiness、计划发射及计数等公共模型。没有导入前序案例的自动或手工函数证明。本例是模块化具体 emitter 实现验证，不新增 raw 输出 patch/link 正确性、编译保持性或 TVM 执行/终止性定理。

## 验证

C* 重放 46.515 秒，退出码 0，verification_conditions/axioms/strategies 均为空。QCP 完成 3 条顶层手工义务、3 个 split；剩余手工义务为零。另有 5 条自动 witness 以 `Admitted` 导出，保留 QCP 自动层信任；manual 和新增库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 0 个另列。

## Annotation / proof 工作量

统计非空非纯注释行。proof 包括声明、Proof/Qed 和顶层路由，排除生成 VC 文本。历史 C* 开发时间、人工时间、无法独立测量的模型活跃时间为 null。该统计是读取源证明后的迁移成本及成品规模，不能直接推断从零证明效率。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 41 | 3 |
| 函数体 annotation | 0 | 21 |
| helper 接入 annotation | 0（include） | 6 |
| Specification + annotation | 41 | 24 |
| 上项含 helper 接入 | 41 | 30 |
| 案例 proof | 23 | 46 |
| 新增公共定义 | 4 | 2 |
| 新增公共 proof | 11 | 0 |
| 案例 + 公共 proof | 34 | 46 |

源新增公共定义为 cm_model_code 的 4 行组合方程；新增公共 proof 为 cm_function_pc_zero 及其证明构造器共 11 行，已覆盖的 prefix-zero 及其他依赖不重复计费。源案例 proof 为 23 行内嵌证明，无文件私有支持。目标新增公共定义 1 项，引理 0 条；实际引用情况在 shared-helper-usage.json 中。目标案例证明体 28 行，声明/包装 18 行。

源 annotation 0 个条目，目标 4 个块，粒度不同。补充相同正则的词法 token（不是模型 token）：

| 项目 | C* token | QCP token |
|---|---:|---:|
| Specification | 327 | 300 |
| 函数体 annotation | 0 | 574 |
| helper 接入 annotation | 0 | 443 |

外部逻辑声明 27 行、Coq 接入 1 行、公共 import/scope 5 行另列。旧依赖的定义和引理复用不重复计新增成本。

分组 owner development 6 次（失败 5 次）、debug 2 次（失败 0 次）、exact 1 次（失败 0 次）。控制器验收、标注修复与失败原因见过程记录，不与 owner 调用重复计数。

## 产物与追溯

- [目标 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_code_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_code_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_code_migration_lib.v)
- [完整计量](metrics/effort.json)、[过程](metrics/process-notes.json)、[分组成本](metrics/group-effort.json)
- [语义审计](metrics/semantic-audit.json)、[最终库审查](metrics/final-library-review.json)、[helper 契约](metrics/helper-contract-audit.json)
- [源重放](metrics/cstar-verification.json)、[终检状态](logs/qcp-controller/controller_state.json)、[哈希清单](target/manifest.json)
