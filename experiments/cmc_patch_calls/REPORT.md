# cmc_concrete_patch_calls.c：C* → QCP

完成两个运行时函数：static 递归 `cmc_patch_code_arrays` 和公开 `cmc_patch_resolved_calls`，包含必要 proof 支持。C* 隔离重放与 QCP 完整终检通过；run `cmc_patch_calls_migration-20261019152754` 为 `done`。运行体 token、共享 ABI、518 个源 C/H 文件及此前验证依赖保持不变。

## 原契约与对应

内部函数在原 wf/code-ready、长度 0..2147483647 与精确 raw 长度条件下，保持程序上下文和完整函数链表，将两个数组变为 cm_patch_code 的 opcode/immediate 投影。CALL 操作码保持不变，其 immediate 通过已验证 cmc_function_pc_total 的总查询更新；非 CALL immediate 保持原值。没有增加函数编号有效性、raw 必须为模型代码或空数组非空指针前提。

公开函数的 resolved 输入是存在某个 raw 物理缓冲区满足 `cm_patch_code raw = resolved` 的逻辑视图。输出是实际存放 resolved 的普通 emitter 表示；没有假设 raw=resolved 或 patch 幂等。程序资源、字段、容量、未使用数组尾部均保留。

复用 emit-resolved 的 patch 模型与长度定理、emit-core 的双数组表示及指令投影、function-pc-total 的已验证 BODY 契约和公共数组库。任意 signed64 CALL target 的总查询语义保持，PC 返回值的 signed32 安全范围用于写回 signed64。沿用既有 policy/cg 参数化边界。没有导入前序案例生成的自动/手工函数证明。本例完成具体 CALL 回填和 resolved 缓冲区实体化，不新增完整编译保持性或 TVM 执行/终止性定理。

## 验证与信任

C* 重放 66.734 秒，退出码 0，verification_conditions/axioms/strategies 均为空。QCP 完成 6 条顶层手工义务、4 个 split，剩余手工义务为零。另有 14 条自动 witness 以 Admitted 导出，保留自动层信任；manual 和新增库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 0 个单列，不当作已完成 split。

## 工作量

非空非纯注释物理行；proof 含声明、Proof/Qed 和路由包装，排除生成 VC 文本。源 static proof helpers 计入案例 proof，公共新增定义和引理单列。历史 C* 开发工时、人工和无法独立测量的模型活跃时间为 null。此为读取源证明后的迁移成本和成品规模，不能推断两工具从零证明效率。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 36 | 6 |
| 函数体 annotation | 8 | 27 |
| 外部 helper 接入 annotation | 0（include） | 3 |
| Specification + annotation | 44 | 33 |
| 上项含外部 helper 接入 | 44 | 36 |
| 案例 proof | 453 | 120 |
| 新增公共定义 | 5 | 4 |
| 新增公共 proof | 0 | 52 |
| 案例 + 公共 proof | 453 | 172 |

源案例 proof = 303 行内嵌 + 150 行文件私有支持；cm_patch_tail 的 5 行公开定义另列，旧 patch 模型/长度等公共支持不重复计费。目标新增公共定义 2 项、引理 2 条。目标案例证明体 90 行，声明/包装 30 行；新增公共 helper 是否实际使用均在 shared-helper-usage.json 中记录。

逐函数行数（C* / QCP，源 proof 此表不含 150 行文件级私有支持）：

| 函数 | Specification | Annotation | Proof |
|---|---:|---:|---:|
| `cmc_patch_code_arrays` | 21 / 3 | 8 / 12 | 205 / 76 |
| `cmc_patch_resolved_calls` | 15 / 3 | 0 / 15 | 98 / 44 |

源 annotation 6 个条目，目标 6 个块，粒度不同。补充相同正则的词法 token（非模型 token）：

| 项目 | C* token | QCP token |
|---|---:|---:|
| Specification | 378 | 327 |
| 函数体 annotation | 134 | 559 |
| 外部 helper 接入 annotation | 0 | 119 |

外部逻辑声明 25 行、Coq 接入 1 行、公共 import/scope 9 行、重复前向规格 0 行另列。

分组 owner development 11 次（失败 8 次）、debug 0 次（失败 0 次）、exact 3 次（失败 0 次）。控制器验收和 annotation 修复单独记录，避免重复计数。

## 产物与追溯

- [目标 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_patch_calls_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_patch_calls_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_patch_calls_migration_lib.v)
- [完整计量](metrics/effort.json)、[过程](metrics/process-notes.json)、[分组成本](metrics/group-effort.json)
- [语义审计](metrics/semantic-audit.json)、[最终库审查](metrics/final-library-review.json)、[helper 契约](metrics/helper-contract-audit.json)
- [源重放](metrics/cstar-verification.json)、[终检状态](logs/qcp-controller/controller_state.json)、[哈希清单](target/manifest.json)
