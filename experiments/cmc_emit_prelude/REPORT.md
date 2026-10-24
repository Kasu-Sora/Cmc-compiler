# cmc_concrete_emit_prelude.c：C* → QCP

完成唯一运行时函数 `cmc_emit_prelude` 及必要 proof 支持。C* 隔离重放通过；QCP run `cmc_emit_prelude_migration-20261019110655` 为 `done`，完整终检通过。运行体 token、共享 ABI、518 个源 C/H 文件与此前验证依赖均保持不变。

## 契约和实现

前置条件仅包含 program-context 和 resolved emitter-plan 资源，后置条件保留相同上下文，并把精确 prelude 指令序列追加到任意 done、保留任意 tail。没有新增 wf/typed、readiness、main_id 非负或有效入口等限制。CALL 仍采用既有 lookup-policy 参数化的总 PC 查询。

输出恰好为 11 条指令：PUSH 1048576、PUSH 8、STORE 0、CALL main 的总函数 PC、PUSH 256、MOD 0、PUSH 256、ADD 0、PUSH 256、MOD 0、HALT 0。运行时只读取 program->main_id，然后逐条调用已有计划发射函数。

两个 helper `cm_emit_plan` 和 `cm_emit_call_plan` 接入契约与已验证 BODY 契约一致；复用原程序上下文、堆表示、指令模型、计划及总查询。源文件的 emit-functions 构建依赖不代表运行时调用；目标只导入实际需要的公共模型闭包。本例是模块化发射实现验证，不新增 main 执行、终止性、链接或编译保持性定理。

## 验证与信任边界

C* 重放 46.238 秒，退出码 0，verification_conditions/axioms/strategies 均为空。QCP 完成 3 条顶层手工义务和 7 个 split，剩余手工义务为零。另有 41 条自动 witness 以 `Admitted` 导出，保留 QCP 自动层信任；manual 和新增库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 0 个另列。

## 工作量

计量非空非纯注释行；proof 包含声明、Proof/Qed 和路由包装，排除生成 VC 文本。历史 C* 开发时间、人工时间、无法独立测量的模型活跃时间均为 null。此为成品规模和读取原证明后的迁移成本，不是从零证明效率对比。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 11 | 3 |
| 函数体 annotation | 21 | 28 |
| helper 接入 annotation | 0（include） | 6 |
| Specification + annotation | 32 | 31 |
| 上项含 helper 接入 | 32 | 37 |
| 案例 proof | 24 | 64 |
| 新增公共定义 | 9 | 6 |
| 新增公共 proof | 0 | 0 |
| 案例 + 公共 proof | 24 | 64 |

源案例 proof 为 24 行内嵌证明，无新增文件私有支持；源公共增量是 9 行 cm_emit_prelude 指令模型，已有 proof 支持不重复计费。目标新增定义 1 项，引理 0 条，公共成本与案例证明分开。目标证明体 34 行、声明/包装 30 行。

源 annotation 21 个条目，目标 13 个标注块，粒度不同。补充相同正则的词法 token（不是模型 token），避免以长行压缩误判工作量：

| 项目 | C* token | QCP token |
|---|---:|---:|
| Specification | 113 | 115 |
| 函数体 annotation | 401 | 2217 |
| helper 接入 annotation | 0 | 231 |

外部逻辑声明 19 行、Coq 接入 1 行、公共 import/scope 4 行另列。实际复用依赖及旧引理引用均记录在 effort.json，不新增计费。

分组 owner 调用 development 5 次（失败 4 次）、debug 4 次（失败 1 次）、exact 1 次（失败 0 次）。控制器验收和 annotation 修复单独记录，避免重复计数。

## 产物与追溯

- [目标 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_prelude_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_prelude_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_prelude_migration_lib.v)
- [完整计量](metrics/effort.json)、[过程](metrics/process-notes.json)、[分组工作量](metrics/group-effort.json)
- [语义审计](metrics/semantic-audit.json)、[最终库审查](metrics/final-library-review.json)、[helper 契约](metrics/helper-contract-audit.json)
- [源重放](metrics/cstar-verification.json)、[终检状态](logs/qcp-controller/controller_state.json)、[产物哈希](target/manifest.json)
