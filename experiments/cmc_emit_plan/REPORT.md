# cmc_concrete_emit_plan.c：C* → QCP

全部八个运行时包装函数已迁移。C* 原证明隔离重放通过；QCP run `cmc_emit_plan_migration-20261017135154` 为 done、final-check passed。运行时函数 token、cm_emitter 声明、共享 ABI 和复用依赖哈希均保持不变。

## 契约与复用

新 `cm_resolved_emitter_plan_rep` 精确对应原定义：`Zlength(done)+Zlength(todo)<=capacity` 的纯事实，加上既有的 `cm_resolved_emitter_rep ... done`。todo 表示逻辑上的剩余容量预算，不额外拥有物理缓冲区，也不要求它等于程序代码、有效指令列表或某个可达后缀。

八个包装函数从 todo 消耗各自的精确 fragment，将相同 fragment 追加至 done，并保持 tail 不变。普通指令保留 opcode 编码相等与非 CALL 限制；normalize/load/store 仅保留原编码相等及 type-code-wf；fp-address 保留原精确片段。临时变量两函数在前后置中均保留八项纯事实及完整 function-context 资源，不增加 fid 合法性或边界。

CALL 的计划片段是逻辑上的 CALL(cm_function_pc policy p function_id)，实际仍调用 resolved helper 写入原函数编号。接受所有 signed int function_id，包括负数和越界编号；没有新增 readiness、程序 wf 或 PC 可表示性前提。使用同一个既有 total cm_lookup_policy。

完整复用已验证 resolved 库及其 core/counts/layout 等依赖。八个 resolved helper 契约规范化后逐字一致；只接入契约，没有重复计入 helper 实现证明或导入旧 manual/auto。实际 selected dependency snapshot 已与冻结依赖哈希核对。

## 验证与信任边界

完成 16 条顶层手工义务、32 个 split，八个函数均有生成义务覆盖，剩余手工义务为零。另有 16 条自动 witness 以 Admitted 导出，依赖 QCP 自动层；手工证明及新增公共库无 Admitted/Axiom/Parameter。未采用的 Abort split 草稿为 0 个。

C* 重放退出码 0，verification_conditions/axioms/strategies 均为空，耗时 39.712 秒。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回及终检。本例验证计划包装函数，未覆盖物理 CALL 回填 pass、完整 TVM 执行或整个编译保持性。

## 工作量

以下为非空非纯注释物理行；自动生成的 VC 文本排除。C* 内嵌 proof 和私有支持函数计入案例 proof；QCP proof 包括声明、Proof/Qed 包装与 split 路由。QCP 的契约常排成长行，不能用物理行数比例判断工作时间或效率。词法 token、字符量及标注条目另见 source-text-size.json 与 annotation-entry-counts.json。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 117 | 24 |
| 函数体 annotation | 22 | 43 |
| 既有 helper 接入 annotation | 0（include） | 24 |
| Annotation 含接入 | 22 | 67 |
| Specification + annotation 含接入 | 139 | 91 |
| 案例 proof | 100 | 336 |

C* 案例 proof 含内嵌 67 行、两个私有容量辅助函数的 33 行。QCP 案例 proof 为证明体 192 行、声明/包装 144 行。

公共新增成本：QCP **1 项定义／4 行，1 条引理／7 行**；案例及新增公共 proof 合计 343 行。对应源库有 1 项计划定义／6 行，以及两个公开的 cm_plan_open/cm_plan_close 证明辅助函数（含私有 cm_plan_fragment_term，共 52 行）。源公开 helper 是操作符号状态的 PROOF 例程，并非两个独立 HOL 定理；其历史编写时间未知。源案例加这部分公共 proof 共 152 行。

已有公共依赖按零新增计入。本次所有新定义、引理均按最终合并库计量，使用情况和阶段增量见 effort.json；不以公共池条目数推断引理数。导入/作用域 9 行、公共自动化/配置 0 行、C Extern 50 行、C Coq import 1 行另列。

| 函数 | C* spec | C* ann | QCP spec | QCP ann | QCP 案例 proof |
|---|---:|---:|---:|---:|---:|
| cm_emit_plan | 11 | 2 | 3 | 6 | 44 |
| cm_emit_call_plan | 9 | 1 | 3 | 5 | 44 |
| cm_emit_normalize_plan | 11 | 2 | 3 | 5 | 40 |
| cm_emit_load_plan | 11 | 2 | 3 | 5 | 40 |
| cm_emit_store_plan | 11 | 2 | 3 | 5 | 40 |
| cm_emit_fp_address_plan | 8 | 1 | 3 | 5 | 40 |
| cm_emit_temp_store_plan | 28 | 6 | 3 | 6 | 44 |
| cm_emit_temp_load_plan | 28 | 6 | 3 | 6 | 44 |

标注阶段 design、symexec、post-lib 各一次通过。证明阶段共 13 次 development 检查（9 次失败）、6 次 debug（2 次失败）、4 次 owner exact 检查全部通过；四组 controller 验收均首次通过。修正集中在预处理已闭合后的冗余 tactic、空间/纯子目标顺序及 debug scope/import；没有修改契约或新增证明阶段公共引理。

QCP run 墙钟 19.43 分钟，包括编辑、调度、检查及等待。历史源工时、不可独立测量的活跃时间记 null。修订、失败检查和验收次数保留在 process-notes.json。这是读取现有源证明后的迁移实验，不是两套工具从零的公平效率比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_plan_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_lib.v)
- [计量明细](metrics/effort.json)、[契约审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [过程](metrics/process-notes.json)、[C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
