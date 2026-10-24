# cmc_concrete_emit_binary_finish.c：C* → QCP

2026-10-18 完成整文件三个运行时函数（含两个 static helper）。C* 隔离重放通过；QCP run `cmc_emit_binary_finish_migration-20261018181500` 为 done、final-check passed。运行时 token、共享 ABI 和旧公共库不变。

## 契约与依赖

保持原 BODY 契约：cm_pointer_scale_value 返回 pointee 的语义大小；cm_emit_binary_generic_fragment 生成 temp-load、swap 和原二元 opcode；cm_emit_binary_finish_plan 按左右指针类型与任意 int op 选择精确指令列表。保留全部原纯事实、program/function/两份 expression 所有权、任意计划 tail 及 done 追加关系。公共函数头文件与实现契约一致。

复用上一例的 cm_pointer_scale、cm_binary_finish_code 模型以及 layout/counts/leaf/core/plan 的既有定义与引理。七个外部 helper 均采用已验证 BODY 契约：cm_expr_type_code_context、cm_type_size_value、cmc_pointee、cmc_is_pointer_value、cmc_binary_opcode、cm_emit_plan、cm_emit_temp_load_plan。没有待迁移的外部实现依赖；导入通用表达式模型库不代表调用通用 cm_emit_expr。

不增加 op 范围、二元表达式类型合法性、fid 范围或 scale 正数前提。本例验证的是生成指令的实现契约，不是所生成指针算术在 TVM 上执行的安全性或编译保持性定理。既有总查询 policy 语义边界不变。

## 验证

40 条顶层手工义务、59 个 split 完成，剩余手工义务为零；127 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。manual 和新增库无 Admitted/Axiom/Parameter。未采用的 Abort split 草稿 0 个。

C* 重放 45.757 秒，退出码 0，verification_conditions/axioms/strategies 为空。QCP 标注验收、独立 VC 审查、分组证明、合并全量检查、写回与终检通过。

## 工作量

非空非纯注释物理行，按分类去重。proof 含声明、Proof/Qed 和路由，不计生成 VC；行数不是工时。QCP 契约采用较长的单行排版，因此 specification 行数不能直接反映表达的信息量；token/字符记录另存。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 122 | 9 |
| 函数体 annotation | 89 | 42 |
| helper 接入 annotation | 0（include） | 18 |
| Specification + annotation | 211 | 51 |
| 上项含 helper 接入 | 211 | 69 |
| 案例 proof | 388 | 713 |
| 公共 proof 新增成本 | 66 | 0 |
| 案例 + 公共 proof | 454 | 713 |

C* 案例 proof = 内嵌 336 行 + 六项私有证明辅助 52 行；QCP 证明体 416 行，声明/包装 297 行。

QCP 新增公共定义 0 项／0 行、引理 0 条／0 行。源新增公共模型 0 行，对应 pointee 编码、wf 和 refs 的公共证明闭包 66 行；其余 pointer bridge、规模、opcode、plan 以及 binary-finish 模型按已复用处理。旧库增量为零。新增但未直接被 manual 引用的引理仍计成本。

QCP 外部类型/逻辑符号声明 35 行、Coq 接入 1 行、公共库 import/scope 1 行另列；effort.json 保留精确区间、token/字符及公共 helper 引用统计。

| 函数 | C* spec | C* annotation | C* 内嵌 proof | QCP spec | QCP annotation | QCP proof |
|---|---:|---:|---:|---:|---:|---:|
| cm_pointer_scale_value | 24 | 4 | 59 | 3 | 2 | 52 |
| cm_emit_binary_generic_fragment | 36 | 10 | 12 | 3 | 4 | 40 |
| cm_emit_binary_finish_plan | 62 | 75 | 265 | 3 | 36 | 621 |

同文件私有支持不在逐函数表重复分摊。实际命令次数、失败修复与 controller 调度时间见 process-notes.json 和日志；未知历史源工时、人工活跃时间及不可独立测量的模型活跃时间为 null。本例比较成品规模和阅读源证明后的迁移成本，不构成两体系从零证明效率的公平实验。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_binary_finish_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
