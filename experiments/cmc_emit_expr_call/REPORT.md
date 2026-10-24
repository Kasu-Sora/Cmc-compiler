# cmc_concrete_emit_expr_call.c：C* → QCP

2026-10-18 完成整文件三个运行时函数：cm_emit_args_reload_plan、cm_emit_args_store_plan、cm_emit_call_expr。C* 隔离重放通过；QCP run `cmc_emit_expr_call_migration-20261018170809` 为 done、final-check passed。运行时 token、共享 ABI 及复用依赖保持不变。

## 契约与依赖边界

保留原参数列表任意合法表达式域、lvalue 的两种分支、总函数查询、wf/typed/counts、槽布局和表示安全、全局数据大小、temp/scratch/temp_limit 与 PC 起止边界。完整 program/function/expression/argument 资源保持；精确消费计划前缀、追加到 done，任意 tail 保持。不增加 fid 范围、参数表达式种类或额外 codegen 假设。

复用五个已验证 helper 的 BODY 契约：cm_args_length、cm_expr_rvalue_count_context、cm_emit_temp_load_plan、cm_emit_temp_store_plan、cm_emit_call_plan。未导入它们的旧 manual/auto，也不重复计入实现证明。

**外部实现依赖仍为 cm_emit_expr。** 本例按原 C* 头文件的完整契约进行模块化调用，其通用递归函数体尚未迁移，不能把本例通过等同于整个递归 emitter 已验证。新增一般表达式代码模型覆盖全部 14 种构造子，属于数学定义；它不代替通用 emitter 的实现证明。既有 lookup policy/codegen obligations 参数化边界不变。本轮也不构成 HOL→Rocq 元层等价定理或 TVM/编译保持性定理。

## 验证

完成 21 条顶层手工义务、43 个 split，剩余手工义务零。manual 和新增公共库无 Admitted/Axiom/Parameter。另有 60 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。未采用的 Abort split 草稿 2 个。

C* 重放 52.001 秒，退出码 0，verification_conditions/axioms/strategies 为空。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回与终检。

## 工作量

按非空非纯注释物理行分类并去重。proof 包含声明、Proof/Qed 和路由，生成 VC 不计手写 proof。辅助函数 BODY 的契约计规格，导入 helper 的契约单列接入 annotation。行数不是工时或难度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 180 | 51 |
| 函数体 annotation | 35 | 40 |
| helper 接入 annotation | 0（include） | 36 |
| Specification + annotation | 215 | 91 |
| Specification + annotation 含接入 | 215 | 127 |
| 案例 proof | 988 | 613 |

C* 案例 proof = 内嵌 515 行 + 同文件私有证明辅助 473 行。QCP 案例 proof 的实际证明体 421 行，声明/包装 192 行。

此外，QCP 外部类型／逻辑符号声明 72 行、Coq 接入声明 1 行单列，未混入函数体 annotation；库 imports/scopes 为 6 行。完整区间另有 token 和字符计量，以辅助判断格式差异。

### 公共依赖新增成本

QCP 最终案例库新增 12 项定义／74 行，10 条引理／134 行；案例加公共 proof 为 747 行。既有库新增成本零。逐声明区间、引用次数及标注/证明阶段成本见 effort.json。新增但未被 manual 直接引用的引理仍计成本。

源侧对应新增依赖为 175 行模型（扣除此前 leaf/var 方程与基础代码），404 行公共证明闭包；本文件另外有 3 项私有 HD/TL 观察定义／7 行，未混入案例 proof。公共证明的构造函数和定理常量只计一次。

### 逐函数

| 函数 | C* spec | C* annotation | C* 内嵌 proof | QCP spec | QCP annotation | QCP proof |
|---|---:|---:|---:|---:|---:|---:|
| cm_emit_args_reload_plan | 38 | 8 | 134 | 9 | 12 | 98 |
| cm_emit_args_store_plan | 76 | 20 | 283 | 21 | 16 | 293 |
| cm_emit_call_expr | 66 | 7 | 98 | 21 | 12 | 222 |

源同文件私有辅助服务多个函数，不在逐函数表中重复分摊。实际命令调用、失败修复与调度时间见 process-notes.json 和 controller 日志。历史源工时、人工活跃时间及无法独立测量的模型活跃时间为 null；本例是阅读源证明后的迁移成本，不是两体系从零证明的公平效率实验。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_call_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
