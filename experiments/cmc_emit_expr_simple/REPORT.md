# cmc_concrete_emit_expr_simple.c：C* → QCP

2026-10-18 完成整个文件唯一运行时函数 cm_emit_simple_expr。C* 隔离重放通过；QCP run `cmc_emit_expr_simple_migration-20261018164711` 为 done、final-check passed。运行时 token、共享 ABI、emitter 声明和复用库哈希保持不变。

## 契约与模型

源 .c/.h 契约一致。保留原 lvalue 界、simple 条件、wf_program、typed_program、总 f 查询、expr_wf/counts、params/locals slots_wf、structs/globals/strings 与 params/locals 安全事实、全局数据总大小界。完整 program/function/expression 资源保留；精确消费代码前缀并追加至 done，任意 tail 保持。

变量分支调用已验证 cm_emit_var_expr，其余简单表达式调用已验证 cm_emit_leaf_expr。两条 helper BODY 契约与既有版本规范化后一致，不导入旧 manual/auto，也不重复计入 helper 实现 proof。组合代码模型复用 leaf/var 定义；新表示见证需覆盖原简单表达式域，不新增输入限制。

- cm_simple_expr精确对应源leaf-or-kind2；复用已验证cm_dispatch_leaf。
- cm_simple_view只含leaf和var，embedding显式嵌入原cm_expr。coverage双向定理和unique证明表示见证不缩小原合法域。
- cm_simple_code_for直接调用既有leaf/var代码模型，不为其余构造子伪造输出；这些源方程不依赖pc/temp，运行时参数仍保留。
- var分支的slot范围、type_code_wf来自counts，binding_valid来自expr_wf；leaf分支得到既有leaf域。两个helper保留完整上下文及计划。
- 全部源前后置纯事实保留；原policy/codegen obligations参数化边界不变；两个helper BODY契约规范化一致。

既有 cm_lookup_policy、cm_codegen_obligations 和 wf_program 参数化边界保持。源/目标对应由审计记录；本例不是 HOL→Rocq 元层等价定理，不声称整个递归 emitter、TVM 语义或编译保持性迁移完成。

## 验证

完成 7 条顶层手工义务、4 个 split，剩余手工义务零。manual 和新增公共库无 Admitted/Axiom/Parameter。另有 14 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。未采用 Abort split 草稿 0 个。

C* 重放耗时 43.193 秒，退出码0，verification_conditions/axioms/strategies 均为空；507个源 C/H 快照一致。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回及终检。

## 工作量

按非空非纯注释物理行计，同一分类按行号去重。源7个 where 条目占4行。Proof 包含声明、Proof/Qed 和 split 路由；生成 VC 不计手写 proof。行数不代表历史工时或工具难度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 52 | 16 |
| 函数体 annotation | 4 | 29 |
| helper 接入 annotation | 0（include） | 25 |
| Annotation 含接入 | 4 | 54 |
| Specification + annotation | 56 | 45 |
| Specification + annotation 含接入 | 56 | 70 |
| 案例 proof | 23 | 93 |
| 新增公共定义 | 3 | 11 |
| 新增公共 proof | 0 | 22 |

C* 案例 proof 全为内嵌证明；QCP 实际证明体 60 行、声明/包装 33 行。QCP 新增公共定义 4 项、引理 2 条；案例与公共 proof 合计 115 行。

对应源增量仅 cm_simple_expr_def 的 leaf-or-kind2 定义（3行）。既有 leaf/var 方程、代码选择器、count/shape 支持和 helper 实现不重复计费。新增的两条对应引理均已编译，本轮 manual 未直接调用，仍计成本。实际复用 cm_expr_rep_node、cm_dispatch_leaf_coverage，并在新增库中复用 dispatch coverage/unique；引用位置计数见 reused-helper-usage.json 与 shared-helper-usage.json。公共 imports/scopes 5 行、公共自动化 0 行、C Extern 56 行、C Coq import 1 行另列。

实际设计、symexec、development/debug/exact 调用和失败修复见 process-notes.json 及封存 owner 输出。Controller 记录 run 墙钟 15.59 分钟，包含编辑、工具、调度与等待；历史源工时及无法独立测量的活跃时间为 null。这是阅读源证明后的迁移成本，不能作为两体系从零证明的公平效率实验。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_simple_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
