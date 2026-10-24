# cmc_concrete_emit_expr_dispatch.c：C* → QCP

整个文件的唯一运行时函数 cm_emit_leaf_expr 已完成迁移。C* 隔离重放通过；QCP run `cmc_emit_expr_dispatch_migration-20261017164114` 为 done、final-check passed。运行时 token、共享 ABI、emitter 声明和复用库哈希保持不变。

## 契约与模型

源 .c/.h 契约一致。保留 lvalue[0,1]、leaf 条件、wf_program、typed_program、总 f 查询、expr_wf、expr_counts_representable、structs/globals/strings 安全与全局数据总大小界；保留完整 program/function/expression 资源，精确消费代码计划前缀并追加至 done，任意 tail 保持。

该函数按 kind 分派 Const、String、Sizeof、Getc。复用上一案例的叶子类型及代码模型；原 kind 析取与存在叶子表示之间的覆盖关系有本地 Rocq 引理支持，不额外限制原合法输入。四条 helper 契约与已验证 leaf 实现版本规范化后一致。其中 const 使用已验证函数体契约，从原 expr_wf 的整数类型条件推出类型编码合法性（counts 也可推出），未把该事实作为 dispatch 的新增输入前提。

- cm_dispatch_leaf逐项对应原kind析取；目标已有cm_leaf_expr是独立类型，因此使用不同谓词名称。
- 原e与leaf表示见证通过e=cm_leaf_source_expr leaf相连；coverage双向证明覆盖原leaf条件，unique保证表示唯一。
- cm_leaf_code_for复用四条已审计源方程及lvalue选择，未为非leaf构造子编造输出。pc/temp在这些方程中不影响代码，C参数仍保留。
- 常量type_code_wf可由原counts推出；最终手工证明使用原expr_wf的整数类型条件。字符串sid范围来自counts，sizeof asked合法性来自expr_wf；完整纯事实与空间资源保留。
- 既有wf_program与四项codegen obligations参数保持，四条helper契约规范化一致；未导入旧manual/auto。

保留既有 cm_lookup_policy、cm_codegen_obligations 和 wf_program 的参数化边界。跨体系源方程对应由语义审计记录，本例不是 HOL→Rocq 元层等价定理，也未完成整个递归 emitter、TVM 语义或编译保持性迁移。

## 验证

完成 13 条顶层手工义务、8 个 split；剩余手工义务零。manual 和新增公共库无 Admitted/Axiom/Parameter。另有 28 条自动 witness 以 Admitted 导出，依赖 QCP 自动层；未采用的 Abort split 草稿 0 个。

C* 重放耗时 45.085 秒，退出码0，verification_conditions/axioms/strategies 均为空；507个源 C/H 文件快照核对一致。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回及终检。

## 工作量

按非空非纯注释物理行计，同一分类内按行号去重。源 12 个 where 条目实际占 8 行（同一行可能有两个条目），条目数另列。Proof 包含声明、Proof/Qed 与 split 路由；生成 VC 不计手写 proof。行数受排版影响，不能代表历史工时或工具难度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 40 | 12 |
| 函数体 annotation | 8 | 51 |
| helper 接入 annotation | 0（include） | 12 |
| Annotation 含接入 | 8 | 63 |
| Specification + annotation | 48 | 63 |
| Specification + annotation 含接入 | 48 | 75 |
| 案例 proof | 64 | 143 |
| 新增公共定义 | 6 | 3 |
| 新增公共 proof | 0 | 16 |

C* 案例 proof 全为内嵌证明。QCP 案例 proof 中实际证明体 80 行、声明/包装 63 行。QCP 新增公共定义 1 项、引理 2 条；案例与公共 proof 合计 159 行。

对应源增量仅 cm_leaf_expr_def 的四种 kind 析取定义（6行）。四条代码方程、代码选择器、count/shape 公共支持和 helper 实现已经在先前案例使用，不重复计费。两条新增对应引理均编译通过，本轮 manual 未直接调用，仍计成本；逐项引用情况见 shared-helper-usage.json。公共 imports/scopes 4 行、公共自动化 0 行、C Extern 43 行、C Coq import 1 行另列。

实际设计、symexec、development/debug/exact 调用及失败修复见 process-notes.json 和封存 owner 输出。Controller 记录的 run 墙钟 430.58 分钟，包含编辑、工具、调度与等待；历史源工时及无法独立测量的活跃时间为 null。此为阅读源证明后的迁移成本，不能作为两体系从零证明的公平效率实验。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_dispatch_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
