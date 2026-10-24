# cmc_concrete_emit_expr_var.c：C* → QCP

整个文件的唯一运行时函数 cm_emit_var_expr 已完成迁移。C* 隔离重放通过；QCP run `cmc_emit_expr_var_migration-20261017152044` 为 done、final-check passed。运行时 token、共享 ABI、emitter 声明和复用库哈希保持不变。

## 契约与模型

源 .c/.h 契约一致。目标保留原 lvalue[0,1]、CMVarE 构造子、wf_program、总 f 查询、slot[0,INT_MAX]、binding_valid、type_code_wf、params/locals slots_wf、安全大小事实及完整 program/function/expression 资源。没有增加 fid 边界、ty 等于绑定实际类型、scalar 或额外 typed 输入条件。三条 helper 契约与已验证 layout/AST/plan 版本规范化后一致。

普通变量右值生成地址代码再加载；数组右值和任意合法左值只生成地址。精确代码片段从计划前缀消耗并追加至 done，任意 tail 保持。变量专用代码模型在原 e=CMVarE 前提下对应源 Var 方程，不伪造其他构造子的默认行为，不声称完整递归表达式模型已经迁移。

- cm_var_lcode直接复用既有binding_address_code；cm_var_rcode为地址加条件加载；cm_var_code_for保留lvalue零/非零选择。
- 变量专用定义不接受任意cm_expr，原契约e=CMVarE支持该特化；源方程不依赖pc/temp，C参数仍保留。
- 源cm_binding_array的global/local非零count与既有cm_binding_array_code编码一致；在原binding_valid与总f查询条件下复用既有lookup语义，参数分支非数组。
- cm_var_source_equation以布尔取反展开源Var分支；是本地Rocq等式，HOL到Rocq对应另由源审计确认，未宣称跨逻辑元定理。
- 既有wf_program及四个codegen obligation参数保持；三个helper按已验证契约接入。

复用现有 cm_lookup_policy 与 cm_codegen_obligations；wf_program 中已有的四个 codegen 条件保留显式参数，源实例化含义与之前 counts/AST 案例相同。本例不新增这些抽象条件，不证明完整模型实例化或编译保持性。

## 验证

完成 9 条顶层手工义务、9 个 split，剩余手工义务零。manual 与新增公共库无 Admitted/Axiom/Parameter；另有 22 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。未采用的 Abort split 草稿 0 个。

C* 重放耗时 42.101 秒，退出码0，verification_conditions/axioms/strategies 均为空；507个源 C/H 文件快照核对一致。QCP 已完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回和终检。

## 工作量

非空非纯注释物理行；生成的 VC 文本不计手写 proof。Proof 包含证明声明、Proof/Qed 及 split 路由；补充字符/token和条目计量见 metrics。不同排版影响行数，不能据此推断难度或工时。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 45 | 13 |
| 函数体 annotation | 21 | 27 |
| helper 接入 annotation | 0（include） | 33 |
| Annotation 含接入 | 21 | 60 |
| Specification + annotation 含接入 | 66 | 73 |
| 案例 proof | 160 | 167 |

C* 案例 proof 包含内嵌 140 行和私有 cm_var_code_shape 的 20 行。QCP 案例 proof 含实际证明体 113 行、声明/包装 54 行。

新增公共成本：QCP 3 项定义／9 行，1 条引理／11 行；案例与公共 proof 合计 178 行。已验证依赖零新增成本。每条新引理的实际使用、仅导入或间接引用情况见 shared-helper-usage.json；未使用但新增的引理仍计成本。

对应源增量：Var 方程片段 8 行；两个 array-code 零/非零定理及其私有构造器、两个计划选择/恢复状态操作共 50 行。既有 layout/AST/plan、上下文开合和 leaf 案例已经计入的选择器定义不重复计算。源案例和增量公共 proof 共 210 行。完整递归 emitter 不计为本例新增已迁移模型。

公共 imports/scopes 4 行、公共自动化 0 行、C Extern 44 行、C Coq import 1 行另列。

设计、symexec、development/debug/exact 的实际调用及失败修复见 process-notes.json 和封存的 owner 输出。QCP run 墙钟 14.87 分钟，包含编辑、调度、工具和等待；历史源工时和不可独立测量的活跃时间为 null。这是读过源证明后的迁移实验，不能作为两体系从零证明的公平效率比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_var_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_var_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_var_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
