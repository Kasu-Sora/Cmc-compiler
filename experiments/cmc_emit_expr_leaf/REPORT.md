# cmc_concrete_emit_expr_leaf.c：C* → QCP

全部九个运行时函数已迁移，含 static cmc_const_immediate、cm_sizeof_value；其余为四个 leaf emitters、cm_type_size_value、两个 member-context wrappers。C* 隔离重放通过；QCP run `cmc_emit_expr_leaf_migration-20261017144315` 为 done、final-check passed。函数运行时 token、共享 ABI、emitter 声明及复用库哈希保持不变。

## 原契约与模型范围

本次以源 .c 中被验证实现的契约为基线。源头文件 cm_emit_const_expr 的声明省略了 cm_type_code_wf ty，而函数体在前后置均保留此条件；QCP 保留函数体条件，不声称已经证明更弱的头文件版本。其余六个公开声明与对应实现契约一致，详见 source-header-audit.json。

常量 helper 接受全部 signed64 value；char 返回低八位，负数先按 unsigned64 转换再取余，数学对应 tower_u8；非 char 返回原值。没有增加 scalar 或 value 非负前提。

四个 emitter 保留原 lvalue[0,1]、表达式构造子及总函数查询条件，并保持完整 program/function/expression 资源。lvalue=0 追加原精确单指令片段，lvalue=1 追加空片段；计划 tail 保持。字符串 sid 仅有原 [0,INT_MAX] 界，未增加 sid<字符串数量限制；typed、安全大小等纯事实在前后置保留。sizeof 和 member 包装保留原 typed/type-code-wf/type_refs/member_valid/count/structs-safe 等各自条件，返回语义大小或成员偏移，不能用表示大小替代。

模型审计记录：

- 四类leaf采用独立cm_leaf_expr类型，嵌入现有cm_expr；非leaf投影为None，没有把非leaf代码伪定义为空。
- cm_leaf_rvalue/code_for对应源Const/String/Getc/Sizeof四条方程及lvalue选择；这些分支不依赖fid/pc/temp，函数契约仍保留原参数和总f查询。
- cm_const_immediate与源char低字节/非char恒等分支一致；使用既有tower_u8。
- cm_strings_prefix直接复用现有表示前缀；其递归与源字符串前缀在所有Z索引上按加法结合律相同，包含负索引。
- 语义string_address保持16+globals语义大小+strings前缀；typed条件用于连接表示与语义global大小。
- 成员前缀使用cm_struct_member_size，保留所有Z索引递归；member_offset保留合法sid判断，越界为0。
- 既有cm_type_size/struct_slots_size模型复用；slots_wf下普通槽大小与结构槽大小相等，再连接表示struct大小与语义type大小。
- 源与目标的leaf方程对应由源码审计确认；本例不把这些Rocq方程引理称为已完成HOL到Rocq元定理。

复用 layout、counts、word、emit-core、emit-plan、emit-ast 等所需公共依赖。六个既有 helper 契约规范化后与已验证版本相同：cm_emit_plan、cmc_string_address、cmc_type_size_at、cmc_member_array、cmc_pointee、cmc_member_offset_at。两个 static helper 自身纳入本例验证，旧 helper 实现证明不重复导入或计入新增。

## 验证与信任

完成 27 条顶层手工义务、37 个 split；九个函数均有验证覆盖，剩余手工义务零。新增公共库及 manual 无 Admitted/Axiom/Parameter。另有 49 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。未采用 Abort split 草稿 0 个，其父目标均已完成。

C* 重放耗时 42.692 秒，退出码0且 verification_conditions/axioms/strategies 均为空；507个源C/H文件快照核对一致。QCP 完成标注、依赖准备、独立VC审查、分组证明、合并全量检查、写回和终检。验证范围为该九个具体实现及所需leaf模型/桥接；完整递归expression emitter、TVM运行语义及编译保持性仍未全量迁移。

## 工作量

按非空非纯注释物理行统计。生成的VC文本不算手写proof；案例proof含证明声明、Proof/Qed和split路由，另列实际证明体。行数受排版影响；字符、词法token与标注条目见计量文件，不能以行数比推断工时或难度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 195 | 27 |
| 函数体 annotation | 25 | 74 |
| 既有 helper 接入 annotation | 0（include） | 17 |
| Annotation 含接入 | 25 | 91 |
| Specification + annotation 含接入 | 220 | 118 |
| 案例 proof | 512 | 506 |

C*案例proof含内嵌 386 行与8个私有PROOF helper的 126 行。QCP案例proof含证明体 314 行、声明/包装 192 行。

新增公共成本：QCP **10 项定义／34 行，14 条引理／125 行**；案例与公共proof合计 631 行。逐条使用情况、阶段增量和实际编译依赖见 effort.json/shared-helper-usage.json。现成库新增成本为零；仅被导入但未被manual引用的引理不记为直接复用。

对应源增量闭包：11项完整定义及4段leaf方程，共76行；12条公共定理及私有构造器共538行。按依赖图扣除已有大小/前缀/编码证明闭包，定义getter及导出脚手架排除。完整递归expression emitter只统计本例实际使用的四个构造子方程，不声称完整模型已迁移。源案例及此公共proof合计 1050行。

公共imports/scopes 5行、公共自动化/配置0行、C Extern 57行、C Coq import 1行另列。

| 函数 | C* spec | C* ann | QCP spec | QCP ann | QCP 案例 proof |
|---|---:|---:|---:|---:|---:|
| cmc_const_immediate | 9 | 0 | 3 | 0 | 33 |
| cm_emit_const_expr | 24 | 3 | 3 | 11 | 82 |
| cm_emit_string_expr | 34 | 6 | 3 | 19 | 92 |
| cm_emit_getc_expr | 22 | 2 | 3 | 2 | 53 |
| cm_sizeof_value | 18 | 2 | 3 | 10 | 59 |
| cm_type_size_value | 18 | 3 | 3 | 1 | 0 |
| cm_emit_sizeof_expr | 30 | 5 | 3 | 11 | 74 |
| cm_member_array_value_context | 19 | 3 | 3 | 10 | 37 |
| cm_member_offset_value_context | 21 | 1 | 3 | 10 | 76 |

标注设计检查6次（1次失败），符号执行5次（4次失败），均在同一annotation attempt修复。8组owner共运行development 41次（37次失败，含3次Show诊断）、debug 20次（2次失败）、exact 10次（2次失败）；各组最终exact及8次controller验收均通过。证明分组返工未产生新的annotation round或公共引理。所有设计、符号执行、development/debug/exact检查及返工均记录在 process-notes.json；annotation round与同轮失败次数分开统计。QCP run墙钟 32.26分钟，包括编辑、调度、工具及等待。历史源工时和不可独立测量的活跃时间记null。这是读过源证明后的迁移实验，不是两体系从零的公平比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_leaf_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[源声明差异](metrics/source-header-audit.json)
- [过程记录](metrics/process-notes.json)、[C*重放](metrics/cstar-verification.json)、[QCP终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
