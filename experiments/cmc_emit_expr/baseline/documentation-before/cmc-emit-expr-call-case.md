# 已验证案例：emit-expr-call，C* → QCP

2026-10-18 完成 cmc_concrete_emit_expr_call.c 的三个运行时函数：cm_emit_args_reload_plan、cm_emit_args_store_plan、cm_emit_call_expr。C* 隔离重放通过；QCP run `cmc_emit_expr_call_migration-20261018170809` 为 done、final-check passed。证据见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_call/REPORT.md`。

## 契约、模型与复用

参数可为任意原契约允许的表达式，不能为了沿用 simple 模型而限制参数种类。保留 lvalue 两分支、全部 wf/typed/counts 与表示安全事实、槽布局、全局区大小、temp/scratch/temp_limit 和 PC 起止界，以及完整上下文所有权和任意计划 tail。既有 lookup policy 和 codegen obligations 参数化边界不变。

复用 cm_args_length、cm_expr_rvalue_count_context、temp load/store plan、call plan 的已验证 BODY 契约。本例仍按原头文件契约调用通用 cm_emit_expr，其函数体尚未迁移。这是原有的模块依赖边界，不代表整个递归 emitter 已验证。新增的 14 构造子一般表达式代码模型是数学定义，不代替实现证明，也不构成 HOL→Rocq 等价或 TVM 保持性定理。

复用 layout/counts 的表达式资源、临时深度和调用事实引理，以及已有 primitive、leaf/var 和 opcode 模型。实际 manual 引用 cm_expr_rep_node、cm_expr_tpair_call、cm_expr_wf_call、cm_expr_counts_repr_call；旧库没有变更，旧 helper 的 manual/auto 不导入也不重复计费。

## 本例可复用经验

- 嵌套 Call 参数列表的代码模型用内部 list fixpoint；单独的 args-store 定义与它的等式需要列表归纳。先泛化 pc、slot、scratch，再归纳；不能直接要求两个不同 fixpoint reflexivity。
- 一般表达式的 lcode/rcode 长度同时证明。递归经过表达式和嵌套参数列表，保持 pc/temp 可变，再用内部列表归纳处理 Call。得到无额外 wf 前提的长度／count 等式后，可复用它证明参数执行后的 PC 安全。
- 参数列表非空分支先展开 head/tail，再开合 cm_arg_list_rep；空指针推出 nil 的纯目标依赖空间资源，若生成的 split 丢失这项资源，按 VC 路线证明原顶层义务。本例两个未采用的 split 保留 Abort，父义务均已 Qed；不可把 Abort 当作未完成顶层证明。
- 保持 opaque emitter plan 的关联方向和 singleton tail 形状，使用 append 归一化后 cancel。which-implies 的局部变量替换和存在变量范围应与后续调用所需资源一致；不要用增强前提解决符号执行困难。
- 调用编号的 signed-int 范围从原 counts 事实导出；temp_limit 的上界可从槽大小非负与 temp_offset 推出，不增加入口条件。

## 验证与计量

21 条顶层手工义务、43 个 split 完成；60 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。manual 和新增公共库无 Admitted/Axiom/Parameter。七组、合并全量检查和终检均通过。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | 180 | 51 |
| 函数体 annotation | 35 | 40 |
| helper 接入 annotation | 0（include） | 36 |
| 案例 proof | 988 | 613 |
| 公共 proof 增量 | 404 | 134 |

C* 案例 proof 含内嵌 515 行和同文件私有辅助 473 行。QCP 新增公共定义 12 项／74 行，引理 10 条／134 行；其中标注阶段为 74 行定义及 36 行引理，证明阶段增加五条引理／98 行。源新增模型闭包 175 行，另有三项私有观察定义／7 行；此前 leaf/var、primitive 和 AST/count 模型不再计入。未被 manual 直接调用的新增引理仍计成本，逐项引用与区间见 effort.json。

非空行受格式、声明包装和证明风格影响，不等于工时。生成 VC 排除在手写 proof 之外；外部声明、导入和实际命令失败修复另列。未知历史工时与不可测活跃时间为 null。
