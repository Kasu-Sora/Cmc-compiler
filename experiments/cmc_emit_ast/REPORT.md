# cmc_concrete_emit_ast.c：C* → QCP

全部两个运行时函数已迁移：cm_emit_binding_address 与 cm_emit_binding_address_plan。C* 原证明隔离重放通过；QCP run `cmc_emit_ast_migration-20261017141940` 为 done、final-check passed。运行时函数 token、cm_emitter 声明、共享 ABI 和复用库哈希保持不变。

## 契约与模型

保留原十项纯事实在前后置中的完整对应：程序 wf、总函数查询、structs/globals 对应关系、binding_valid、params/locals 的 slots_wf，以及 globals/params/locals 的表示安全性。两个函数同时保持完整 program-context 与 function-context 所有权。没有新增 fid 有效性、偏移界或 readiness 前提。

直接函数按 scope 生成精确地址片段：global 为 PUSH(global address)，local 为 FP-relative(local offset)，else 为 FP-relative(param offset)，追加至 done。计划包装函数消费 fragment++tail 中的 fragment，追加至 done 并保留 tail。binding_valid 自身保留原三种合法 scope 与 slot 条件。

新语义前缀按列表递归、在整数 index 等于零时停止；保留负数及超长 index 的原定义行为，不以 Z.to_nat 截断替代。语义地址分别为 16+globals-prefix、8+params-prefix、8+params-size+locals-prefix；函数查找沿用原 cm_lookup_policy。证明将已有表示大小、前缀计算与这些语义偏移连接。

复用 layout、counts、emit-core、emit-resolved、emit-plan 等已经验证的库。三个 layout helper 和两个 resolved helper 的契约与先前版本规范化后完全一致，未导入其 manual/auto 或重复计入实现证明。复用依赖确实进入 selected dependency snapshot，哈希与冻结版本一致。

沿用 counts 的 cm_wf_program policy cg p：typed/counts/size/stack 等条件完整保留；四项完整 codegen 条件仍由 cm_codegen_obligations 参数表示，具体 C* 实例化边界保持公开。当前证明只提取 typed/global-wf 所需结论，没有删除其它条件，也没有宣称已重建完整 emitter 或编译保持性。

## 验证

完成 9 条顶层手工义务、14 个 split，两个函数均有生成和检查覆盖，未完成手工义务为零。新增公共库和 manual 无 Admitted/Axiom/Parameter。另有 14 条自动 witness 以 Admitted 导出，依赖 QCP 自动层，不能称为全部义务均有独立 Rocq 内核证书。未采用的 Abort split 草稿 0 个，均有已完成顶层证明覆盖。

C* 重放退出码 0，verification_conditions/axioms/strategies 均为空，耗时 40.571 秒。507 个源 C/H 文件快照核对一致。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回及终检。

## 工作量

计数为非空非纯注释物理行；自动生成 VC 文本不计手写 proof。C* 内嵌 proof 和七个私有 cm_ast_* 支持函数计入案例 proof；QCP proof 包含证明声明、Proof/Qed 包装和 split 路由。契约排版差异较大，因此另外提供词法 token、字符量和标注条目，不能把行数比例当作工时或难度比。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | 73 | 55 |
| 函数体 annotation | 13 | 50 |
| helper 接入 annotation | 0（include） | 15 |
| Annotation 含接入 | 13 | 65 |
| Specification + annotation 含接入 | 86 | 120 |
| 案例 proof | 196 | 201 |

C* 案例 proof 为内嵌 113 行、七个私有支持函数 83 行；QCP 案例 proof 为证明体 132 行、声明/包装 69 行。

公共新增成本单列：QCP **7 项定义／30 行，2 条引理／34 行**。最终案例与新增公共 proof 合计 235 行。引理逐条使用情况与 annotation/proving 阶段增量见 effort.json、shared-helper-usage.json。

源对应增量依赖为 7 项模型定义／49 行，4 条公开引理及其构造器／169 行：两个前缀一致性桥和 globals-wf 的 head/tail 引理。已有 slots-wf head/tail、slot/global-size 桥、上下文开合、plan 开合、binding 非负性等不重复计为新增。源案例与这部分公共 proof 合计 365 行；这只是选定依赖闭包的规模，不是其历史开发时间。

已有依赖新增成本为零。公共导入/作用域 5 行，公共自动化/配置 0 行，C Extern 37 行、Coq import 1 行另列。

| 函数 | C* spec | C* ann | QCP spec | QCP ann | QCP 案例 proof |
|---|---:|---:|---:|---:|---:|
| cm_emit_binding_address | 37 | 8 | 28 | 35 | 157 |
| cm_emit_binding_address_plan | 36 | 5 | 27 | 15 | 44 |

标注 design/symexec/post-lib 各一次通过，无 annotation retry。三个证明组 controller 均首次验收通过；development 共 15 次（失败 12 次）、debug 共 6 次（失败 2 次）、owner exact 共 3 次全部通过。修正涉及空间资源的重复消去、scope 常量化简、片段长度的显式定义改写、Intros 语法与假设名，以及 aggressive 子目标的空间优先顺序。公共库在 proving 阶段未修改。

QCP run 墙钟 18.74 分钟，包含编辑、调度、工具检查与等待。检查次数、失败原因和修订见 process-notes.json，实际命令和结果保存在 logs。历史源工时、人工及模型活跃时间无独立可靠记录，记 null。本例是读取源证明后的迁移实验，不是两套体系从零证明的公平比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_ast_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_lib.v)
- [计量明细](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[helper 契约审计](metrics/helper-contract-audit.json)
- [过程记录](metrics/process-notes.json)、[C* 日志](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
