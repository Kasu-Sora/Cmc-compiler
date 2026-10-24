from pathlib import Path
import json,csv,io,shutil,difflib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];D=E['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
files=[S/'SKILL.md',S/'references/cmc-emit-expr-leaf-case.md',W/'MIGRATION_PLAN.md',W/'migration_inventory.csv'];before={str(p):p.read_text()if p.exists()else''for p in files};b=R/'baseline/documentation-before';b.mkdir(exist_ok=True)
for p in files:
 if p.exists():shutil.copy2(p,b/p.name)
text=f'''# 已验证案例：emit-expr-leaf，C* → QCP

2026-10-17完成cmc_concrete_emit_expr_leaf.c全部九个运行时函数，含两个static helper。C*隔离重放通过，QCP run `{run}`为done、final-check passed。完整证据及计量见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_leaf/REPORT.md`。

## 范围与原契约

文件中的static cmc_const_immediate和cm_sizeof_value也是待验证运行时函数，不能仅接入假定契约。源cm_emit_const_expr头文件省略了实现前后置中的cm_type_code_wf ty；本例以被验证实现为基线保留它，并单独披露声明差异，不声称更弱头文件已经验证。

四类leaf为Const/String/Getc/Sizeof。独立cm_leaf_expr类型显式限制范围，嵌入既有cm_expr；非leaf投影为None。cm_leaf_rvalue和cm_leaf_code_for精确对应源四条方程及lvalue选择。原契约已有构造子等式，因此此特化不增加输入条件。不要把不支持的构造子默认输出空列表后仍命名为完整cm_expr_code_for；未来迁移递归emitter时需建立完整模型及leaf对应。

保留所有原纯事实与program/function/expression资源。字符串sid只有原[0,INT_MAX]界，不补sid<length；getc不增加typed条件；char立即数支持所有signed64输入，复用tower_u8模型；本例manual以既有类型编码引理和内嵌模运算证明低字节等式，不将导入word库算作直接复用其余数引理；lvalue=1消耗空片段并保留tail。

## 大小与偏移桥

结构体成员前缀使用cm_struct_member_size，普通槽位使用cm_slot_size。先在slots_wf下证明大小一致，再复用AST前缀与core大小桥连接表示和语义。成员offset保留sid有效性判断及越界0；前缀递归保留全部Z索引行为。string前缀可直接别名既有表示前缀，因为两个递归式仅差加法结合；global大小仍需wf桥。

布局/type-code/member-valid已有条件用于推导指针阈值、结构编号与成员边界。C的Z.rem不能无前提当作Z.mod；负常量低字节先按unsigned64取模，再证明二次取低字节等于tower_u8。六个外部helper契约与已验证layout/plan版本一致，不导入旧manual/auto或重复计其实现proof。

## 本例可复用的标注与证明经验

调用cm_emit_plan前，显式把leaf代码转换为singleton计划。此处直接写lvalue==0曾触发过早替换，使谓词匹配失败；等价的0<=lvalue<=0保留了匹配形状，生成的义务再证明lvalue==0。只在遇到同类匹配问题时采用此写法。字符串调用先匹配表示地址，再用typed_program推出语义地址等式；存在量由资源推断，避免where引用断言作用域之外的名字。

资源证明中Intros可能已提取纯事实，需查看实际上下文；payload合取需拆开后才能替换三个空指针。涉及string_scope时显式写Z.eqb。aggressive分支分派按实际生成次序，不能假定纯目标总在空间目标之前。

## 已验证规模

{N['manual_top_level']}条顶层手工义务、{N['manual_splits']}个split完成；{N['automatic_witnesses']}条自动witness以Admitted导出，依赖QCP自动层。manual及新增公共库无Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体annotation | {C['annotation']} | {Q['annotation']} |
| helper接入annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例proof | {C['case_proof']} | {Q['case_proof']} |
| 增量公共proof | {D['public_proof_lines']} | {Q['new_common_proof']} |

QCP新增{len(N['new_model_declarations'])}项定义/{Q['new_common_definitions']}行，{len(N['new_helpers'])}条引理/{Q['new_common_proof']}行；已有依赖零新增。按最终合并库统计，包括未直接被manual引用的辅助模型/引理，具体使用情况见shared-helper-usage.json。源8个私有PROOF helpers计案例proof，两个static普通函数也各自计契约/标注/证明。源模型只计四个leaf方程及所需选择器，不把整个递归emitter记为已迁移。行数不是历史工时或工具效率。
'''
(S/'references/cmc-emit-expr-leaf-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-expr-leaf-case.md'not in s
s=s.replace('emit-ast 的两个地址生成函数；','emit-ast 的两个地址生成函数及 emit-expr-leaf 的九个函数（含两个 static helper）；').replace('emit-ast 为 `cmc_emit_ast_migration.c`。','emit-ast 为 `cmc_emit_ast_migration.c`，emit-expr-leaf 为 `cmc_emit_expr_leaf_migration.c`。')
entry=f'`cmc_concrete_emit_expr_leaf.c` 于2026-10-17完成九个运行时函数验证。涉及leaf模型特化、static helper覆盖、声明/实现契约差异、结构体大小和成员偏移桥时，读取 [references/cmc-emit-expr-leaf-case.md](references/cmc-emit-expr-leaf-case.md)。本例完成{N["manual_top_level"]}条顶层手工义务、{N["manual_splits"]}个split，另有{N["automatic_witnesses"]}条可信自动结果；新增公共定义{len(N["new_model_declarations"])}项、引理{len(N["new_helpers"])}条。\n\n'
old='这些结果覆盖十六个具体实现文件的运行时部分、95 个运行时函数及必要依赖；';assert old in s;s=s.replace(old,entry+'这些结果覆盖十七个具体实现文件的运行时部分、104 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('emit-ast 的两个地址生成函数，共十六个具体实现文件的运行时部分、95 个运行时函数','emit-ast 的两个地址生成函数及 emit-expr-leaf 的九个函数，共十七个具体实现文件的运行时部分、104 个运行时函数').replace('83、16、16、14 条可信自动',f'83、16、16、14、{N["automatic_witnesses"]} 条可信自动').replace('[emit-ast 报告](experiments/cmc_emit_ast/REPORT.md)。','[emit-ast 报告](experiments/cmc_emit_ast/REPORT.md)、[emit-expr-leaf 报告](experiments/cmc_emit_expr_leaf/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`、';assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_expr_leaf.c` | 九个运行时函数（含两个static helper）；{N["manual_top_level"]}条手工义务、{N["manual_splits"]}个split、{N["automatic_witnesses"]}条可信自动结果；新增公共定义{len(N["new_model_declarations"])}项、引理{len(N["new_helpers"])}条；保留实现契约并披露const头文件差异 |\n| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf已完成）、')
s=s.replace('emit-plan 与 emit-ast 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_leaf.c`','emit-plan、emit-ast 与 emit-expr-leaf 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_var.c`');p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_expr_leaf.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_9_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_body_contract_header_difference'
  buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n'if line.endswith(b'\r\n')else'\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
(R/'logs/documentation-update.diff').write_text(''.join(''.join(difflib.unified_diff(before[str(p)].splitlines(True),p.read_text().splitlines(True),fromfile=str(p),tofile=str(p)))for p in files));print('Updated verified leaf skill reference, plan, inventory.')
