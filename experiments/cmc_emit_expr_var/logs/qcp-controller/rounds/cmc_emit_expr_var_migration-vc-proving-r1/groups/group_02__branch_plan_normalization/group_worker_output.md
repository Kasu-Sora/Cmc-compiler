# branch_plan_normalization

完成 which_implies_wit_4、which_implies_wit_5、which_implies_wit_6 及各自 spatial split goal。仅修改本组分配的六个 proof spans；group_worker_lib 无修改，无新增 helper 或 import。

调用成本：development 2 次，其中失败 1 次；debug 2 次，其中失败 1 次；exact 0 次。

修复原因：初版仅用 `simpl Z.eqb`，保留了 `if true`，使 `app_assoc` 无法匹配；增加 `cbn beta iota zeta` 消去条件表达式。首次 debug 缺少当前 case library 的 import，补齐与 manual 对应的 import 后取得实际目标。

三个分支分别用 lvalue 的零值边界、array-code 零/非零条件及 lvalue 非零条件归一化；列表运算归一化后用 reflexivity 闭合。top-level 均使用 aggressive_pre_process 后仅 Goal_apply 对应 split lemma。
