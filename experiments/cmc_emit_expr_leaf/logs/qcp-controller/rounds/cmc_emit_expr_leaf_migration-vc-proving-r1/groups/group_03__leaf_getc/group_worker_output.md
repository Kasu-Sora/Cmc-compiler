leaf_getc 已完成全部 3 个 top-level VC 和 5 个 split goal；顶层仅以 aggressive_pre_process 和对应 Goal_apply 分派。

实际命令次数：development 2 次，debug 2 次，exact 2 次。

失败与修复：
- 第 1 次 development 的 return_wit_1 空间目标仍有未闭合资源；直接 cbn 未展开 cm_leaf_code_for，改用现有 cm_leaf_getc_source_equation 重写后消去。
- 第 2 次 development 在纯等式 split_goal_2 报 No such goal；预处理已关闭目标，删除冗余步骤并显式使用 reflexivity closer。
- 第 1 次 exact 的 which_implies 顶层应用顺序不匹配；debug 显示分支顺序为空间目标、纯不等式、纯等式，按该顺序调整 Goal_apply。

没有新增公共或本地 helper，没有新增 import，group_worker_lib 未修改。复用 seed 中已有的 cm_leaf_getc_source_equation。
