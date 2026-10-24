# expression_representation 完成记录

5 个 assigned top-level 和 4 个 assigned split 全部 Qed；按既定 whole-goal/aggressive 路线完成。library 无修改，无新增 helper。

本组使用已有 cm_expr_rep、cm_expr_node、cm_expr_payload 和 cm_arg_list_rep。析构表达式，沿用原字段指针，提取 payload 的纯事实，展开 call-list 定义并正规化 sepcon 结合后 cancellation，保持所有资源。

本组实际命令次数：development 9 次（8 次失败，最终 1 次通过）；debug 3 次（2 次成功 Show 诊断，1 次失败）；exact 0 次。最终接纳由 main finalize-delivery 完成。

修复轨迹：避免 CMCallE 的 args binder 与节点 witness 名冲突；处理字段 sepcon 结合形状；修正 Ltac 分支括号；以既有 sepcon_assoc_change 替换不可用的 sepcon_assoc 名称；关闭节点前显式 Intros 提取 payload 纯合取。无契约、annotation、statement 或共享定义修改。
