本组完成三个 return witness 及其 spatial split proof。无新增或复制 helper，group_worker_lib 未修改。

成本记录：debug 调用 9 次，其中失败 6 次；development 调用 0 次；exact 调用 1 次，其中失败 0 次。

调试修复原因：前三次补齐 debug 脚本中所需的模型、策略和列表 import；第四次将布尔分支的 simpl 改为明确的 cbn 规约；第六次修正表达式类型投影名称；第七次补充 cm_expr_type 规约并逐项 cancel。第五、八次用于查看剩余目标，第九次完整闭合首个 split proof。其后将同一资源重组方法适配至另两个分支。
