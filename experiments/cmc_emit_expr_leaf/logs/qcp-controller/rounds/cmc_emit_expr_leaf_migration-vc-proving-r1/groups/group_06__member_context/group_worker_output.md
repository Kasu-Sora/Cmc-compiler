member_context 本次完成 3 个 assigned top-level VC 和 2 个 aggressive split goals，遵循指定 proof mode。未新增公共或本地 helper，group_worker_lib 保持不变。

检查计量：debug 4 次，均正常完成；development 5 次，前 4 次失败，第 5 次完成；exact 1 次完成。

失败及修复：
- 第 1 次 development：C `%` 实际是 Z.rem，Z.mod_small 无法匹配。改用 Z.rem_small，安全边界改用 Z.rem_bound_pos，并由已有 retval/base_ty 关系证明非负。
- 第 2 次 development：Intros_p 在 program context 的 existential 尚未提取时不能匹配。改为先提取 existential。
- 第 3 次 development：Intros s g t 的名字与策略内部绑定冲突。使用新的 ss、gg、tt 名字，并由该策略提取 non-null pure fact。
- 第 4 次 development：一次 cancel 仅消去一个资源。改用 repeat progress cancel 消去全部五个字段与三个列表资源。

交付后停止修改；最终接纳由主代理 finalize-delivery 的封存验证决定。
