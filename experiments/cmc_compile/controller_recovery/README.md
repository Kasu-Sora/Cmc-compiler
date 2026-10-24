# 顶层验证流程恢复修复

旧 annotation attempt 在生成 VC 之前报告语义依赖缺口，因此没有 manual 文件。controller 仍返回 `retry-round`，但其反馈提取无条件读取 manual 哈希，随后又无条件要求失败 VC，导致同一 annotation owner 无法恢复。

修复仅允许 controller 已派发的 `annotation-blocked` 重试，且来源为 annotation、终态 blocked、缺口为 dependency-gap、VC 列表为空时，以已封存的叙述报告作为证据。含 VC 的反馈仍必须检查 manual 哈希。没有制造 manual、修改 run 状态或跳过证明检查；旧报告保留。

原文件在 `controller_attempts.before.py`，精确补丁在 `controller_attempts.patch`。3 个针对性回归与 31 个现有 annotation-design 回归通过。后者首次受到 macOS `/var` 软链接临时目录限制影响，指定真实 TMPDIR 后通过。

公共数学证明、案例 proof 和工具恢复代码分别计量；这段修复不计入编译保持性证明行数。
