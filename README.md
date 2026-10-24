# CMC compiler verification migration

CMC compiler verification migrated from C* to QCP/Rocq, including annotated C code, formal proofs, and verification reports.

本仓库保存 CMC / TVM 的 C* → QCP / Rocq 验证迁移成果。迁移对象包括 C 实现的规约与标注、逻辑模型、公共引理，以及顶层编译保持性证明。

## 阅读入口

- [已迁移函数与功能对照表](MIGRATED_FUNCTIONS.md)：31 个实现单元、132 个运行时函数及其目标规约。
- [迁移范围与验收状态](MIGRATION_PLAN.md)：迁移范围、依赖与覆盖说明。
- [顶层 cmc_compile 验证报告](experiments/cmc_compile/REPORT.md)：最终契约、验证结果、工作量与信任边界。
- [源文件迁移清单](migration_inventory.csv)：源文件分类、迁移状态和哈希。
- [迁移工作量统计](experiments/migration-complexity-summary.json)。

## 目录

- `experiments/cmc_*/target/`：带 QCP 标注的 C 实现、Rocq 目标、手工证明与支持库。
- `experiments/cmc_compile/`：顶层实现验证，以及语义、运行时、模拟不变量和保持性证明各阶段的源码。
- `experiments/cmc_*/baseline/`：用于对照和审计的源文件及依赖记录。
- `experiments/cmc_*/metrics/`、`logs/`：验证、假设审计、成本统计与过程记录。
- `examples/ast_to_tvm/`：AST 到 TVM 的示例及输出记录。

## 验证状态与复现

现有报告记录了截至 2026-10-21 的验证结果；上传本仓库本身不代表重新运行了全部验证。手工证明、数学支持与 QCP 自动结果的信任边界分别见各案例报告。部分自动 VC 以可信 `Admitted` 常量导出，不能视为独立 Rocq 内核证明。

复现需要原 C* 与 QCP/Rocq 工具链。仓库保留实验脚本和配置，其中部分路径指向原开发机器上的 CMC、QCP 与 Rocq 安装；在其他机器上运行前需调整这些路径。历史日志和审计记录中的绝对路径保持原样。

Git 不收录编译产物、工具链副本、重复构建工作区和验证备份快照；迁移源码、目标证明、报告与轻量验证记录保留在仓库中。
