# cmc_compile：第五批公共证明支持

补齐 short-ready。累计原 18 项中的 12 项，亦即本轮剩余 11 项中的 5 项，具备具体 initial/step/任意步数保持性证明。仍缺 layout-ready、runtime、type、tagged-valid、code-layout、完整 target-sim；原 cmc_preservation、cmc_compile 成功桥和顶层 QCP 未完成，skill 未改。

## 证明内容

保持原 cm_frame_short_ready、cm_frames_short_ready、cm_task_short_ready 含义：只有 CMBinRK 记录短路条件，op=0 要求左值为 false，op=1 要求为 true。其余 frame 不额外约束。

新增本地 saved-region generation inclusion：保存的区域代际包含于当前区域代际。通过实际 R/L/S/V/C 步进、调用、局部激活、作用域和调用恢复证明它的初始及任意步保持性。恢复区域时只修改存活性，不改变已有代际的首次基址；调用和局部分配只增加新代际。因此原先有代际界的左值数值及真值不变。逐一覆盖短路 frame 创建、值/控制返回及 IO/存储分支，再结合此前已证明的 generation-safe。没有将尚未完成的 runtime 或目标模拟定理作为假设，也没有添加 C Require。

3 个原定义逐项映射，5 个本地定义用于强化证明状态及组合；它们的初始/逐步条件全部闭合。已验证的 30 个公共库原样复用，复用新增源码成本为 0。

## 新增公共依赖成本

本批 8 定义、40 引理；定义 12 行，proof 191 行（引理 158，8 个 Ltac 共 33 行）。非空非注释物理行，proof 含陈述及 Proof/Qed，工具与生成审计不计；所有辅助引理均计入。新增运行时 C 和 annotation 为 0。

五批累计 391 定义、363 引理，定义 1544 行、proof 1960 行。对应 C* 同名参照切片定义 79 行、直接 proof 构造器 71 行、常量装配 2 行；该切片不含传递闭包，不计算与全部 QCP proof 的比值。历史人工耗时未知保持 null。

## 验证

40/40 Print Assumptions 闭合，无新公理；独立 coqchk 退出 0，耗时 301.31 秒；两个正式目录公共库编译通过。518 原源文件、185 旧目标文件、30 前批库及 skill/计划/清单哈希未变。失败尝试、命令耗时和哈希保存在 metrics 和 logs。顶层 VC 尚未生成，原 controller/annotation owner 保留。C* 顶层此前完整重放通过，本批未重复。

重放依赖顺序见 publish.py：check.py development MODULE；source_reference_cost.py；check.py development TransportAudit；完成后 check.py kernel TransportAudit。kernel-input-manifest 固定源及 .vo；publish.py 和 record_checkpoint.py 都有核验门禁。
