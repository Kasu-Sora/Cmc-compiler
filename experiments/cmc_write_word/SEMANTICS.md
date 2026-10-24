# cmc_write_word 语义核对基线

本文件记录迁移前固定的语义验收要求。现已通过完整验证，最终状态与证据见 REPORT.md 和 controller。

| 要点 | C* 源 | QCP 必须保留 |
|---|---|---|
| 输入范围 | long long 的全部有符号 64 位值 | 不额外要求 word_value 非负 |
| 数学字节 | tower_u8(z)=z mod 256；第 k 个字节为 k 次正除数 256 的数学除法后取模 | Z.div/Z.modulo，保留负值行为 |
| 字序 | tower_word_bytes 按 k=0..7 排列 | 小端序的八元素列表 |
| 运行时转换 | long long → unsigned long long → unsigned char | 保留原 C cast，并证明与数学模型的桥接 |
| 前置算术 | 0≤cursor，cursor+8≤capacity，capacity≤2147483647 | 不增加合法调用者负担 |
| 前置堆 | 已初始化 prefix 与未初始化后缀分离 | UCharArray.seg 与 undef_seg |
| 后置堆 | prefix ++ tower_word_bytes(word_value)，其后仍未初始化 | 内容、长度和资源分割均保持 |
| 模块化调用 | 八次 cmc_write_byte | 使用先前已验证的同义契约，保留调用及参数 |

数学检查点：-1 应得到八个 255；-2^63 应得到七个 0 后接 128；2^63-1 应得到七个 255 后接 127。这些例子只帮助审查含义，不能代替任意输入的证明。

原模型定义位于 baseline/tower_base.c:28–29、393–407、427–432。源桥接证明在 baseline/cmc_concrete_emit_word.c:6–142。原函数契约在 174–186，执行体从 188 开始。

源代码导出 cmc_unsigned_byte0_bridge，后续 char 文件可能复用。计量把该公开桥接及其通用构造器依赖闭包单列 98 行；私有 byte1..7 实例、范围引理及前缀归一化单列 57 行，内联 proof 162 行。同一个构造器只计算一次。

复用 helper 的现有目标文件、哈希和成功 controller 状态保存在 baseline/verified-byte/。此前两条自动结果的信任不会因为复用而消失，也不重复算作本次新增 proof 工作。
