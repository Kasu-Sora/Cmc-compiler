# string-final-return

完成两个递归返回顶层证明及四个 aggressive split goals。复用既有 string list representation、size、bytes、unsigned-byte buffer 定义，没有新增或改写公共 helper，group library 保持种子内容。

开发检查共 6 次：5 次失败、最终 1 次通过；辅助 coq-debug 共 4 次，均正常完成。修正均限于本组证明：显式展开 cm_rep_string_size 后进行算术；提取空 full 数组中的纯事实；显式 cancel 链表和数组资源；将顶层 Goal_apply 顺序调整为先 spatial 后 pure；空节点反证前先引入表示中的两个存在量。没有 annotation/spec 缺口，也没有修改声明或契约。

cons 分支按空／非空 source bytes 区分，保留空缓冲区 emp 的原含义，并在非空分支使用已给定 nonnull 前提恢复 cm_uint8_buffer。输出 buffer 的端点经整数结合律归一化，内容经 append 结合律归一化；nil 分支保留原始 prefix 和未初始化 suffix。
