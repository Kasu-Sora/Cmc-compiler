# helper-call-pure

完成两个已分配顶层 VC 及各自的一个 split goal。空列表等式由 reflexivity，globals cursor 非负性由已有返回等式和大小非负前提经 lia 完成；均使用明确 closer 的 LLM_pre_process，顶层仅使用 aggressive_pre_process 和对应 Goal_apply。

开发检查共 2 次，失败 1 次。第一次 LLM_pre_process 已关闭纯目标，随后冗余 dump_pre_spatial 导致 No such goal；删除冗余收尾后第二次开发检查通过。未执行额外 exact 预检，正式接纳由 main 调用 finalize-delivery 完成。

没有新增公共或本地 helper、定义和 import，group worker library 未修改。修改仅限已分配的四个 proof spans。
