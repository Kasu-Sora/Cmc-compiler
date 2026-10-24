# CMC 已迁移函数与功能对照表

整理日期：2026-10-21。依据本仓库当前 `target/*_migration.c` 的函数定义、QCP 契约和各模块 `REPORT.md` 核对，共 **31 个已完成迁移的实现单元、132 个运行时函数**，包含 static helper。函数声明和依赖导入不重复计数。

这里的“需要实现的功能”是已迁移函数必须满足的行为，不代表这些函数仍待实现。所有描述均以各函数 `Require` 成立为前提；表格突出功能与关键结果，不代替完整规约。函数名链接定位到实现及紧随其后的 `With / Require / Ensure`。

注意三个阅读区别：

- “计算”函数只返回尺寸、偏移、标志或代码长度；“生成”函数向输出缓冲区写入 TVM 指令，函数名中的 load/store 不意味着编译时执行目标程序的内存操作。
- PC／代码长度的单位是指令条数，数据长度／地址／帧偏移的单位是字节。`lvalue=1` 表示生成左值代码，`lvalue=0` 表示生成右值代码。
- `resolved` 描述逻辑上的 CALL 目标地址；在物理回填之前，数组中仍保存函数编号。`plan` 在此基础上记录剩余片段和容量预算，`done` 是已生成前缀，`tail` 是尚未消费的后缀。

先前 131 个函数沿用已有验证报告；本次新增顶层 cmc_compile 的完整验证。报告中 QCP 自动 witness 仍以 `Admitted` 导出，不能把“已完成流程验证”解读为所有义务都有独立 Rocq 内核证书。顶层 `cmc_compile` 已完成，见第 13 组及文末范围说明。

## 导航

| 分组 | 函数数 | 主要用途 |
|---|---:|---|
| [1. 基础字节写入与复制](#group-1) | 5 | 精确写入字节及整数编码 |
| [2. 类型、布局、地址与临时空间](#group-2) | 39 | 布局、查询、栈帧及临时槽需求 |
| [3. 代码／数据长度与上下文查询](#group-3) | 21 | 精确代码／数据大小与函数入口 PC |
| [4. 数据区生成](#group-4) | 3 | 全局变量、字符串及数据区组合 |
| [5. 基础指令生成](#group-5) | 9 | 写入 opcode／立即数和基础片段 |
| [6. resolved 逻辑视图包装](#group-6) | 8 | 将 raw 输出解释为已解析的逻辑代码 |
| [7. 带剩余容量计划的指令生成](#group-7) | 8 | 按计划消费代码片段和容量预算 |
| [8. 变量地址与简单表达式](#group-8) | 14 | 绑定地址、叶子表达式及变量 |
| [9. 调用参数与二元运算收尾](#group-9) | 6 | 参数求值与传递、指针运算缩放 |
| [10. 通用表达式生成](#group-10) | 7 | 所有表达式的递归代码生成 |
| [11. 语句、函数与完整代码生成](#group-11) | 9 | 控制流、栈帧、函数及程序代码组合 |
| [12. CALL 物理回填](#group-12) | 2 | 将 CALL 函数编号替换为实际 PC |
| [13. 顶层编译](#group-13) | 1 | 容量检查、代码／数据生成及原语义保持性连接 |

<a id="group-1"></a>

## 1. 基础字节写入与复制

### cmc_write_byte（1 个函数）

[迁移与验证报告](experiments/cmc_write_byte/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_write_byte](experiments/cmc_write_byte/target/cmc_write_byte_migration.c#L6) | 向目标缓冲区当前位置写入一个字节。 | 原前缀后精确追加 byte；剩余空间保持未初始化。 |

### cmc_write_zeroes（1 个函数）

[迁移与验证报告](experiments/cmc_write_zeroes/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_write_zeroes](experiments/cmc_write_zeroes/target/cmc_write_zeroes_migration.c#L7) | 从 cursor 开始连续写入 count 个零字节。 | 原前缀后追加 zeros(count)，包括 count=0。 |

### cmc_copy_bytes（1 个函数）

[迁移与验证报告](experiments/cmc_copy_bytes/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_copy_bytes](experiments/cmc_copy_bytes/target/cmc_copy_bytes_migration.c#L9) | 将源数组的 length 个字节复制到目标 cursor 处。 | 源数组不变；目标前缀追加完整源字节；保留零长度情形。 |

### cmc_write_word（1 个函数）

[迁移与验证报告](experiments/cmc_write_word/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_write_word](experiments/cmc_write_word/target/cmc_write_word_migration.c#L21) | 把一个 64 位整数编码为 8 个小端字节。 | 低位字节在前；负数也按其 64 位位模式编码。 |

### cmc_write_char（1 个函数）

[迁移与验证报告](experiments/cmc_write_char/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_write_char](experiments/cmc_write_char/target/cmc_write_char_migration.c#L19) | 取一个 64 位整数的低 8 位并写入一个字节。 | 追加 tower_u8(value)，结果在 0…255。 |

<a id="group-2"></a>

## 2. 类型、布局、地址与临时空间

### cmc_layout（39 个函数）

[迁移与验证报告](experiments/cmc_layout/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_max](experiments/cmc_layout/target/cmc_layout_migration.c#L117) | 计算两个整数的最大值。 | 返回 cm_imax(a,b)。 |
| [cmc_is_pointer](experiments/cmc_layout/target/cmc_layout_migration.c#L131) | 判断类型编码是否表示指针。 | ty≥1024 返回 1，否则返回 0。 |
| [cmc_is_pointer_value](experiments/cmc_layout/target/cmc_layout_migration.c#L145) | 通过输出指针给出类型是否为指针。 | 把同一判断结果写入 *pointer。 |
| [cmc_pointee](experiments/cmc_layout/target/cmc_layout_migration.c#L154) | 去掉类型编码的一层指针标记。 | 返回 ty−1024；适用条件见原契约。 |
| [cmc_leaf_size](experiments/cmc_layout/target/cmc_layout_migration.c#L162) | 计算叶类型的字节大小。 | 指针和 int 为 8，char 为 1，其他编码为 0。 |
| [cmc_code_slot_size](experiments/cmc_layout/target/cmc_layout_migration.c#L180) | 根据类型编码和 count 计算槽大小。 | count=0 按单值处理；否则为 count×叶类型大小。底层契约保留有符号 count 域。 |
| [cmc_members_size](experiments/cmc_layout/target/cmc_layout_migration.c#L195) | 累加成员链表中所有成员占用的字节数。 | 返回成员尺寸之和，保持成员链表。 |
| [cmc_struct_size_at](experiments/cmc_layout/target/cmc_layout_migration.c#L225) | 查询第 sid 个结构体的总大小。 | 累加其成员大小；遍历到空表返回 0。 |
| [cmc_nonzero](experiments/cmc_layout/target/cmc_layout_migration.c#L260) | 把整数转换为 0/1 的非零标志。 | n=0 返回 0，否则返回 1。 |
| [cmc_global_array_at](experiments/cmc_layout/target/cmc_layout_migration.c#L274) | 查询指定全局变量是否为数组。 | 依据该节点 count 是否非零；非负索引查到空表返回 0。 |
| [cmc_slot_array_at](experiments/cmc_layout/target/cmc_layout_migration.c#L308) | 查询指定参数／局部槽是否为数组。 | 依据 count 是否非零；非负索引查到空表返回 0。 |
| [cmc_slot_type_at](experiments/cmc_layout/target/cmc_layout_migration.c#L340) | 查询指定槽的类型编码。 | 返回节点 ty；非负索引查到空表返回 0。 |
| [cmc_member_array_at](experiments/cmc_layout/target/cmc_layout_migration.c#L372) | 查询指定成员是否为数组。 | 依据 count 是否非零；非负索引查到空表返回 0。 |
| [cmc_type_size_at](experiments/cmc_layout/target/cmc_layout_migration.c#L404) | 计算一般类型的字节大小。 | 指针/int 为 8、char 为 1；结构体按 ty−2 查询成员总大小。 |
| [cmc_slots_size](experiments/cmc_layout/target/cmc_layout_migration.c#L423) | 计算整条参数／局部槽链表的总大小。 | 返回精确字节数，保持链表和契约中的尺寸界。 |
| [cmc_slots_prefix](experiments/cmc_layout/target/cmc_layout_migration.c#L453) | 计算指定槽之前的槽所占的总字节数。 | index=0 为 0；到表尾停止；结果不超过总槽大小。 |
| [cmc_members_prefix](experiments/cmc_layout/target/cmc_layout_migration.c#L489) | 计算指定成员之前的成员所占的总字节数。 | 按成员链表累加前缀，保持链表及尺寸界。 |
| [cmc_member_offset_at](experiments/cmc_layout/target/cmc_layout_migration.c#L525) | 查询某结构体中指定成员的偏移。 | 返回该结构体的成员前缀大小。 |
| [cmc_struct_member_array_at](experiments/cmc_layout/target/cmc_layout_migration.c#L563) | 查询某结构体中指定成员的数组标志。 | 先定位结构体，再查询成员；保持结构体列表。 |
| [cmc_globals_size](experiments/cmc_layout/target/cmc_layout_migration.c#L601) | 计算全部全局变量占用的数据字节数。 | 精确累加全局槽大小，保持原尺寸界。 |
| [cmc_globals_prefix](experiments/cmc_layout/target/cmc_layout_migration.c#L633) | 计算指定全局变量之前的数据字节数。 | 返回全局变量尺寸前缀，不超过总大小。 |
| [cmc_strings_size](experiments/cmc_layout/target/cmc_layout_migration.c#L671) | 计算全部字符串的数据字节数。 | 每项贡献 length+1，包含零终止字节。 |
| [cmc_strings_prefix](experiments/cmc_layout/target/cmc_layout_migration.c#L703) | 计算指定字符串之前的数据字节数。 | 累加前面各项的 length+1。 |
| [cmc_global_address](experiments/cmc_layout/target/cmc_layout_migration.c#L741) | 计算指定全局变量的 TVM 内存地址。 | 16+该全局变量之前的字节数。 |
| [cmc_string_address](experiments/cmc_layout/target/cmc_layout_migration.c#L752) | 计算指定字符串的 TVM 内存地址。 | 16+全局区总大小+字符串前缀字节数。 |
| [cmc_binding_array_value](experiments/cmc_layout/target/cmc_layout_migration.c#L766) | 按作用域判断变量绑定是否为数组，并写入输出指针。 | 全局／局部查询相应列表；参数分支为 0；保留 binding_valid 等前提。 |
| [cmc_binding_array](experiments/cmc_layout/target/cmc_layout_migration.c#L785) | 返回变量绑定的数组标志。 | 包装 cmc_binding_array_value，保持所需程序／函数字段资源。 |
| [cmc_member_array](experiments/cmc_layout/target/cmc_layout_migration.c#L798) | 根据结构体指针类型和成员编号判断成员是否为数组。 | 解出结构体编号后查询；保持类型、成员合法性前提。 |
| [cmc_member_array_value](experiments/cmc_layout/target/cmc_layout_migration.c#L810) | 通过输出指针返回成员的数组标志。 | 包装 cmc_member_array，结果写入 *array。 |
| [cm_args_length](experiments/cmc_layout/target/cmc_layout_migration.c#L830) | 统计函数调用实参链表的长度。 | 返回精确实参数量，保持链表。 |
| [cmc_args_tpair](experiments/cmc_layout/target/cmc_layout_migration.c#L856) | 同时计算实参数量和各实参右值求值的最大临时槽需求。 | 分别写入 *count、*depth；后者是各参数需求的最大值。 |
| [cm_expr_temps](experiments/cmc_layout/target/cmc_layout_migration.c#L893) | 递归计算表达式左值／右值求值需要的临时槽数。 | 输出模型 tpair 的两个分量；调用分支包含实参暂存需求。 |
| [cm_expr_rtemps](experiments/cmc_layout/target/cmc_layout_migration.c#L1214) | 计算表达式作为右值时的临时槽需求。 | 返回 cm_expr_temps 的右值分量。 |
| [cmc_stmt_temps](experiments/cmc_layout/target/cmc_layout_migration.c#L1226) | 计算整条语句所需的最大临时槽数。 | 递归合并表达式、分支和循环体需求；保持语句树。 |
| [cmc_frame_size](experiments/cmc_layout/target/cmc_layout_migration.c#L1402) | 计算函数栈帧总字节数。 | 8+参数区大小+局部区大小+8×语句临时槽数。 |
| [cmc_param_offset](experiments/cmc_layout/target/cmc_layout_migration.c#L1414) | 计算参数槽相对帧指针的偏移。 | 8+该参数之前的参数字节数。 |
| [cmc_local_offset](experiments/cmc_layout/target/cmc_layout_migration.c#L1424) | 计算局部槽相对帧指针的偏移。 | 8+参数区大小+该局部槽之前的字节数。 |
| [cmc_temp_offset](experiments/cmc_layout/target/cmc_layout_migration.c#L1435) | 计算临时槽相对帧指针的偏移。 | 8+参数区大小+局部区大小+8×temp。 |
| [cm_normalize_count](experiments/cmc_layout/target/cmc_layout_migration.c#L1446) | 计算类型归一化需要生成的指令数。 | char 为 6，其他类型为 0。 |

<a id="group-3"></a>

## 3. 代码／数据长度与上下文查询

### cmc_counts（15 个函数）

[迁移与验证报告](experiments/cmc_counts/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_expr_type_code_value](experiments/cmc_counts/target/cmc_counts_migration.c#L212) | 读取表达式的类型编码。 | 写入 *code，保持表达式树。 |
| [cm_expr_lvalue_count](experiments/cmc_counts/target/cmc_counts_migration.c#L244) | 计算表达式作为左值时的代码长度。 | 调用联合计数函数，返回左值指令数。 |
| [cm_expr_rvalue_count](experiments/cmc_counts/target/cmc_counts_migration.c#L258) | 计算表达式作为右值时的代码长度。 | 调用联合计数函数，返回右值指令数。 |
| [cmc_args_code_count](experiments/cmc_counts/target/cmc_counts_migration.c#L272) | 计算调用的实参求值、暂存、重载及最终 CALL 的指令总数。 | 空实参为 1；非空为头参数右值长度+10+尾部计数。 |
| [cm_binding_address_count_value](experiments/cmc_counts/target/cmc_counts_migration.c#L327) | 计算取得变量绑定地址需要的指令数。 | 全局为 1，其他作用域为 4；写入 *count。 |
| [cm_expr_counts](experiments/cmc_counts/target/cmc_counts_migration.c#L339) | 递归计算表达式左值／右值代码长度。 | 覆盖叶子、赋值、二元／一元、索引、成员、调用及内建操作；精确对应代码计数模型。 |
| [cmc_stmt_code_count](experiments/cmc_counts/target/cmc_counts_migration.c#L942) | 递归计算语句生成的指令数。 | 包含求值、POP、初始化、分支／循环跳转及返回尾声等开销。 |
| [cmc_param_stores_count](experiments/cmc_counts/target/cmc_counts_migration.c#L1284) | 计算将参数保存到栈帧所需的指令数。 | 每个参数增加类型归一化长度+5。 |
| [cmc_function_prologue_count](experiments/cmc_counts/target/cmc_counts_migration.c#L1315) | 计算函数序言指令数。 | 14+所有参数存储指令数。 |
| [cmc_function_code_count](experiments/cmc_counts/target/cmc_counts_migration.c#L1339) | 计算一个完整函数的指令数。 | 序言长度+函数体长度+7 条默认返回指令。 |
| [cmc_function_prefix_count](experiments/cmc_counts/target/cmc_counts_migration.c#L1384) | 累计从当前函数开始的前 remaining 个函数的代码长度。 | remaining=0 或到表尾停止；递归推进函数编号。 |
| [cmc_function_pc](experiments/cmc_counts/target/cmc_counts_migration.c#L1465) | 计算指定函数的代码入口 PC。 | 11+该函数之前的函数代码总长度；前提按该函数契约。 |
| [cmc_functions_code_size_count](experiments/cmc_counts/target/cmc_counts_migration.c#L1510) | 累计函数链表的全部代码长度。 | 每项使用对应函数编号，保持程序上下文和函数链表。 |
| [cmc_model_code_length](experiments/cmc_counts/target/cmc_counts_migration.c#L1579) | 计算完整程序代码的指令数。 | 11 条程序序言指令+全部函数代码长度。 |
| [cmc_model_data_length](experiments/cmc_counts/target/cmc_counts_migration.c#L1618) | 计算完整数据输出区所需的字节数。 | 8 个保留字节+全局变量字节数+含终止零的字符串字节数。 |

### cmc_count_context（4 个函数）

[迁移与验证报告](experiments/cmc_count_context/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_expr_type_code_context](experiments/cmc_count_context/target/cmc_count_context_migration.c#L81) | 在表达式表示契约下读取类型编码。 | 保持 cm_expr_rep，结果写入 *code。 |
| [cm_expr_lvalue_count_context](experiments/cmc_count_context/target/cmc_count_context_migration.c#L104) | 在完整程序／函数上下文下计算左值代码长度。 | 返回精确计数，同时恢复上下文与表达式资源。 |
| [cm_expr_rvalue_count_context](experiments/cmc_count_context/target/cmc_count_context_migration.c#L137) | 在完整程序／函数上下文下计算右值代码长度。 | 返回精确计数，同时恢复上下文与表达式资源。 |
| [cm_stmt_code_count_context](experiments/cmc_count_context/target/cmc_count_context_migration.c#L170) | 在完整程序／函数上下文下计算语句代码长度。 | 返回精确计数，同时恢复上下文与语句资源。 |

### cmc_function_pc_total（2 个函数）

[迁移与验证报告](experiments/cmc_function_pc_total/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_function_prefix_total](experiments/cmc_function_pc_total/target/cmc_function_pc_total_migration.c#L51) | 对任意 target 累计到该函数编号之前的代码长度。 | 遇 index=target 或表尾停止；target 不在当前后缀编号范围时累加整个后缀。 |
| [cmc_function_pc_total](experiments/cmc_function_pc_total/target/cmc_function_pc_total_migration.c#L111) | 对任意 target 给出总定义的函数入口 PC 查询结果。 | 11+总前缀查询结果；保留负数／越界 target 域，在 code-ready 前提下保证结果范围。 |

<a id="group-4"></a>

## 4. 数据区生成

### cmc_emit_globals（1 个函数）

[迁移与验证报告](experiments/cmc_emit_globals/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_globals](experiments/cmc_emit_globals/target/cmc_emit_globals_migration.c#L70) | 依次生成全部全局变量的初始化字节。 | 有初值时按 char／word 编码，否则按槽大小补零；返回最终 cursor，保持全局描述符。 |

### cmc_emit_strings（1 个函数）

[迁移与验证报告](experiments/cmc_emit_strings/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_strings](experiments/cmc_emit_strings/target/cmc_emit_strings_migration.c#L46) | 依次复制字符串字节并追加零终止字节。 | 源链表和源数组不变；返回 cursor+字符串区总大小。 |

### cmc_emit_data（1 个函数）

[迁移与验证报告](experiments/cmc_emit_data/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_data](experiments/cmc_emit_data/target/cmc_emit_data_migration.c#L66) | 组合生成完整数据区。 | 依次为 8 个零字节、全局区、字符串区；返回精确末尾位置。 |

<a id="group-5"></a>

## 5. 基础指令生成

### cmc_emit_core（9 个函数）

[迁移与验证报告](experiments/cmc_emit_core/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_raw](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L62) | 把一条指令直接写入 ops／imms 两个数组。 | 在当前 pc 写入 op 和 immediate，pc 加 1，保留已写前缀与剩余容量资源。 |
| [cm_emit](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L89) | 按指令模型发射一条指令。 | 把 todo 首条移到 done；底层调用 cm_emit_raw。 |
| [cm_emit_normalize](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L104) | 生成 char 值归一化的指令片段。 | char 生成 ((x mod 256)+256) mod 256 的 6 条指令；其他类型不发射。 |
| [cm_emit_load](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L122) | 生成按类型选择的内存加载指令。 | char 用 LOADB，其他类型用 LOAD。 |
| [cm_emit_store](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L137) | 生成按类型选择的内存存储指令。 | char 用 STOREB，其他类型用 STORE。 |
| [cm_emit_fp_address](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L152) | 生成计算帧指针加 offset 的指令片段。 | PUSH 8、LOAD、PUSH offset、ADD，共 4 条。 |
| [cm_emit_temp_store](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L165) | 生成将栈顶值存入指定临时槽的指令片段。 | 计算临时槽偏移，发射帧相对地址与 STORE，共 5 条。 |
| [cm_emit_temp_load](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L194) | 生成从指定临时槽加载值的指令片段。 | 计算临时槽偏移，发射帧相对地址与 LOAD，共 5 条。 |
| [cmc_binary_opcode](experiments/cmc_emit_core/target/cmc_emit_core_migration.c#L223) | 把源语言二元操作编号映射为 TVM opcode。 | 显式处理比较和加减乘除；其余输入按原实现映射为 MOD。 |

<a id="group-6"></a>

## 6. resolved 逻辑视图包装

### cmc_emit_resolved（8 个函数）

[迁移与验证报告](experiments/cmc_emit_resolved/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_resolved](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L107) | 在 resolved 逻辑视图中追加一条普通指令。 | 保留非 CALL 限制；底层写入原 opcode／立即数。 |
| [cm_emit_resolved_call](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L126) | 在 resolved 逻辑视图中追加一次函数调用。 | 物理数组写函数编号；逻辑指令立即数为对应函数 PC。 |
| [cm_emit_resolved_normalize](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L142) | 在 resolved 逻辑视图中追加类型归一化片段。 | 精确追加 cm_char_normalize_code。 |
| [cm_emit_resolved_load](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L159) | 在 resolved 逻辑视图中追加按类型加载片段。 | 精确追加 cm_load_code。 |
| [cm_emit_resolved_store](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L176) | 在 resolved 逻辑视图中追加按类型存储片段。 | 精确追加 cm_store_code。 |
| [cm_emit_resolved_fp_address](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L193) | 在 resolved 逻辑视图中追加帧相对地址片段。 | 精确追加 cm_fp_relative_address_code(offset)。 |
| [cm_emit_resolved_temp_store](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L209) | 在 resolved 逻辑视图中追加临时槽存储片段。 | 精确追加 cm_temp_store_code，保持函数上下文与偏移条件。 |
| [cm_emit_resolved_temp_load](experiments/cmc_emit_resolved/target/cmc_emit_resolved_migration.c#L227) | 在 resolved 逻辑视图中追加临时槽加载片段。 | 精确追加 cm_temp_load_code，保持函数上下文与偏移条件。 |

<a id="group-7"></a>

## 7. 带剩余容量计划的指令生成

### cmc_emit_plan（8 个函数）

[迁移与验证报告](experiments/cmc_emit_plan/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L117) | 按剩余计划发射一条普通指令。 | 将计划首条追加到 done，保留 tail；具有剩余容量预算。 |
| [cm_emit_call_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L133) | 按剩余计划发射一条 CALL。 | 逻辑计划消费 CALL(函数 PC)；实际仍写函数编号，留待回填。 |
| [cm_emit_normalize_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L147) | 按计划发射类型归一化片段。 | 消费归一化片段，追加到 done，保留 tail。 |
| [cm_emit_load_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L161) | 按计划发射按类型加载片段。 | 消费 load 片段，追加到 done，保留 tail。 |
| [cm_emit_store_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L175) | 按计划发射按类型存储片段。 | 消费 store 片段，追加到 done，保留 tail。 |
| [cm_emit_fp_address_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L189) | 按计划发射帧相对地址片段。 | 消费地址片段，追加到 done，保留 tail。 |
| [cm_emit_temp_store_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L204) | 按计划发射临时槽存储片段。 | 消费 temp-store 片段，保持函数上下文和 tail。 |
| [cm_emit_temp_load_plan](experiments/cmc_emit_plan/target/cmc_emit_plan_migration.c#L220) | 按计划发射临时槽加载片段。 | 消费 temp-load 片段，保持函数上下文和 tail。 |

<a id="group-8"></a>

## 8. 变量地址与简单表达式

### cmc_emit_ast（2 个函数）

[迁移与验证报告](experiments/cmc_emit_ast/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_binding_address](experiments/cmc_emit_ast/target/cmc_emit_ast_migration.c#L81) | 生成变量绑定的地址计算代码。 | 全局用绝对地址 PUSH；局部／参数用各自偏移的帧相对地址片段。 |
| [cm_emit_binding_address_plan](experiments/cmc_emit_ast/target/cmc_emit_ast_migration.c#L157) | 按计划生成变量绑定地址代码。 | 与上一函数相同的精确片段，并消费对应计划前缀。 |

### cmc_emit_expr_leaf（9 个函数）

[迁移与验证报告](experiments/cmc_emit_expr_leaf/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_const_immediate](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L107) | 计算常量表达式应使用的立即数。 | char 取低 8 位；其他类型保留原 64 位值。 |
| [cm_emit_const_expr](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L122) | 生成常量表达式代码。 | 右值发射 PUSH(规范化常量)；左值模式不发射。 |
| [cm_emit_string_expr](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L150) | 生成字符串表达式代码。 | 右值发射字符串地址的 PUSH；左值模式不发射。 |
| [cm_emit_getc_expr](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L187) | 生成读取字符的表达式代码。 | 右值发射 GETC；左值模式不发射。 |
| [cm_sizeof_value](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L203) | 计算 sizeof 所查询类型的字节大小。 | 指针为 8，否则按一般类型大小查询结构体环境。 |
| [cm_type_size_value](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L229) | 提供一般类型大小查询接口。 | 包装 cm_sizeof_value，保持程序上下文。 |
| [cm_emit_sizeof_expr](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L239) | 生成 sizeof 表达式代码。 | 右值发射 PUSH(所查询类型的大小)；左值模式不发射。 |
| [cm_member_array_value_context](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L266) | 在完整程序上下文下查询成员的数组标志。 | 保持完整上下文，返回成员数组模型值。 |
| [cm_member_offset_value_context](experiments/cmc_emit_expr_leaf/target/cmc_emit_expr_leaf_migration.c#L288) | 在完整程序上下文下查询结构体成员偏移。 | 由基址指针类型解出结构体编号，返回成员前缀大小。 |

### cmc_emit_expr_var（1 个函数）

[迁移与验证报告](experiments/cmc_emit_expr_var/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_var_expr](experiments/cmc_emit_expr_var/target/cmc_emit_expr_var_migration.c#L104) | 生成变量左值或右值代码。 | 左值／数组右值保留地址；非数组右值在地址后追加按类型加载。 |

### cmc_emit_expr_dispatch（1 个函数）

[迁移与验证报告](experiments/cmc_emit_expr_dispatch/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_leaf_expr](experiments/cmc_emit_expr_dispatch/target/cmc_emit_expr_dispatch_migration.c#L91) | 分派叶子表达式代码生成。 | 按 kind 选择常量、字符串、sizeof 或 getc 的 emitter。 |

### cmc_emit_expr_simple（1 个函数）

[迁移与验证报告](experiments/cmc_emit_expr_simple/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_simple_expr](experiments/cmc_emit_expr_simple/target/cmc_emit_expr_simple_migration.c#L104) | 分派简单表达式代码生成。 | 变量走 cm_emit_var_expr，其余简单表达式走叶子分派。 |

<a id="group-9"></a>

## 9. 调用参数与二元运算收尾

### cmc_emit_expr_call（3 个函数）

[迁移与验证报告](experiments/cmc_emit_expr_call/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_args_reload_plan](experiments/cmc_emit_expr_call/target/cmc_emit_expr_call_migration.c#L140) | 按实参顺序从临时槽重载参数值。 | 每个参数生成一次 temp-load；槽号逐项加 1。 |
| [cm_emit_args_store_plan](experiments/cmc_emit_expr_call/target/cmc_emit_expr_call_migration.c#L178) | 依次生成实参求值代码并暂存到独立临时槽。 | 每项先求右值再存槽；推进 PC／slot，使用 scratch 区处理嵌套求值。 |
| [cm_emit_call_expr](experiments/cmc_emit_expr_call/target/cmc_emit_expr_call_migration.c#L238) | 生成完整函数调用表达式代码。 | 右值依次求值暂存参数、重载参数、发射 CALL；左值模式不发射。 |

### cmc_emit_binary_finish（3 个函数）

[迁移与验证报告](experiments/cmc_emit_binary_finish/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_pointer_scale_value](experiments/cmc_emit_binary_finish/target/cmc_emit_binary_finish_migration.c#L85) | 计算指针运算所需的元素缩放大小。 | 读取表达式类型并取其 pointee 的类型大小。 |
| [cm_emit_binary_generic_fragment](experiments/cmc_emit_binary_finish/target/cmc_emit_binary_finish_migration.c#L99) | 生成普通二元运算的收尾片段。 | 重载临时槽中的左值、SWAP，再发射映射得到的二元 opcode。 |
| [cm_emit_binary_finish_plan](experiments/cmc_emit_binary_finish/target/cmc_emit_binary_finish_migration.c#L114) | 生成二元运算的类型相关收尾代码。 | 处理整数运算、指针加减整数的缩放，以及指针差除以元素大小。 |

<a id="group-10"></a>

## 10. 通用表达式生成

### cmc_emit_expr（7 个函数）

[迁移与验证报告](experiments/cmc_emit_expr/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_intrinsic_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L346) | 生成 putc、puti 或 exit 内建表达式代码。 | 输出操作先求值并 DUP 保留结果；exit 把退出码归一化为 char 后 HALT。 |
| [cm_emit_unary_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L620) | 生成解引用、取地址、负号和逻辑非代码。 | 区分左／右值；解引用右值追加加载，取地址使用子表达式左值代码。 |
| [cm_emit_index_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L921) | 生成数组／指针下标访问代码。 | 暂存基址，计算索引×元素大小并相加；右值再加载，左值保留地址。 |
| [cm_emit_assignment_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L1066) | 生成赋值表达式代码。 | 暂存目标地址、计算并归一化右值、按类型存储，再加载赋值结果；左值模式不发射。 |
| [cm_emit_binary_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L1207) | 生成二元表达式代码。 | 逻辑或／与生成短路跳转及 0/1 结果；其他运算暂存左值后求右值并调用收尾函数。 |
| [cm_emit_member_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L1470) | 生成结构体成员访问代码。 | 求基址并加成员偏移；非数组右值追加加载，数组／左值保留地址。 |
| [cm_emit_expr](experiments/cmc_emit_expr/target/cmc_emit_expr_migration.c#L1593) | 按表达式种类统一分派递归代码生成。 | 覆盖全部 14 类表达式；精确追加 cm_expr_code_for，保持 PC 和临时槽预算条件。 |

<a id="group-11"></a>

## 11. 语句、函数与完整代码生成

### cmc_emit_return（1 个函数）

[迁移与验证报告](experiments/cmc_emit_return/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cm_emit_return_epilogue_plan](experiments/cmc_emit_return/target/cmc_emit_return_migration.c#L28) | 生成函数返回尾声。 | 发射 6 条指令，从当前帧恢复旧帧指针并 RET。 |

### cmc_emit_stmt（2 个函数）

[迁移与验证报告](experiments/cmc_emit_stmt/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_if_stmt](experiments/cmc_emit_stmt/target/cmc_emit_stmt_migration.c#L253) | 生成 if/else 语句代码。 | 根据 guard／分支精确长度计算跳转目标，组合条件、JZ、then、JMP、else。 |
| [cmc_emit_stmt](experiments/cmc_emit_stmt/target/cmc_emit_stmt_migration.c#L347) | 递归生成完整语句代码。 | 覆盖空语句、表达式、声明、初始化、顺序、块、if、while、break、continue、return；维护循环目标与 PC。 |

### cmc_emit_function（3 个函数）

[迁移与验证报告](experiments/cmc_emit_function/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_param_stores_from](experiments/cmc_emit_function/target/cmc_emit_function_migration.c#L199) | 生成把调用参数保存到栈帧的代码。 | 递归先处理尾部，按栈顺序反向存参数；每项归一化并写入正确帧偏移。 |
| [cmc_emit_prologue](experiments/cmc_emit_function/target/cmc_emit_function_migration.c#L232) | 生成函数栈帧序言和参数保存代码。 | 按 frame_size 保存旧帧指针并建立新帧；14 条固定指令后追加参数存储。 |
| [cmc_emit_function](experiments/cmc_emit_function/target/cmc_emit_function_migration.c#L269) | 生成一个完整函数。 | 序言+函数体+PUSH 0 与返回尾声；按精确函数入口 PC 和临时槽上界组合。 |

### cmc_emit_functions（1 个函数）

[迁移与验证报告](experiments/cmc_emit_functions/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_functions](experiments/cmc_emit_functions/target/cmc_emit_functions_migration.c#L80) | 依次生成函数链表中的所有函数。 | 每次按当前函数长度推进下一函数 PC，函数编号加 1。 |

### cmc_emit_prelude（1 个函数）

[迁移与验证报告](experiments/cmc_emit_prelude/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_prelude](experiments/cmc_emit_prelude/target/cmc_emit_prelude_migration.c#L42) | 生成程序启动与退出序言。 | 11 条固定结构指令：初始化帧指针为 1048576、调用 main、归一化退出码并 HALT。 |

### cmc_emit_code（1 个函数）

[迁移与验证报告](experiments/cmc_emit_code/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_emit_code](experiments/cmc_emit_code/target/cmc_emit_code_migration.c#L54) | 组合生成完整程序代码。 | 从 PC=0 发射程序序言，再从 PC=11 发射所有函数；精确对应完整代码模型。 |

<a id="group-12"></a>

## 12. CALL 物理回填

### cmc_patch_calls（2 个函数）

[迁移与验证报告](experiments/cmc_patch_calls/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_patch_code_arrays](experiments/cmc_patch_calls/target/cmc_patch_calls_migration.c#L43) | 扫描指令数组并物理回填 CALL 的立即数。 | CALL 的函数编号替换为总 PC 查询值；其他指令、顺序及长度不变。 |
| [cmc_patch_resolved_calls](experiments/cmc_patch_calls/target/cmc_patch_calls_migration.c#L79) | 把 emitter 的 resolved 逻辑视图落实为物理指令数组。 | 对已写入的 pc 条指令调用回填；结果 ops／imms 等于 resolved 模型的投影。 |

<a id="group-13"></a>

## 13. 顶层编译

[迁移与验证报告](experiments/cmc_compile/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_compile](experiments/cmc_compile/target/cmc_compile_migration.c#L124) | 计算所需容量，生成代码、回填 CALL 并生成数据。 | 容量不足返回 1、保留所需长度及 entry=-1；成功返回 0、entry=0，精确输出模型字节／指令，并保持源终止的输入、输出和退出状态。 |

## 与上述 132 个运行时函数分开统计的内容

| 项目 | 当前范围／状态 |
|---|---|
| readiness 纯证明支持 | data_ready、program_ready、code_ready、temp_ready、function_ready、compile_ready 六个源支持单元已迁移，不增加运行时函数数。 |
| 顶层数学公共支持 | 22 批 198 模块，494 项定义、1061 条定理；另有案例库 11 项定义、5 条引理。 |
| 编译语义保持性 | 原 18 项不变量在成功执行可达状态上成立；cmc_preservation 与原成功桥已验证，实际顶层成功返回证明调用此桥。 |
| 范围边界 | 不宣称全部源 helper/export 逐名迁移、发散保持、双向等价或独立 TVM C 解释器实现验证。 |

依据：[迁移总览](MIGRATION_PLAN.md)、[顶层最终报告](experiments/cmc_compile/REPORT.md)。
