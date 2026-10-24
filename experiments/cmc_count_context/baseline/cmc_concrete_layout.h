#pragma once

#include "cmc_concrete_defs.h"
#require "cmc_concrete_defs.c"

PROOF extern thm cm_binding_array_code_cases;
PROOF extern thm cm_binding_valid_slot_nonnegative;
PROOF extern thm cm_encoded_member_sid;
PROOF extern thm cm_member_array_code_cases;
PROOF extern thm cm_nonnegative_i32_cast;

int cm_args_length(struct cm_arg *arg)
    [[cst::param(`args:(cm_expr)list`)]]
    [[cst::require(`fact(cm_rep_args_safe args <=> true) **
      cm_arg_list_rep arg args`)]]
    [[cst::ensure(`fact(cm_rep_args_safe args <=> true) **
      cm_arg_list_rep arg args **
      fact((__return:int) == cm_rep_args_length args)`)]];

int cm_normalize_count(int ty)
    [[cst::require(`emp`)]]
    [[cst::ensure(
      `fact((__return:int) == cm_normalize_code_value ty)`)]];

int cmc_binding_array(struct cm_program *program, int fid,
                             struct cm_function *fn,
                             int scope, int slot)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       fact((__return:int) ==
         cm_binding_array_code p fid scope slot)`)]];

void cmc_binding_array_value(struct cm_program *program, int fid,
                                    struct cm_function *fn,
                                    int scope, int slot, int *array)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       undef_data_at array Tint`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       data_at array Tint
         (cm_binding_array_code p fid scope slot)`)]];

long long cmc_code_slot_size(int code, int count)
    [[cst::require(`emp`)]]
    [[cst::ensure(`emp **
      fact((__return:int) == cm_rep_code_slot_size code count)`)]];

long long cmc_frame_size(struct cm_function *fn)
    [[cst::param(`params:(cm_slot_d)list`,
                 `locals:(cm_slot_d)list`, `body:cm_stmt`,
                 `zp:int`, `zl:int`, `zb:int`)]]
    [[cst::require(
      `fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       fact(cm_rep_stmt_temps_safe body <=> true) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * cm_stemps body <=
         2147483647i) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       data_at (field_addr fn Tcm_function Fbody) Tptr zb **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       cm_stmt_rep zb body`)]]
    [[cst::ensure(
      `fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       fact(cm_rep_stmt_temps_safe body <=> true) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * cm_stemps body <=
         2147483647i) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       data_at (field_addr fn Tcm_function Fbody) Tptr zb **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       cm_stmt_rep zb body **
       fact((__return:int) == 8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * cm_stemps body)`)]];

long long cmc_global_address(struct cm_global *globals, int index)
    [[cst::param(`items:(cm_global_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_globals_safe items <=> true) **
      cm_global_list_rep globals items`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_globals_safe items <=> true) **
      cm_global_list_rep globals items **
      fact((__return:int) == cm_rep_global_address items index) **
      fact(16i <= (__return:int)) ** fact((__return:int) <= 1048576i)`)]];

long long cmc_globals_size(struct cm_global *node)
    [[cst::param(`globals:(cm_global_d)list`)]]
    [[cst::require(`fact(cm_rep_globals_safe globals <=> true) **
      cm_global_list_rep node globals`)]]
    [[cst::ensure(`fact(cm_rep_globals_safe globals <=> true) **
      cm_global_list_rep node globals **
      fact((__return:int) == cm_rep_globals_size globals) **
      fact(0i <= (__return:int)) ** fact((__return:int) <= 1048560i)`)]];

int cmc_is_pointer(int ty)
    [[cst::require(`emp`)]]
    [[cst::ensure(`emp **
      fact((__return:int) == cm_rep_is_pointer_code ty)`)]];

void cmc_is_pointer_value(int ty, int *pointer)
    [[cst::require(`undef_data_at pointer Tint`)]]
    [[cst::ensure(
      `data_at pointer Tint (cm_rep_is_pointer_code (ty:int))`)]];

long long cmc_local_offset(struct cm_function *fn, int slot)
    [[cst::param(`params:(cm_slot_d)list`,
                 `locals:(cm_slot_d)list`, `zp:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       fact((__return:int) == 8i + cm_rep_members_size params +
         cm_rep_member_prefix locals slot)`)]];

int cmc_member_array(struct cm_program *program, int base_ty, int mid)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `structs:(cm_struct_d)list`, `zs:int`)]]
    [[cst::require(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs`)]]
    [[cst::ensure(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       fact((__return:int) == cm_member_array_code p base mid)`)]];

void cmc_member_array_value(struct cm_program *program,
                                   int base_ty, int mid, int *array)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `structs:(cm_struct_d)list`, `zs:int`)]]
    [[cst::require(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       undef_data_at array Tint`)]]
    [[cst::ensure(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at array Tint
         (cm_member_array_code p base mid)`)]];

long long cmc_member_offset_at(struct cm_struct *item,
                                      int sid, int index)
    [[cst::param(`structs:(cm_struct_d)list`)]]
    [[cst::require(`fact(0i <= sid) ** fact(0i <= index) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs`)]]
    [[cst::ensure(`fact(0i <= sid) ** fact(0i <= index) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs **
      fact((__return:int) ==
        cm_rep_struct_member_prefix structs sid index) **
      fact(0i <= (__return:int)) ** fact((__return:int) <= 1048576i)`)]];

long long cmc_param_offset(struct cm_function *fn, int slot)
    [[cst::param(`params:(cm_slot_d)list`, `zp:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       cm_slot_list_rep zp params`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       cm_slot_list_rep zp params **
       fact((__return:int) == 8i + cm_rep_member_prefix params slot)`)]];

int cmc_pointee(int ty)
    [[cst::require(
      `fact(1024i <= ty) ** fact(ty <= 2147483647i)`)]]
    [[cst::ensure(`fact((__return:int) == ty - 1024i)`)]];

int cmc_slot_type_at(struct cm_slot *item, int index)
    [[cst::param(`slots:(cm_slot_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      cm_slot_list_rep item slots`)]]
    [[cst::ensure(`fact(0i <= index) **
      cm_slot_list_rep item slots **
      fact((__return:int) == cm_rep_slot_type slots index)`)]];

long long cmc_string_address(struct cm_global *globals,
                                    struct cm_string *strings, int index)
    [[cst::param(`global_items:(cm_global_d)list`,
                 `string_items:(cm_string_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_globals_safe global_items <=> true) **
      fact(cm_rep_strings_safe string_items <=> true) **
      fact(cm_rep_globals_size global_items +
        cm_rep_strings_size string_items <= 1048560i) **
      cm_global_list_rep globals global_items **
      cm_string_list_rep strings string_items`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_globals_safe global_items <=> true) **
      fact(cm_rep_strings_safe string_items <=> true) **
      fact(cm_rep_globals_size global_items +
        cm_rep_strings_size string_items <= 1048560i) **
      cm_global_list_rep globals global_items **
      cm_string_list_rep strings string_items **
      fact((__return:int) ==
        cm_rep_string_address global_items string_items index) **
      fact(16i <= (__return:int)) ** fact((__return:int) <= 1048576i)`)]];

long long cmc_strings_size(struct cm_string *node)
    [[cst::param(`strings:(cm_string_d)list`)]]
    [[cst::require(`fact(cm_rep_strings_safe strings <=> true) **
      cm_string_list_rep node strings`)]]
    [[cst::ensure(`fact(cm_rep_strings_safe strings <=> true) **
      cm_string_list_rep node strings **
      fact((__return:int) == cm_rep_strings_size strings) **
      fact(0i <= (__return:int)) ** fact((__return:int) <= 1048560i)`)]];

int cmc_stmt_temps(struct cm_stmt *stmt)
    [[cst::param(`s:cm_stmt`)]]
    [[cst::require(
      `fact(cm_rep_stmt_temps_safe s <=> true) **
       cm_stmt_rep stmt s`)]]
    [[cst::ensure(
      `fact(cm_rep_stmt_temps_safe s <=> true) **
       cm_stmt_rep stmt s **
       fact((__return:int) == cm_stemps s) **
       fact(0i <= cm_stemps s) **
       fact(cm_stemps s <= 2147483647i)`)]];

long long cmc_temp_offset(struct cm_function *fn, int temp)
    [[cst::param(`params:(cm_slot_d)list`,
                 `locals:(cm_slot_d)list`, `zp:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * temp <= 2147483647i) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * temp <= 2147483647i) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       fact((__return:int) == 8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * temp)`)]];

long long cmc_type_size_at(struct cm_struct *items, int ty)
    [[cst::param(`structs:(cm_struct_d)list`)]]
    [[cst::require(`fact(0i <= ty) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep items structs`)]]
    [[cst::ensure(`fact(0i <= ty) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep items structs **
      fact((__return:int) == cm_rep_type_size structs ty)`)]];
