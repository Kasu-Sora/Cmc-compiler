(* Variable-only specialization of cmc_codegen.c:721-728.  The source
   CMVarE equation is independent of pc/temp.  This model does not provide
   dummy clauses for any other cm_expr constructor.  The public C contract
   supplies e = CMVarE scope slot ty and preserves the existing total lookup
   policy and complete cm_wf_program/codegen-obligations model. *)
From Coq Require Import ZArith List Bool.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_ast_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Source cm_binding_array uses a nonzero global/local count, with parameters
   and other scopes false. cm_binding_array_code already implements precisely
   that total zero/nonzero encoding; use it directly, without a fresh oracle. *)
Definition cm_var_lcode policy p fid scope slot :=
  cm_binding_address_code policy p fid scope slot.
Definition cm_var_rcode policy p fid scope slot ty :=
  cm_binding_address_code policy p fid scope slot ++
  (if Z.eqb (cm_binding_array_code policy p fid scope slot) 0
   then cm_load_code ty else []).
Definition cm_var_code_for policy p fid scope slot ty (lvalue:Z) :=
  if Z.eqb lvalue 0 then cm_var_rcode policy p fid scope slot ty
  else cm_var_lcode policy p fid scope slot.

Lemma cm_var_source_equation policy p fid scope slot ty lvalue :
 cm_var_code_for policy p fid scope slot ty lvalue =
 if Z.eqb lvalue 0 then
   cm_binding_address_code policy p fid scope slot ++
   (if negb (Z.eqb (cm_binding_array_code policy p fid scope slot) 0)
    then [] else cm_load_code ty)
 else cm_binding_address_code policy p fid scope slot.
Proof.
 unfold cm_var_code_for, cm_var_rcode, cm_var_lcode.
 destruct (Z.eqb lvalue 0), (Z.eqb (cm_binding_array_code policy p fid scope slot) 0); reflexivity.
Qed.
