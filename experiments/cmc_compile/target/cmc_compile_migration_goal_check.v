From SimpleC.EE.QCP_demos_human Require Import cmc_compile_migration_goal cmc_compile_migration_proof_auto cmc_compile_migration_proof_manual.

Module VC_Correctness : VC_Correct.
  Include cmc_compile_migration_proof_auto.
  Include cmc_compile_migration_proof_manual.
End VC_Correctness.
