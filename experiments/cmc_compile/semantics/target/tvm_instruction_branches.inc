 | TVMPushOp => (if (Zlength (tvm_stack st) <? 65536)
        then TVMStepState
          (tvm_next_state st
            ((tower_wrap64 imm) :: tvm_stack st)
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMPopOp => (if (1 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMDupOp => (if (1 <=? Zlength (tvm_stack st)) &&
           (Zlength (tvm_stack st) <? 65536)
        then TVMStepState
          (tvm_next_state st
            (hd 0 (tvm_stack st) :: tvm_stack st)
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMSwapOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (hd 0 (tl (tvm_stack st)) :: hd 0 (tvm_stack st) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLoadOp => (if (1 <=? Zlength (tvm_stack st)) &&
           tower_word_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_getw (tvm_mem st) (hd 0 (tvm_stack st)) ::
              tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMStoreOp => (if (2 <=? Zlength (tvm_stack st)) &&
           tower_word_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tl (tvm_stack st)))
            (tvm_calls st)
            (tower_setw (tvm_mem st) (hd 0 (tvm_stack st))
              (hd 0 (tl (tvm_stack st))))
            (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLoadBOp => (if (1 <=? Zlength (tvm_stack st)) &&
           tower_addr_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_getb (tvm_mem st) (hd 0 (tvm_stack st)) ::
              tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMStoreBOp => (if (2 <=? Zlength (tvm_stack st)) &&
           tower_addr_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tl (tvm_stack st)))
            (tvm_calls st)
            (tower_setb (tvm_mem st) (hd 0 (tvm_stack st))
              (hd 0 (tl (tvm_stack st))))
            (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMAddOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_add (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMSubOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_sub (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMMulOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_mul (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMDivOp => (if (2 <=? Zlength (tvm_stack st)) &&
           negb ((hd 0 (tvm_stack st) =? 0))
        then TVMStepState
          (tvm_next_state st
            (tower_div (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMModOp => (if (2 <=? Zlength (tvm_stack st)) &&
           negb ((hd 0 (tvm_stack st) =? 0))
        then TVMStepState
          (tvm_next_state st
            (tower_mod (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMEqOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tl (tvm_stack st)) =? hd 0 (tvm_stack st))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMNeOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (negb ((hd 0 (tl (tvm_stack st)) =? hd 0 (tvm_stack st)))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLtOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tl (tvm_stack st)) <? hd 0 (tvm_stack st))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLeOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tl (tvm_stack st)) <=? hd 0 (tvm_stack st))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMGtOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tvm_stack st) <? hd 0 (tl (tvm_stack st)))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMGeOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tvm_stack st) <=? hd 0 (tl (tvm_stack st)))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMJmpOp => (if tvm_target_validb code imm
        then TVMStepState
          (tvm_jump_state st imm (tvm_stack st) (tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMJzOp => (if (1 <=? Zlength (tvm_stack st))
        then if (hd 0 (tvm_stack st) =? 0)
             then if tvm_target_validb code imm
                  then TVMStepState
                    (tvm_jump_state st imm (tl (tvm_stack st))
                      (tvm_calls st) (tvm_mem st) (tvm_input st)
                      (tvm_output st))
                  else TVMStepError st
             else TVMStepState
               (tvm_next_state st (tl (tvm_stack st))
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
        else TVMStepError st)
 | TVMJnzOp => (if (1 <=? Zlength (tvm_stack st))
        then if negb ((hd 0 (tvm_stack st) =? 0))
             then if tvm_target_validb code imm
                  then TVMStepState
                    (tvm_jump_state st imm (tl (tvm_stack st))
                      (tvm_calls st) (tvm_mem st) (tvm_input st)
                      (tvm_output st))
                  else TVMStepError st
             else TVMStepState
               (tvm_next_state st (tl (tvm_stack st))
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
        else TVMStepError st)
 | TVMCallOp => (if tvm_target_validb code imm &&
           (Zlength (tvm_calls st) <? 65536)
        then TVMStepState
          (tvm_jump_state st imm (tvm_stack st)
            ((tvm_pc st + 1) :: tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMRetOp => (if (1 <=? Zlength (tvm_calls st))
        then TVMStepState
          (tvm_jump_state st (hd 0 (tvm_calls st)) (tvm_stack st)
            (tl (tvm_calls st)) (tvm_mem st) (tvm_input st)
            (tvm_output st))
        else TVMStepError st)
 | TVMGetcOp => (if (Zlength (tvm_stack st) <? 65536)
        then if list_empty (tvm_input st)
             then TVMStepState
               (tvm_next_state st ((-1) :: tvm_stack st)
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
             else TVMStepState
               (tvm_next_state st
                 (tower_u8 (hd 0 (tvm_input st)) :: tvm_stack st)
                 (tvm_calls st) (tvm_mem st) (tl (tvm_input st))
                 (tvm_output st))
        else TVMStepError st)
 | TVMPutcOp => (if (1 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st)
            (tvm_output st ++ [tower_u8 (hd 0 (tvm_stack st))]))
        else TVMStepError st)
 | TVMPutiOp => (if (1 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st)
            (tvm_output st ++ tower_decimal (hd 0 (tvm_stack st))))
        else TVMStepError st)
 | TVMHaltOp => (if (1 <=? Zlength (tvm_stack st)) &&
           tower_byte_valueb (hd 0 (tvm_stack st))
        then TVMStepHalt
          (TVMState (tvm_pc st) (tl (tvm_stack st)) (tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
          (hd 0 (tvm_stack st))
        else TVMStepError st)
