theory Proof_5_36
  imports Proofs_5
begin

theorem proof_5_8: "VC36 inv5 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC36_def inv5_def R5_def extraInv_def)
  apply(rule impI)
  apply((drule conjE)+)
                      prefer 22
                      apply assumption
                      prefer 21
                      apply assumption
                     prefer 20
                     apply assumption
                    prefer 19
                    apply assumption
                   prefer 18
                   apply assumption
                  prefer 17
                  apply assumption
                 prefer 16
                 apply assumption
                prefer 15
                apply assumption
               prefer 14
               apply assumption
              prefer 13
              apply assumption
             prefer 12
             apply assumption
            prefer 11
            apply assumption
           prefer 10
           apply assumption
          prefer 9
          apply assumption
         prefer 8
         apply assumption
        prefer 7
        apply assumption
       prefer 6
       apply assumption
      prefer 5
      apply assumption
     prefer 4
     apply assumption
    prefer 3
    apply assumption
   prefer 2
   apply assumption
  by (metis One_nat_def Suc_1 Zero_not_Suc getPstate.simps(9) numeral_3_eq_3 substate_refl zero_neq_numeral)
 
  