theory Proof_1_12
  imports Proofs_1
begin

theorem proof_1_12: "VC12 inv1 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC12_def inv1_def R1_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply((rule allI)+)
   apply(rule impI)
   apply ((drule conjE)+)
                      prefer 36
                      apply assumption
                      prefer 35
                      apply assumption
                       prefer 34
                        apply assumption
                        prefer 33
                        apply assumption
                        prefer 32
                        apply assumption
                        prefer 31
                        apply assumption
                        prefer 30
                        apply assumption
                        prefer 29
                        apply assumption
                        prefer 28
                        apply assumption
                        prefer 27
                        apply assumption
                        prefer 26
                        apply assumption
                        prefer 25
                        apply assumption
                        prefer 24
                        apply assumption
                        prefer 23
                        apply assumption
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
  subgoal premises prems for s1 s2
    thm prems(27)
    using prems(2-10) prems(12-14) prems(17) prems(19) prems(21-22) 
    apply(simp split: if_splits)
    using substate_toEnvNum_id substate_refl prems
     apply (metis One_nat_def)
 using prems(15) by auto
   
    
  
    
    