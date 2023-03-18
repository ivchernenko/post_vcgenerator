theory Proof_4_2
  imports Proofs_4
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value \<equiv>
 (toEnv
       (setPstate (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) ERROR
         Ctrl'emergency))"

theorem proof_4_2: "VC2 inv4 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC2_def inv4_def R4_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply((rule allI)+)
   apply((drule conjE)+)
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
  subgoal premises prems  for s1 s2 s3
    apply(rule impI)
    apply(simp split: if_splits)
    using getPstate.simps(9) prems(2) prems(20) prems(4) substate_refl apply presburger
    using prems(5)
    by (metis One_nat_def) 
  
