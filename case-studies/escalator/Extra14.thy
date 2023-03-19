theory Extra14
  imports ExtraInv VCTheoryLemmas
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value \<equiv>
 (toEnv (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value))"

theorem extra14: "VC14 extraInv env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value "
  apply(simp only: VC14_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  subgoal
    apply((drule conjE[of _ _ ?thesis])+)
                        defer
                        apply assumption+
    subgoal premises prems
      apply(rule conjI)
      using prems(1-7) prems(8) apply simp
      apply(rule conjI)
      using prems(1-7) prems(9) apply simp
      apply(rule conjI)
      using prems(10) apply -[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value")
         apply(rule impI)
         apply(drule allE[of _ s0])
          prefer 2
          apply assumption
         apply(drule impE)
           prefer 3
           apply assumption
        using prems(1-7) substate_refl apply simp
         apply(drule exE)
          prefer 2
          apply assumption
         apply(drule exE)
          prefer 2
          apply assumption
        subgoal for s2 s3
          apply(rule exI[of _ s2])
          apply(rule exI[of _ s3])
          apply(rule cut_rl[of "s2 \<noteq> s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"])
           apply auto[1]
          apply(rule cut_rl[of "s2 \<noteq> s0 \<and> substate s0 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value)"])
          using substate_trans substate_antisym apply blast
          using prems(1-7) substate_refl apply simp
          by (metis substate_antisym toEnvNum_id)
        using prems(1-7) by simp
      apply(rule conjI)
      using prems(11) apply -[1]
       apply(rule allI)
      subgoal for s3
        apply(cases "s3 = s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value")
         apply(rule impI)
          apply(drule allE[of _ s0])
           prefer 2
        apply assumption
        using prems(1-7) substate_refl toEnvP_ltime apply simp
         apply (metis One_nat_def Suc_less_eq2 diff_Suc_1)
        using prems(1-7) by simp
      apply(rule conjI)
      using prems(1-7) prems(12) apply simp
      apply(rule conjI)
      using prems(1-7) prems(13) apply simp
      apply(rule conjI)
      using prems(1-7) prems(14) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(15) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(16) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(17) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(18) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(19) apply simp
      apply(rule conjI)
      using prems(1-7) prems(20) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(21) apply simp
      apply(rule conjI)
      using prems(1-7)  prems(22) substate_refl apply simp
      apply(rule conjI)
      using prems(1-7) prems(23) apply simp
      using prems(1-7) prems(24) by simp
    done
  done

end       
