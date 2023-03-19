theory Extra6
  imports ExtraInv VCTheoryLemmas
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value \<equiv>
 (toEnv
   (setVarBool (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value)
     direction'
     (getVarBool (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value)
       directionSwitch')))"

theorem extra6: "VC6 extraInv env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC6_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  subgoal
    apply((drule conjE[of _ _ ?thesis])+)
                        defer
                        apply assumption+
    subgoal premises prems
      apply(rule conjI)
      using  prems(7) apply -[1]
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
        using prems(1-6) substate_refl apply simp
         apply(drule disjE)
           prefer 3
           apply assumption
          apply(rule disjI1)
          apply(drule exE)
           prefer 2
           apply assumption
          apply(drule exE)
           prefer 2
           apply assumption
        subgoal for s2 s3
          apply(rule exI[of _ s2])
          apply(rule exI[of _ s3])
          apply(((rule conjI),(auto)[1])+)
          using prems(1-6) apply -
          apply((rule allI)+)
          subgoal for s4 s5
            apply(cases "s5 = s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value")
             apply simp
            using substate_toEnvNum_id apply blast
            apply simp
            by blast
          done
         apply(rule disjI2)
        using prems(1-6) apply -[1]
         apply((rule allI)+)
        subgoal for s4 s5
          apply(cases "s5 = s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value")
           apply simp
          using substate_toEnvNum_id apply blast
          apply simp
          by blast
        by auto
      apply(rule conjI)
      using prems(1-6) prems(8) apply simp
      apply(rule conjI)
      using prems(1-6) prems(9) apply simp
      apply(rule conjI)
      using prems(1-6) prems(10) apply simp
      apply(rule conjI)
      using prems(1-6) prems(11) apply simp
      apply(rule conjI)
      using prems(1-6) prems(12) apply simp
      apply(rule conjI)
      using prems(1-6) prems(13) apply simp
      apply(rule conjI)
      using prems(1-6) prems(14) apply simp
      apply(rule conjI)
      using prems(1-6) prems(15) apply simp
      apply(rule conjI)
      using prems(1-6) prems(16) apply simp
      apply(rule conjI)
      using prems(1-6) prems(17) apply simp
      apply(rule conjI)
      using prems(1-6) prems(18) apply simp
      apply(rule conjI)
      using prems(1-6) prems(19) apply simp
      apply(rule conjI)
      using prems(1-6) prems(20) substate_refl  apply simp
      apply(rule conjI)
      using prems(1-6) prems(21) apply simp
      apply(rule conjI)
      using prems(1-6) prems(22) apply simp
      using prems(1-6) prems(23) by simp
    done
  done

end