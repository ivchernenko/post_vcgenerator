theory Extra4
  imports ExtraInv VCTheoryLemmas
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value  directionSwitch_value alarmButton_value stuck_value \<equiv>
 (toEnv
   (setPstate
     (setVarBool
       (setVarBool
         (setVarBool (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value)
           up' UP')
         moving' UP')
       direction' UP')
     ERROR Ctrl'goUp))"

theorem extra4: "VC4 extraInv env s0 userAtTop_value userAtBottom_value  directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC4_def extraInv_def)
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
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value")
         apply(rule impI)
         apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"])
        using prems(1-7) substate_refl toEnvNum_id apply -[1]
         apply((rule conjI);simp)
        using prems(10) by simp
      apply(rule conjI)
      using prems(1-7) prems(11) apply simp
      apply(rule conjI)
      using prems(1-7) prems(12) apply simp
      apply(rule conjI)
      using prems(1-7) prems(13) apply simp
      apply(rule conjI)
      using prems(1-7) prems(14) apply simp
      apply(rule conjI)
      using prems(1-7) prems(15) apply simp
      apply(rule conjI)
      using prems(1-7) prems(16) apply simp
      apply(rule conjI)
      using prems(1-7) prems(17) apply simp
      apply(rule conjI)
      using prems(1-7) prems(18) apply simp
      apply(rule conjI)
      using prems(1-7) prems(19) apply simp
      apply(rule conjI)
      using prems(1-7) prems(20) apply simp
      apply(rule conjI)
      using prems(1-7) prems(21) apply simp
      apply(rule conjI)
      using prems(1-7) prems(21) prems(22) substate_refl apply simp
      apply(rule conjI)
      using prems(1-7) prems(23) apply simp
      using prems(1-7) prems(24) by simp
    done
  done

end
