theory Extra2
  imports ExtraInv VCTheoryLemmas
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value \<equiv>
(toEnv
             (setPstate (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) ERROR
               Ctrl'emergency))"

theorem extra2: "VC2 extraInv env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC2_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  subgoal
    apply((drule conjE[of _ _ ?thesis])+)
                        defer
                        apply assumption+
    subgoal premises prems
      apply(rule conjI)
      using prems(1-4) prems(5) apply simp
      apply(rule conjI)
      using prems(1-4) prems(6) apply simp
      apply(rule conjI)
      using prems(1-4) prems(7) apply simp
 apply(rule conjI)
      using prems(1-4) prems(8) apply simp
 apply(rule conjI)
      using prems(1-4) prems(9) apply simp
 apply(rule conjI)
      using prems(1-4) prems(10) apply simp
 apply(rule conjI)
      using prems(1-4) prems(11) apply simp
 apply(rule conjI)
      using prems(1-4) prems(12) apply simp
 apply(rule conjI)
      using prems(1-4) prems(13) apply simp
 apply(rule conjI)
      using prems(1-4) prems(14) apply simp
 apply(rule conjI)
      using prems(1-4) prems(15) apply simp
 apply(rule conjI)
      using prems(1-4) prems(16) apply simp
      apply(rule conjI)
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value")
         apply(rule impI)
         apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"])
        using prems(1-4) substate_refl toEnvNum_id apply -
         apply(((rule conjI),simp)+)
        using substate_trans substate_antisym
         apply (metis le_numeral_extra(4) not_one_le_zero)
        using prems(17) by simp
 apply(rule conjI)
      using prems(1-4) prems(18) apply simp
 apply(rule conjI)
      using prems(1-4) prems(19) apply simp
 apply(rule conjI)
      using prems(1-4) prems(20) apply simp
      using prems(1-4) prems(21) by simp
    done
  done

end     
      