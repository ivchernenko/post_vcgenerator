theory Proof_5_26
  imports Proofs_5
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value \<equiv>
(toEnv
   (setPstate
     (setVarBool
       (setVarBool (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) up'
         DOWN')
       down' DOWN')
     ERROR Ctrl'emergency))"

theorem proof_5_26: "VC26 inv5 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC26_def inv5_def R5_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply((rule allI)+)
   apply(rule impI)
   apply((drule conjE)+)
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
    apply(rule disjE[OF le_imp_less_or_eq[OF prems(13)]])
    apply(rule cut_rl[of " \<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4  s0 \<and>
         toEnvNum s2 s4 \<le> ERROR \<and>
         getVarBool s4 up' = DOWN' \<and>
         getVarBool s4 down' = DOWN' \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 up' = UP' \<or> getVarBool s3 down' = UP')"])
      apply(drule exE)
       prefer 2
       apply assumption
    subgoal for s4
      apply(rule exI[of _ s4])
      by simp
    using prems(2) prems(4) prems(6) prems(8) prems(9) prems(11) prems(15) prems(16) apply -[1]
     apply(drule allE[of _ s1])
      prefer 2
      apply assumption
     apply(drule allE[of _ s2])
      prefer 2
      apply assumption
     apply(simp split: if_splits)
    apply(rule cut_rl[of "\<forall> s5. toEnvP s5 \<and> substate s2 s5 \<and> substate s5
 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) \<longrightarrow>
 pred5 s1 s2
 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) s5"])
     apply(drule allE[of _ s2])
      prefer 2
      apply assumption
     apply(drule impE)
       prefer 3
       apply assumption
    using prems(4,8) substate_refl apply fast
     apply(simp only: pred5_def)
     apply(drule impE)
       prefer 3
       apply assumption
    using prems(2)  prems(4) prems(6) prems(8) prems(9) prems(15) prems(16) substate_refl substate_trans substate_antisym
      apply blast
      apply blast
      apply(rule allI)
    subgoal premises toEnvNums2s for s5
      apply(induction rule: state_down_ind)
      using prems(8) apply simp
      apply(simp only: pred5_def)
       apply(rule impI)
       apply((drule conjE)+)
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

       apply(rule exI[of _ "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"])
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
       apply(rule conjI)
        apply simp
      using substate_trans substate_antisym apply blast

      subgoal for s5
        apply(simp only: pred5_def)
        apply(rule impI)
        apply(cases "getVarBool (predEnv s5) up' = False  \<and> getVarBool (predEnv s5) down' = False")
       apply(rule exI[of _ "predEnv s5"])
       apply(rule conjI)
        apply(rule toEnvP_substate_pred_imp_toEnvP_pred[of s2])
        apply blast
       apply(rule conjI)
      using substate_refl apply simp
       apply(rule conjI)
      using predEnv_substate substate_trans apply blast
       apply(rule conjI)
      using toEnvNum3[of s2 "predEnv s5"
 "(s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) "]
        apply force
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
      using substate_antisym apply fast
      apply(drule impE)
        apply(((rule conjI),blast)+)
      using substate_eq_or_predEnv apply blast
      prefer 2
       apply assumption
      apply(drule exE)
       prefer 2
       apply assumption
      subgoal for s4
        apply(rule exI[of _ s4])
       apply(rule conjI)
         apply blast
        apply(rule conjI)
        using predEnv_substate substate_trans apply blast
        apply(((rule conjI),blast)+)
        apply((drule conjE)+)
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
        using predEnv_substate_imp_eq_or_substate by blast
      done
    done
  done
