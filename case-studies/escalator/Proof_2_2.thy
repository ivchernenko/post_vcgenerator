theory Proof_2_2
  imports Proofs_2 Extra2
begin

abbreviation s where "s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value \<equiv>
(toEnv
             (setPstate (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) ERROR
               Ctrl'emergency))"

lemma VC2_R2_ind_proof: "toEnvP s0 \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'motionless \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          ((getPstate s2 ERROR = Ctrl'goUp \<or> getPstate s2 ERROR = Ctrl'goDown) \<and>
           ltime s2 ERROR = DELAY'TIMEOUT \<and> \<not> (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and> ltime s2 ERROR = SUSPENSION_TIME'TIMEOUT \<and> \<not> getVarBool s2 moving') \<and>
          \<not> getVarBool s3 alarmButton' \<and>
          \<not> getVarBool s3 stuck' \<and>
          (\<forall>s4 s5.
              toEnvP s4 \<and>
              toEnvP s5 \<and>
              substate s3 s4 \<and>
              substate s4 s5 \<and>
              substate s5 s1 \<and>
              toEnvNum s4 s5 = ERROR \<longrightarrow>
              getPstate s4 ERROR = Ctrl'motionless \<and>
              \<not> getVarBool s5 alarmButton' \<and>
              \<not> getVarBool s5 stuck' \<and> \<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<or>
      (\<forall>s4 s5.
          toEnvP s4 \<and>
          toEnvP s5 \<and>
          substate s4 s5 \<and>
          substate s5 s1 \<and>
          toEnvNum s4 s5 = ERROR \<longrightarrow>
          getPstate s4 ERROR = Ctrl'motionless \<and>
          \<not> getVarBool s5 alarmButton' \<and> \<not> getVarBool s5 stuck' \<and> \<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          ((getPstate s2 ERROR = Ctrl'motionless \<or> getPstate s2 ERROR = Ctrl'goUp) \<and>
           (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and>
           ltime s2 ERROR = SUSPENSION_TIME'TIMEOUT \<and> getVarBool s2 moving' \<and> getVarBool s2 direction' = UP') \<and>
          \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3 stuck')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s0 \<and> getPstate s3 ERROR = Ctrl'goUp \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow> getPstate s1 ERROR = Ctrl'goUp) \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> \<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          ((getPstate s2 ERROR = Ctrl'motionless \<or> getPstate s2 ERROR = Ctrl'goDown) \<and>
           (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and>
           ltime s2 ERROR = SUSPENSION_TIME'TIMEOUT \<and> getVarBool s2 moving' \<and> getVarBool s2 direction' = DOWN') \<and>
          \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3 stuck')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s0 \<and> getPstate s3 ERROR = Ctrl'goDown \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow> getPstate s1 ERROR = Ctrl'goDown) \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> \<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'stuckState \<longrightarrow> ltime s1 ERROR \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = UP' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          (getPstate s2 ERROR = Ctrl'goUp \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and> getVarBool s2 moving' \<and> getVarBool s2 direction' = UP') \<and>
          \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = DOWN' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          (getPstate s2 ERROR = Ctrl'goDown \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and> getVarBool s2 moving' \<and> getVarBool s2 direction' = DOWN') \<and>
          \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> \<not> getVarBool s1 moving' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          (getPstate s2 ERROR = Ctrl'motionless \<or> getPstate s2 ERROR = Ctrl'stuckState \<and> \<not> getVarBool s2 moving') \<and>
          \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s0 \<and> getPstate s3 ERROR = Ctrl'stuckState \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
            getPstate s1 ERROR = Ctrl'stuckState \<and>
            getVarBool s1 moving' = getVarBool s3 moving' \<and> getVarBool s1 direction' = getVarBool s3 direction') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> getVarBool s2 up' = DOWN' \<and> getVarBool s2 down' = DOWN')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'emergency \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          getPstate s2 ERROR \<noteq> Ctrl'emergency \<and>
          getVarBool s3 alarmButton' \<and>
          (\<forall>s4 s5.
              toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
              getPstate s4 ERROR = Ctrl'emergency \<and> getVarBool s5 up' = DOWN' \<and> getVarBool s5 down' = DOWN'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'motionless \<longrightarrow>
      getVarBool s1 up' = DOWN' \<and> getVarBool s1 down' = DOWN' \<and> \<not> getVarBool s1 moving') \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow>
      getVarBool s1 up' = UP' \<and> getVarBool s1 down' = DOWN' \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = UP') \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow>
      getVarBool s1 up' = DOWN' \<and> getVarBool s1 down' = UP' \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = DOWN') \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
      getPstate s1 ERROR = Ctrl'motionless \<or>
      getPstate s1 ERROR = Ctrl'goUp \<or>
      getPstate s1 ERROR = Ctrl'goDown \<or> getPstate s1 ERROR = Ctrl'stuckState \<or> getPstate s1 ERROR = Ctrl'emergency) \<Longrightarrow>
toEnvP s2 \<Longrightarrow>
 getPstate (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) ERROR =
      Ctrl'motionless \<and>
     getVarBool (setVarAny s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value)
      alarmButton' \<Longrightarrow>
toEnvP s5 \<and>
    substate s2 s5 \<and> substate s5 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) \<longrightarrow>
    pred2 s1 s2 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) s5"
 subgoal premises extraInvs0
    apply(induction rule: state_down_ind)
    using extraInvs0(1) extraInvs0(2) apply simp
     apply(simp only: pred2_def)
     apply(rule impI)
     apply(rule cut_rl[of "getVarBool s0 up' = False \<and> getVarBool s0 down' = False"])
      apply((drule conjE)+)
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
      apply(drule allE[of _ s0])
       prefer 2
       apply assumption
      apply(drule impE)
        apply(rule conjI)
    using extraInvs0(1) apply fast
    using substate_refl apply (simp split: if_splits)
       prefer 2
       apply assumption
      apply fast
    apply(rule cut_rl[of "getPstate s0 Ctrl' = Ctrl'motionless"])
      apply (simp add: extraInvs0(1) substate_refl)
    using extraInvs0(3) apply simp

  subgoal for s5
      apply(simp only: pred2_def)
      apply(rule impI)
      apply(cases "(getVarBool (predEnv s5) up' = DOWN' \<and> getVarBool (predEnv s5) down' = DOWN' \<or>
 getVarBool (predEnv s5) userAtTop' \<or> getVarBool (predEnv s5) userAtBottom')")
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
      using le_add1 apply presburger
       apply(rule conjI)
      apply assumption
       apply (metis substate_antisym)
      apply(drule impE)
      apply(((rule conjI),blast)+)
        apply (metis substate_eq_or_predEnv)
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
        by (metis predEnv_substate_imp_eq_or_substate)
      done
    done
  done

theorem proof_2_2: "VC2 inv2 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC2_def inv2_def R2_def extraInv_def)
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
    apply(rule cut_rl[of "\<exists>s4. toEnvP s4 \<and>
         substate s2 s4 \<and>
         substate s4 s0 \<and>
         toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
         (getVarBool s4 up' = DOWN' \<and> getVarBool s4 down' = DOWN' \<or> getVarBool s4 userAtTop' \<or> getVarBool s4 userAtBottom') \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               (getVarBool s3 up' = UP' \<or> getVarBool s3 down' = UP') \<and> \<not> getVarBool s3 userAtTop' \<and> \<not> getVarBool s3 userAtBottom'
)"])
      apply(drule exE)
       prefer 2
       apply assumption
    subgoal for s4
      apply(rule exI[of _ s4])
      by simp
    thm prems(11)
    using prems(2) prems(4) prems(6) prems(7) prems(9) prems(11) prems(15) prems(17) prems(18) apply -[1]
     apply(drule allE[of _ s1])
      prefer 2
    apply assumption
      apply(drule allE[of _ s2])
      prefer 2
      apply assumption
     apply (simp split: if_splits)
    apply(rule cut_rl[of
 "pred2 s1 s2 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value) s2"])
     apply(simp only: pred2_def)
     apply(drule impE)
    using prems(2) prems(4) prems(6) prems(7) prems(11) prems(15) prems(17) prems(18) substate_trans substate_refl
    using substate_antisym apply blast
      prefer 2
      apply assumption
     apply assumption
    apply(rule mp[of
 "toEnvP s2 \<and> substate s2 s2 \<and>
 substate s2 (s s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value)"])
     apply(rule VC2_R2_ind_proof)
    using prems  apply fast
    using prems apply fast
    using prems apply fast
    apply(rule conjI)
    using prems apply fast
    apply(rule conjI)
    using substate_refl apply fast
    using prems by fast
  apply(simp only: extraInv_def[symmetric])
  using extra2 VC2_def by auto

end
