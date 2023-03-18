theory Proofs_4
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv4 where "inv4 s \<equiv> R4 s \<and> extraInv s"

thm extraInv_def

lemma stuckState_R4: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 < SUSPENSION_TIME'TIMEOUT - 1 \<and> getPstate s0 Ctrl' = Ctrl'stuckState \<and>
 ltime s0 Ctrl' = SUSPENSION_TIME'TIMEOUT \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<longrightarrow> ltime s1 ERROR \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = UP' \<longrightarrow>
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
      substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = DOWN' \<longrightarrow>
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
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> \<not> getVarBool s1 moving' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          (getPstate s2 ERROR = Ctrl'motionless \<or> getPstate s2 ERROR = Ctrl'stuckState \<and> \<not> getVarBool s2 moving') \<and>
          \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'stuckState  \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
            getPstate s1 ERROR = Ctrl'stuckState \<and>
            getVarBool s1 moving' = getVarBool s3 moving' \<and> getVarBool s1 direction' = getVarBool s3 direction') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> getVarBool s2 up' = DOWN' \<and> getVarBool s2 down' = DOWN')) 
 \<longrightarrow>
\<not>(getVarBool s1 up' = True \<or> getVarBool s1 down'= True) \<or> \<not> getVarBool s2 stuck'"
  by metis

lemma goUp_R4: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 < SUSPENSION_TIME'TIMEOUT - 1 \<and> getPstate s0 Ctrl' = Ctrl'goUp\<and>
 ltime s0 Ctrl' = DELAY'TIMEOUT \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow>
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
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'goUp \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow> getPstate s1 ERROR = Ctrl'goUp) \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> \<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom'))) 
 \<longrightarrow>
\<not>(getVarBool s1 up' = True \<or> getVarBool s1 down'= True) \<or> \<not> getVarBool s2 stuck'"
  apply(rule impI)
  apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT - 1"])
   apply metis
  by auto

lemma goDown_R4: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 < SUSPENSION_TIME'TIMEOUT - 1 \<and> getPstate s0 Ctrl' = Ctrl'goDown\<and>
 ltime s0 Ctrl' = DELAY'TIMEOUT \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow>
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
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'goDown \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow> getPstate s1 ERROR = Ctrl'goDown) \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> \<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom')))  
 \<longrightarrow>
\<not>(getVarBool s1 up' = True \<or> getVarBool s1 down'= True) \<or> \<not> getVarBool s2 stuck'"
  apply(rule impI)
  apply(rule cut_rl[of "toEnvNum s2 s0 < DELAY'TIMEOUT - 1"])
   apply metis
  by auto

lemma motionless_R4: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> 1 \<le> toEnvNum s2 s0 \<and> toEnvNum s2 s0 < SUSPENSION_TIME'TIMEOUT - 1 \<and> getPstate s0 Ctrl' = Ctrl'motionless \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'motionless \<longrightarrow>
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
              toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
              getPstate s4 ERROR = Ctrl'motionless \<and>
              \<not> getVarBool s5 alarmButton' \<and>
              \<not> getVarBool s5 stuck' \<and> \<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<or>
      (\<forall>s4 s5.
          toEnvP s4 \<and> toEnvP s5 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
          getPstate s4 ERROR = Ctrl'motionless \<and>
          \<not> getVarBool s5 alarmButton' \<and> \<not> getVarBool s5 stuck' \<and> \<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<longrightarrow> ltime s1 ERROR \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = UP' \<longrightarrow>
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
      substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = DOWN' \<longrightarrow>
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
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'stuckState \<and> \<not> getVarBool s1 moving' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s1 = ltime s1 ERROR \<and>
          (getPstate s2 ERROR = Ctrl'motionless \<or> getPstate s2 ERROR = Ctrl'stuckState \<and> \<not> getVarBool s2 moving') \<and>
          \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'stuckState  \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
            getPstate s1 ERROR = Ctrl'stuckState \<and>
            getVarBool s1 moving' = getVarBool s3 moving' \<and> getVarBool s1 direction' = getVarBool s3 direction') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> getVarBool s2 up' = DOWN' \<and> getVarBool s2 down' = DOWN')) 
 \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goUp \<longrightarrow>
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
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'goUp \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow> getPstate s1 ERROR = Ctrl'goUp) \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> \<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow> ltime s1 ERROR \<le> DELAY'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'goDown \<longrightarrow>
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
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'goDown \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow> getPstate s1 ERROR = Ctrl'goDown) \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> \<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom')))  
 \<longrightarrow>
\<not>(getVarBool s1 up' = True \<or> getVarBool s1 down'= True) \<or> \<not> getVarBool s2 stuck'"
  apply(rule impI)
  apply(rule cut_rl[of " (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          ((getPstate s2 ERROR = Ctrl'goUp \<or> getPstate s2 ERROR = Ctrl'goDown) \<and>
           ltime s2 ERROR = DELAY'TIMEOUT \<and> \<not> (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and> ltime s2 ERROR = SUSPENSION_TIME'TIMEOUT \<and> \<not> getVarBool s2 moving') \<and>
          \<not> getVarBool s3 alarmButton' \<and>
          \<not> getVarBool s3 stuck' \<and>
          (\<forall>s4 s5.
              toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s0 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
              getPstate s4 ERROR = Ctrl'motionless \<and>
              \<not> getVarBool s5 alarmButton' \<and>
              \<not> getVarBool s5 stuck' \<and> \<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<or>
      (\<forall>s4 s5.
          toEnvP s4 \<and> toEnvP s5 \<and> substate s4 s5 \<and> substate s5 s0 \<and> toEnvNum s4 s5 = ERROR \<longrightarrow>
          getPstate s4 ERROR = Ctrl'motionless \<and>
          \<not> getVarBool s5 alarmButton' \<and> \<not> getVarBool s5 stuck' \<and> \<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))"])
   apply(drule disjE)
     prefer 3
     apply assumption
    apply(drule exE)
     prefer 2
     apply assumption
    apply(drule exE)
     prefer 2
     apply assumption
  subgoal for s3 s4
    apply(cases "substate s2 s3")
     apply(cases "getPstate s3 Ctrl' = Ctrl'goUp")
      apply(rule impE[OF goUp_R4[of s1 s2 s3 s]])
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
    using substate_trans
        apply meson
       apply(rule conjI)
        apply fast
       apply(rule conjI)
    using substate_trans[of s3 s4 s0] toEnvNum3[of s2 s3 s0] apply arith
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply linarith
       apply fast
    apply assumption
     apply(cases "getPstate s3 Ctrl' = Ctrl'goDown")
      apply(rule impE[OF goDown_R4[of s1 s2 s3 s]])
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
    using substate_trans
        apply meson
       apply(rule conjI)
        apply fast
       apply(rule conjI)
    using substate_trans[of s3 s4 s0] toEnvNum3[of s2 s3 s0] apply arith
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply linarith
       apply fast
      apply assumption
     apply(rule cut_rl[of "getPstate s3 Ctrl' = Ctrl'stuckState"])
      apply(rule impE[OF stuckState_R4[of s1 s2 s3 s]])
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply fast
       apply(rule conjI)
    using substate_trans
        apply meson
       apply(rule conjI)
        apply fast
       apply(rule conjI)
    using substate_trans[of s3 s4 s0] toEnvNum3[of s2 s3 s0] apply arith
       apply(rule conjI)
        apply fast
       apply(rule conjI)
        apply linarith
       apply fast
      apply assumption
     apply fast
    apply(cases "s2 = s4")
     apply fast
    apply(rule cut_rl[of "substate s4 s1"])
     apply blast
    apply(rule disjE[of "substate s4 s1" "substate s1 s4 \<and> s1 \<noteq> s4"])
    using substate_trans substate_linear substate_refl
      apply (smt (verit)) 
     apply assumption
    apply(rule cut_rl[of "substate s3 s2 \<and> s2 \<noteq> s3"])
     apply(rule disjE[of "substate s1 s3" "substate s3 s1 \<and> s1 \<noteq> s3"])
    using substate_linear substate_refl
       apply metis
      apply(rule cut_rl[of "toEnvNum s3 s2 > 0"])
       apply(rule cut_rl[of "s1 = s3"])
        apply(rule cut_rl[of "s2 = s4"])
         apply fast
        apply(rule cut_rl[of "toEnvNum emptyState s2 = toEnvNum emptyState s4"])
    using gtimeE_inj
         apply (smt (verit) substate_linear)
    using toEnvNum3[of emptyState s1 s2] toEnvNum3[of emptyState s3 s4] emptyState_substate
        apply (smt (verit)) 
       apply(rule cut_rl[of "toEnvNum s1 s3 = 0"])
    using substate_toEnvNum_id
        apply meson
    using toEnvNum3[of s1 s3 s2] apply arith
    using toEnvNum3 gtimeE_inj
      apply (smt (verit) gr0I substate_toEnvNum_id) 
     apply(rule cut_rl[of "s1=s4"])
      apply fast
     apply(rule cut_rl[of "toEnvNum s1 s4 = 0"])
    using substate_toEnvNum_id
      apply meson
     apply(rule cut_rl[of "toEnvNum s3 s1 > 0"])
    using toEnvNum3[of s3 s1 s4] apply arith
    using substate_toEnvNum_id
     apply (smt (verit) gr0I) 
    using substate_linear substate_refl
    by (smt (verit) \<open>substate s3 s4 \<and> substate s4 s0 \<Longrightarrow> substate s3 s0\<close>)
   apply meson
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
  by blast

theorem proof_4_1: "VC1 inv4 s0"
  apply(simp only: VC1_def inv4_def R4_def extraInv_def)
  by auto

end
