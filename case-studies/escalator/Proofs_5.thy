theory Proofs_5
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv5 where "inv5 s \<equiv> R5 s \<and> extraInv s"

thm R5_def

definition pred5 where "pred5 s1 s2 s s5 \<equiv>
substate s1 s2 \<and> substate s2 s5 \<and> substate s5 s \<and> toEnvP s1 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s5 \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s = 1 \<and>
(getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<and> getVarBool s2 alarmButton' \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> s4 \<noteq> s5 \<longrightarrow>
(getVarBool s4 up' = True \<or> getVarBool s4 down' = True)) \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s5 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 1 \<and>
getVarBool s4 up' = False \<and> getVarBool s4 down' = False \<and>
(\<forall> s3. toEnvP s3 \<and> substate s5 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> 
(getVarBool s3 up' = True \<or> getVarBool s3 down' = True)))"

lemma goUp_not_moving:
 " toEnvP s1 \<and> toEnvP s0 \<and> substate s1 s0 \<and>  substate s0 s \<and> toEnvNum s1 s0 = 0 \<and>
 getVarBool s1 alarmButton' \<and> getPstate s0 Ctrl' = Ctrl'goUp \<and>
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
\<Longrightarrow>
\<exists> s4. toEnvP s4 \<and> substate s4 s0 \<and> toEnvNum s4 s0 \<le> 1  \<and> getVarBool s4 up' = False \<and> getVarBool s4 down' = False"
    apply(cases "ltime s0 Ctrl' \<le> 1")
  apply(rule exE[of " (\<lambda> s2. \<exists> s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvNum s2 s3 = ERROR \<and>
          toEnvNum s2 s0 = ltime s0 ERROR \<and>
          ((getPstate s2 ERROR = Ctrl'motionless \<or> getPstate s2 ERROR = Ctrl'goUp) \<and>
           (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or>
           getPstate s2 ERROR = Ctrl'stuckState \<and>
           ltime s2 ERROR = SUSPENSION_TIME'TIMEOUT \<and> getVarBool s2 moving' \<and> getVarBool s2 direction' = UP') \<and>
          \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3 stuck')"])
    apply blast
   apply (drule exE)
    prefer 2
    apply assumption
  subgoal for s2 s3
    by (smt (verit) One_nat_def le_0_eq le_Suc_eq nat_le_linear shift_toEnvNum substate_antisym substate_shift substate_trans toEnvNum_id)
  by (metis leI zero_less_diff) 

theorem proof_5_1: "VC1 inv5 s0"
  apply(simp only: VC1_def inv5_def R5_def extraInv_def)
  by auto

theorem proof_6_7: "VC7 inv5 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC7_def)
  by auto

theorem proof_6_9: "VC9 inv5 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC9_def)
  by auto

theorem proof_6_11: "VC11 inv5 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC11_def)
  by auto

end

  
