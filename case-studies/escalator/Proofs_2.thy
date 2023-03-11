theory Proofs_2
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"

definition pred2 where "pred2 s1 s2 s s5\<equiv> 
substate s1 s2 \<and> substate s2 s5 \<and> substate s5 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s5 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s = DELAY'TIMEOUT \<and>
(getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<and> \<not> getVarBool s2 userAtTop' \<and> \<not> getVarBool s2 userAtBottom' \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> s4 \<noteq> s5 \<longrightarrow> 
(getVarBool s4 up' = True \<or> getVarBool s4 down' = True) \<and> \<not> getVarBool s4 userAtTop' \<and> \<not> getVarBool s4 userAtBottom')
\<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s5 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
(getVarBool s4 up' = False \<and> getVarBool s4 down' = False \<or> getVarBool s4 userAtTop' \<or> getVarBool s4 userAtBottom') \<and>
(\<forall> s3. toEnvP s3 \<and> substate s5 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
(getVarBool s3 up' = True \<or> getVarBool s3 down' = True) \<and> \<not> getVarBool s3 userAtTop' \<and> \<not> getVarBool s3 userAtBottom'))"

lemma goUp_notMoving: "toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'goUp \<and>
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
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'stuckState \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
            getPstate s1 ERROR = Ctrl'stuckState \<and>
            getVarBool s1 moving' = getVarBool s3 moving' \<and> getVarBool s1 direction' = getVarBool s3 direction') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> getVarBool s2 up' = DOWN' \<and> getVarBool s2 down' = DOWN')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'motionless \<longrightarrow>
      getVarBool s1 up' = DOWN' \<and> getVarBool s1 down' = DOWN' \<and> \<not> getVarBool s1 moving')  \<Longrightarrow>
\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> ltime s1 Ctrl' \<and>
 (getVarBool s2 up' = False \<and> getVarBool s2 down' = False \<or> getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom')\<and>
(toEnvNum s2 s1 = ltime s1 Ctrl' \<longrightarrow> getVarBool s2 up' = False \<and> getVarBool s2 down' = False)
"
  apply(rule exE[of "(\<lambda> s2. \<exists> s3.
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
          \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3 stuck')"])
   apply blast
apply(drule exE)
   prefer 2
   apply assumption
  subgoal for s2 s3
    apply(cases "getPstate s2 Ctrl' = Ctrl'motionless")
     apply (smt (verit, best) nat_le_linear substate_trans)
    apply(cases "getPstate s2 Ctrl' = Ctrl'goUp")
    apply(rule exI[of _ s3])
    apply (smt (z3) nat_le_linear not_one_le_zero numeral_eq_iff semiring_norm(85) semiring_norm(90) shift_toEnvNum substate_antisym substate_shift substate_trans toEnvNum_id)
       apply(rule cut_rl[of "getPstate s2 Ctrl' = Ctrl'stuckState"])
     apply (smt (z3) nat_le_linear one_less_numeral_iff semiring_norm(76) substate_linear substate_trans toEnvNum_id zero_less_diff)
    by blast
  done



lemma goDown_notMoving: "toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'goDown \<and>
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
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 ERROR = Ctrl'stuckState \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 ERROR \<longrightarrow>
            getPstate s1 ERROR = Ctrl'stuckState \<and>
            getVarBool s1 moving' = getVarBool s3 moving' \<and> getVarBool s1 direction' = getVarBool s3 direction') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 ERROR - ERROR \<longrightarrow>
            \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> getVarBool s2 up' = DOWN' \<and> getVarBool s2 down' = DOWN')) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 ERROR = Ctrl'motionless \<longrightarrow>
      getVarBool s1 up' = DOWN' \<and> getVarBool s1 down' = DOWN' \<and> \<not> getVarBool s1 moving')  \<Longrightarrow>
\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> ltime s1 Ctrl' \<and>
 (getVarBool s2 up' = False \<and> getVarBool s2 down' = False \<or> getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom')
"
 apply(rule exE[of "(\<lambda> s2. \<exists> s3.
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
          \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3 stuck')"])
   apply blast
apply(drule exE)
   prefer 2
   apply assumption
  subgoal for s2 s3
    apply(cases "getPstate s2 Ctrl' = Ctrl'motionless")
     apply (smt (verit, best) nat_le_linear substate_trans)
    apply(cases "getPstate s2 Ctrl' = Ctrl'goDown")
    apply(rule exI[of _ s3])
     apply (metis (mono_tags, opaque_lifting) eval_nat_numeral(3) n_not_Suc_n nat_le_linear shift_toEnvNum substate_antisym substate_shift substate_trans)
    apply(rule cut_rl[of "getPstate s2 Ctrl' = Ctrl'stuckState"])
    apply (smt (z3) nat_le_linear one_less_numeral_iff semiring_norm(76) substate_linear substate_trans toEnvNum_id zero_less_diff)
    by blast
  done

theorem proof_2_7: "VC7 inv2 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC7_def)
  by auto

end