theory Proof_5_2
  imports Requirements VCTheoryLemmas
begin

abbreviation s where "s s0 requestButton_value \<equiv> (toEnv
          (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
            redAfterMinimalRed))"

lemma VC2_R5_aux1: "toEnvP s2 \<and> toEnvP s0 \<and> substate s2 s0 \<and> toEnvNum s2 s3 < T1 \<and> s3 = s s0 requestButton_value \<Longrightarrow>
toEnvNum s2 s0 < T1"
  apply auto
  apply(simp split: if_splits)
  using substate_refl substate_asym[of s0 "s s0 requestButton_value"] by  auto

lemma VC2_R5: " (toEnvP s0 \<and>
        (\<forall>s1 s2 s3.
            substate s1 s2 \<and>
            substate s2 s3 \<and>
            substate s3 s0 \<and>
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            toEnvP s3 \<and>
            toEnvNum s1 s2 = Ctrl \<and>
            toEnvNum s2 s3 < T1 \<and> getVarBool s1 minimalRed \<noteq> NOT_PRESSED \<and> getVarBool s2 minimalRed = NOT_PRESSED \<longrightarrow>
            getVarBool s3 minimalRed = NOT_PRESSED)) \<and>
       env (setVarAny s0 requestButton_value) requestButton_value \<and>
       getPstate (setVarAny s0 requestButton_value) Ctrl = minimalRed \<and>
       getVarBool (setVarAny s0 requestButton_value) Ctrl \<and>
       MINIMAL_RED_TIME_LIMIT
       \<le> ltimeEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl \<Longrightarrow>
       substate s1 s2 \<and>
       substate s2 s3 \<and>
       substate s3 (s s0 requestButton_value) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvP s3 \<and>
       toEnvNum s1 s2 = Ctrl \<and>
       toEnvNum s2 s3 < T1 \<and> getVarBool s1 minimalRed \<noteq> NOT_PRESSED \<and> getVarBool s2 minimalRed = NOT_PRESSED \<Longrightarrow>
       getVarBool s3 minimalRed = NOT_PRESSED"
  apply(cases "s3 = s s0 requestButton_value")
   apply(cases "s2 = s s0 requestButton_value")
    apply blast
   apply(rule cut_rl[of "substate s2 s0"])
    apply(rule cut_rl[of "getVarBool s0 trafficLight = RED"])
  apply (metis getVarBool.simps(2) getVarBool.simps(4) getVarBool.simps(6) getVarBool.simps(7) numeral_eq_iff one_eq_numeral_iff semiring_norm(85) semiring_norm(89))
    apply(drule conjE)
     prefer 2
     apply assumption
apply(drule conjE)
     prefer 2
     apply assumption
apply(drule conjE)
     prefer 2
     apply assumption
apply(drule allE[of _ s1])
     prefer 2
  apply assumption
   apply(drule allE[of _ s2])
     prefer 2
     apply assumption 
apply(drule allE[of _ s0])
     prefer 2
     apply assumption
    apply(rule cut_rl[of "toEnvNum s2 s0 < T1"])
  using substate_refl apply fast
    apply((rule VC2_R5_aux1);fast)
  apply (metis substate.simps(2) substate.simps(4) substate.simps(6) substate.simps(7) toEnvP.simps(4) toEnvP.simps(6) toEnvP.simps(7))
  apply(rule cut_rl [of "substate s3 s0"])
   apply blast
  by (metis substate.simps(2) substate.simps(4) substate.simps(6) substate.simps(7) toEnvP.simps(4) toEnvP.simps(6) toEnvP.simps(7))
   

theorem proof_5_2: "VC2 R5 s0 requestButton_value"
  apply(simp only: VC2_def R5_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI);(rule allI);(rule allI))
  apply(rule impI)
  by ((rule VC2_R5);assumption)
  