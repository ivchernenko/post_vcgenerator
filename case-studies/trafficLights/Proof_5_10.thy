theory Proof_5_10
  imports Requirements VCTheoryLemmas
begin

abbreviation s where "s s0 requestButton_value \<equiv> (toEnv (setPstate (setVarBool (setVarAny s0 requestButton_value) minimalRed NOT_PRESSED) Ctrl minimalRed))"

lemma VC10_R5_aux1: "toEnvP s2 \<and> toEnvP s0 \<and> substate s2 s0 \<and> toEnvNum s2 s3 < T1 \<and> s3 = s s0 requestButton_value \<Longrightarrow>
toEnvNum s2 s0 < T1"
  apply auto
  apply(simp split: if_splits)
  using substate_refl substate_asym[of s0 "s s0 requestButton_value"] by  auto

lemma VC10_R5: " (toEnvP s0 \<and>
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
       getPstate (setVarAny s0 requestButton_value) Ctrl = green \<and>
       300 \<le> ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<Longrightarrow>
       substate s1 s2 \<and>
       substate s2 s3 \<and>
       substate s3
        (toEnv (setPstate (setVarBool (setVarAny s0 requestButton_value) minimalRed NOT_PRESSED) Ctrl minimalRed)) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvP s3 \<and>
       toEnvNum s1 s2 = Ctrl \<and>
       toEnvNum s2 s3 < T1 \<and> getVarBool s1 minimalRed \<noteq> NOT_PRESSED \<and> getVarBool s2 minimalRed = NOT_PRESSED \<Longrightarrow>
       getVarBool s3 minimalRed = NOT_PRESSED"
  apply(cases "s3 = s s0 requestButton_value")
  apply (metis getVarBool.simps(2) getVarBool.simps(4) getVarBool.simps(7))
  apply(rule cut_rl [of "substate s3 s0"])
   apply blast
  by (metis substate.simps(2) substate.simps(4) substate.simps(6) substate.simps(7) toEnvP.simps(4) toEnvP.simps(6) toEnvP.simps(7))
   
    

theorem proof_5_2: "VC10 R5 s0 requestButton_value"
  apply(simp only: VC10_def R5_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI);(rule allI);(rule allI))
  apply(rule impI)
  by ((rule VC10_R5);assumption)
  