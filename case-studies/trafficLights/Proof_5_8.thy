theory Proof_5_8
  imports Proof_5
begin

abbreviation s where "s s0 requestButton_value \<equiv> (toEnv
          (setPstate
            (setVarBool (setVarBool (setVarAny s0 requestButton_value) minimalRed PRESSED) redAfterMinimalRed
              NOT_PRESSED)
            Ctrl green)) "

lemma VC8_R5_aux1: "toEnvP s0 \<and>  getPstate (setVarAny s0 requestButton_value) Ctrl = redToGreen \<and> 
RED_TO_GREEN_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<and> 
(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<Longrightarrow>
ltimeEnv s0 Ctrl = RED_TO_GREEN_TIME_LIMIT"
  using substate_refl by auto

lemma VC8_R5_aux2: "toEnvP s2 \<and>substate s2 s3 \<and>  s3 = s s0 requestButton_value \<and> toEnvNum s2 s3 < T1 \<and> substate s2 s0 \<Longrightarrow>
toEnvNum s2 s0 < T1 - 1"
  apply auto
   apply(simp split: if_splits)
  using substate_refl substate_asym[of s0 "s s0 requestButton_value"] by auto
   


lemma VC8_R5_aux3: "toEnvP s2 \<and> toEnvP s0 \<and> substate s2 s0 \<and> toEnvNum s2 s3 < T1 \<and> s3 = s s0 requestButton_value \<Longrightarrow>
toEnvNum s2 s0 < T1"
  apply auto
  apply(simp split: if_splits)
  using substate_refl substate_asym[of s0 "s s0 requestButton_value"] by  auto

lemma VC8_R5: " ((toEnvP s0 \<and>
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
        toEnvP s0 \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
              0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
              (\<exists>s2. toEnvP s2 \<and>
                    substate s2 s1 \<and>
                    toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = T2) \<or>
              (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
            getPstate s1 Ctrl = minimalRed) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and>
            substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
            toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
        (\<forall>s1. toEnvP s1 \<and>
              substate s1 s0 \<and>
              getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
              (\<exists>s2. toEnvP s2 \<and>
                    substate s2 s1 \<and>
                    getPstate s2 Ctrl = minimalRed \<and>
                    ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                    getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                    (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                          getPstate s3 Ctrl = redAfterMinimalRed \<and>
                          getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
              0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
              (\<exists>s2. toEnvP s2 \<and>
                    substate s2 s1 \<and>
                    toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                    getPstate s2 Ctrl = redAfterMinimalRed \<and>
                    (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and> substate s2 s0 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
            getPstate s1 Ctrl = redToGreen) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and>
            substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
            toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
              0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> T2) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
              (\<exists>s2. toEnvP s2 \<and>
                    substate s2 s1 \<and>
                    toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                    getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
            getPstate s1 Ctrl = green) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and>
            substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
            toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
              getPstate s1 Ctrl = minimalRed \<or>
              getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
        (\<forall>s1 s2.
            toEnvP s1 \<and>
            toEnvP s2 \<and>
            substate s1 s2 \<and>
            substate s2 s0 \<and>
            toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
            getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
            getVarBool s1 Ctrl = NOT_PRESSED) \<and>
        (\<forall>s2. toEnvP s2 \<and>
              substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
              (\<exists>s1. toEnvP s1 \<and>
                    substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
        (\<forall>s1. toEnvP s1 \<and>
              substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
              (\<exists>s2. toEnvP s2 \<and>
                    substate s2 s1 \<and>
                    toEnvNum s2 s1 = Ctrl \<and>
                    getPstate s2 Ctrl = minimalRed \<and>
                    ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                    (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
        (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
              getVarBool s1 redAfterMinimalRed = NOT_PRESSED)) \<and>
       env (setVarAny s0 requestButton_value) requestButton_value \<and>
       getPstate (setVarAny s0 requestButton_value) Ctrl = redToGreen \<and>
       RED_TO_GREEN_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<Longrightarrow>
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
    apply(rule cut_rl[of "toEnvNum s1 s0 < T1"])
apply(rule cut_rl[of "\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> toEnvNum s2 s0 \<le> T1
 \<longrightarrow>      getVarBool s2 minimalRed = NOT_PRESSED"])
apply (meson less_or_eq_imp_le substate_trans)
     apply(rule cut_rl[of "\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> toEnvNum s2 s0 \<le> MINIMAL_RED_TIME_LIMIT + ltimeEnv s0 Ctrl
 \<longrightarrow>      getVarBool s2 minimalRed = NOT_PRESSED"])
      apply(rule cut_rl[of "ltimeEnv s0 Ctrl = RED_TO_GREEN_TIME_LIMIT"])
       apply metis
      apply(rule VC8_R5_aux1)
      apply fast
     apply(rule redToGreen_red_at_least_T1[of _ s0])
     apply(rule cut_rl[of "getPstate s0 Ctrl = redToGreen"])
  using substate_refl apply fast
     apply (smt (verit) getPstate.simps(6)) 
    apply(rule cut_rl[of "toEnvNum s2 s0 < T1 - 1"])
  using toEnvNum3[of s1 s2 s0] apply arith
    apply(rule VC8_R5_aux2)
    apply blast
apply (metis substate.simps(2) substate.simps(4) substate.simps(6) substate.simps(7) toEnvP.simps(4) toEnvP.simps(6) toEnvP.simps(7))
  apply(rule cut_rl [of "substate s3 s0"])
   apply meson
by (metis substate.simps(2) substate.simps(4) substate.simps(6) substate.simps(7) toEnvP.simps(4) toEnvP.simps(6) toEnvP.simps(7))
  
theorem proof_5_8: "VC8 inv5 s0 requestButton_value"
  apply(simp only: VC8_def inv5_def R5_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
  apply(rule conjI)
   apply simp
  apply((rule allI);(rule allI);(rule allI))
  apply(rule impI)
   apply((rule VC8_R5);assumption)
  
  