theory Extra3
  imports ExtraInv VCTheoryLemmas
begin

theorem extra3: "VC3 extraInv s0 requestButton_value"
  apply(simp only: VC3_def extraInv_def)
proof
  print_state
  assume "(toEnvP s0 \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
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
           substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
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
           0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
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
     (\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
           (\<exists>s1. toEnvP s1 \<and>
                 substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = Ctrl \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
           getVarBool s1 redAfterMinimalRed = NOT_PRESSED)) \<and>
    env (setVarAny s0 requestButton_value) requestButton_value \<and>
    getPstate (setVarAny s0 requestButton_value) Ctrl = minimalRed \<and>
    getVarBool (setVarAny s0 requestButton_value) Ctrl \<and>
    \<not> MINIMAL_RED_TIME_LIMIT
       \<le> ltimeEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl"
  then obtain ei0: "toEnvP s0"
and ei1: " (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT)"
and ei2: " (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
           (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed))"
and ei3: " (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
         getPstate s1 Ctrl = minimalRed)"
and ei4: " (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
         toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
and ei5: " (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                 (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                       getPstate s3 Ctrl = redAfterMinimalRed \<and>
                       getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)))"
and ei6:"(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT)"
and ei7: "(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                 getPstate s2 Ctrl = redAfterMinimalRed \<and>
                 (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED)))"
and ei8: " (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and> substate s2 s0 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
         getPstate s1 Ctrl = redToGreen)"
and ei9: "(\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
         toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
and ei10: "(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"
and ei11: "(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                 getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT))"
and ei12: "(\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
         getPstate s1 Ctrl = green)"
and ei13: " (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
         toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
and ei14: " (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED)"
and ei15: "(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED)"
and ei16: " (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
           getPstate s1 Ctrl = minimalRed \<or>
           getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) "
and ei17: "(\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
         getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
         getVarBool s1 Ctrl = NOT_PRESSED)"
and ei18: " (\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
           (\<exists>s1. toEnvP s1 \<and>
                 substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED))"
and ei19: "(\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = Ctrl \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)))"
and ei20: " (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
           getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
and vc: " env (setVarAny s0 requestButton_value) requestButton_value \<and>
    getPstate (setVarAny s0 requestButton_value) Ctrl = minimalRed \<and>
    getVarBool (setVarAny s0 requestButton_value) Ctrl \<and>
    \<not> MINIMAL_RED_TIME_LIMIT
       \<le> ltimeEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl"
    by fast
  have "toEnvP (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED))"
    by auto
  moreover from ei1 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT)"
    by auto
  moreover  have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed))"
  proof
    fix s1
    show "toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)"
    proof cases
      assume 1: "s1 =  (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED))"
      show ?thesis
      proof
      from ei0 vc substate_refl ei2  have "(\<exists>s2. toEnvP s2 \<and>
           substate s2 s0 \<and>
           toEnvNum s2 s0 = ltimeEnv s0 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
     (\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<longrightarrow> getPstate s2 Ctrl = minimalRed)"
        by auto
      thus "(\<exists>s2. toEnvP s2 \<and>
          substate s2 s1 \<and>
          toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
    (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)"
      proof
        assume "\<exists>s2. toEnvP s2 \<and>
         substate s2 s0 \<and>
         toEnvNum s2 s0 = ltimeEnv s0 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT"
        with 1 vc show ?thesis by fastforce
      next
        assume "\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<longrightarrow> getPstate s2 Ctrl = minimalRed"
        with 1 vc show ?thesis by auto
      qed
    qed
  next
    assume "s1 \<noteq> toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) "
    with ei2 show ?thesis by auto
  qed
qed
  moreover  have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed)"
    using vc ei3 ei0 substate_refl by auto
  moreover from ei4 vc ei0 substate_refl have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
    sorry
  moreover from ei5 have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)))"
    by auto
  moreover from ei6 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT)"
    by auto
  moreover from ei7 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redAfterMinimalRed \<and>
                (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED)))"
    by auto
  moreover from ei8 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen)"
    by auto
  moreover from ei9 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
    by auto
  moreover from ei10 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"
    by auto
  moreover from ei11 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT))"
    by auto
  moreover from ei12 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green)"
    by auto
  moreover from ei13 vc have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
    by auto
  moreover from ei14 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED)"
    by auto
  moreover from ei15 vc ei0 substate_refl  have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED)"
    by auto
  moreover from ei16 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green)"
    by auto
  moreover from ei17 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED)"
    by auto
  moreover   have " (\<forall>s2. toEnvP s2 \<and>
          substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED))"
  proof
    fix s2
    show "toEnvP s2 \<and>
          substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)"
    proof cases
      assume 1: "s2 = (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED))"
      with vc  have " ( toEnvP s2 \<and> substate s2 s2 \<and> toEnvNum s2 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s2 Ctrl = PRESSED)"
        using ei0 by (cases s0; auto)
      then show ?thesis by blast
    next
      assume 1: "s2 \<noteq> (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED))"
      with ei18 show ?thesis by auto
    qed
  qed
  moreover from ei19 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) "
    by auto
  moreover from ei20 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
    by auto
  ultimately
  show " toEnvP (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redAfterMinimalRed \<and>
                (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s2. toEnvP s2 \<and>
          substate s2 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)" by blast
qed
