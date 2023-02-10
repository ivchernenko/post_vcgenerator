theory Extra4
  imports ExtraInv VCTheoryLemmas
begin

theorem extra4: "VC4 extraInv s0 requestButton_value"
  apply(simp only: VC4_def extraInv_def)
proof
  assume " (toEnvP s0 \<and>
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
    \<not> getVarBool (setVarAny s0 requestButton_value) Ctrl \<and>
    MINIMAL_RED_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButton_value) Ctrl"
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
and vc: "env (setVarAny s0 requestButton_value) requestButton_value \<and>
    getPstate (setVarAny s0 requestButton_value) Ctrl = minimalRed \<and>
    \<not> getVarBool (setVarAny s0 requestButton_value) Ctrl \<and>
    MINIMAL_RED_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButton_value) Ctrl" by fast
  have "toEnvP (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed))"
    by simp
  moreover from ei1 ei0 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT)"
    by auto
  moreover from ei2 ei0 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed))"
    by auto
  moreover from ei3 ei0 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed)" by auto
  moreover from ei4 ei0 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)" by auto
  moreover  have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)))"
  proof
    fix s1
    show "toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))"
    proof cases
      assume 1: "s1 = (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed))"
      show ?thesis
      proof
        assume 2: "toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED"
         have "(toEnvP s0 \<and>
                substate s0 s1 \<and>
                getPstate s0 Ctrl = minimalRed \<and>
                ltimeEnv s0 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s0 redAfterMinimalRed = NOT_PRESSED) \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s0 s3 \<and> substate s3 s1 \<and> s0 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)" 
         proof
           from 1 2 ei0 ei1 vc substate_refl show " toEnvP s0 \<and>
    substate s0 s1 \<and>
    getPstate s0 Ctrl = minimalRed \<and>
    ltimeEnv s0 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> getVarBool s0 redAfterMinimalRed = NOT_PRESSED"
             by auto
         next
           show " \<forall>s3. toEnvP s3 \<and> substate s0 s3 \<and> substate s3 s1 \<and> s0 \<noteq> s3 \<longrightarrow>
         getPstate s3 Ctrl = redAfterMinimalRed \<and>
         getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED"
           proof
             fix s3
             show "toEnvP s3 \<and> substate s0 s3 \<and> substate s3 s1 \<and> s0 \<noteq> s3 \<longrightarrow>
          getPstate s3 Ctrl = redAfterMinimalRed \<and>
          getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED"
               using 1 2 vc substate_asym[of s0 s3] by auto
           qed
         qed
         thus "\<exists>s2. toEnvP s2 \<and>
       substate s2 s1 \<and>
       getPstate s2 Ctrl = minimalRed \<and>
       ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
       getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
       (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
             getPstate s3 Ctrl = redAfterMinimalRed \<and>
             getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)"
           by auto
       qed
     next
       assume  "s1 \<noteq> (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed))"
       with ei5 show ?thesis by auto
     qed
   qed
   moreover from ei6 ei0 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT)"
     by auto
   moreover from ei7 ei0 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redAfterMinimalRed \<and>
                (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED)))"
     by auto
   moreover from ei8 ei0 vc have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen)"
     by auto
   moreover from ei9 ei0 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
     by auto
   moreover from ei10 ei0 vc have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"
     by auto
   moreover from ei11 ei0 vc have "  (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT))"
     by auto
   moreover from ei12 ei0 vc have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green)"
     by auto
   moreover from ei13 ei0 vc have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
     by auto
   moreover from ei14 ei0 vc have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED)"
     by auto
   moreover from ei15 ei0 vc substate_refl have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED)"
     by auto
   moreover from ei16 ei0 vc substate_refl have "(\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green)"
     by auto
   moreover from ei17 ei0 vc substate_refl have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED)"
     by auto
   moreover from ei18 ei0 vc substate_refl have "(\<forall>s2. toEnvP s2 \<and>
          substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED))"
     by auto
   moreover have " (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)))"
   proof
     fix s1
     show "toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))"
     proof cases
       assume 1: "s1 = (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed))"
       show ?thesis
       proof
         assume 2: "toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed"
        from 1 2 ei0 ei1 vc substate_refl toEnvNum_id  have "toEnvP s0 \<and>
                substate s0 s1 \<and>
                toEnvNum s0 s1 = Ctrl \<and>
                getPstate s0 Ctrl = minimalRed \<and>
                ltimeEnv s0 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s0 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)"
          by auto
        thus " \<exists>s2. toEnvP s2 \<and>
         substate s2 s1 \<and>
         toEnvNum s2 s1 = Ctrl \<and>
         getPstate s2 Ctrl = minimalRed \<and>
         ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)"
          by auto
      qed
    next
      assume "s1 \<noteq> (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed))"
      with ei19 show ?thesis by auto
    qed
  qed
  moreover from ei20 ei0 vc substate_refl have "(\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
    by auto
  ultimately show "toEnvP (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
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
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
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
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s2. toEnvP s2 \<and>
          substate s2 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
    by fast
qed

