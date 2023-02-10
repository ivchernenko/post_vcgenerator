theory Proof_2_5
  imports Requirements VCTheoryLemmas
begin

theorem proof_2_5: "VC5 inv2 s0 requestButtonValue"
  apply(simp only: VC5_def inv2_def  R2_def extraInv_def)
proof
  print_state
  assume " ((toEnvP s0 \<and>
      (\<forall>s1 s2 s3.
          substate s1 s2 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          toEnvNum s1 s2 = Ctrl \<and>
          toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
          getVarBool s3 minimalRed = PRESSED)) \<and>
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
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> 0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> T2) \<and>
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
    env (setVarAny s0 requestButtonValue) requestButtonValue \<and>
    getPstate (setVarAny s0 requestButtonValue) Ctrl = minimalRed \<and>
    \<not> getVarBool (setVarAny s0 requestButtonValue) Ctrl \<and>
    \<not> MINIMAL_RED_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButtonValue) Ctrl "
  then obtain reqs0: "(toEnvP s0 \<and>
      (\<forall>s1 s2 s3.
          substate s1 s2 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          toEnvNum s1 s2 = Ctrl \<and>
          toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
          getVarBool s3 minimalRed = PRESSED))" 
and ei0: "toEnvP s0"
and ei1: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
 0<ltimeEnv s1 Ctrl \<and>  ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) " 
and ei2: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
 ((\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl  \<and>
 getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
 (\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed))) "
and ei3: "(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and>
 toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow> getPstate s1 Ctrl = minimalRed) "
and ei4: "\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed ) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl" 
and ei5: "\<forall> s1 . toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and>
 getVarBool s1 requestButtonPressed = False \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = minimalRed \<and> ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
getVarBool s2 requestButtonPressed = False \<and> (\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
 getPstate s3 Ctrl = redAfterMinimalRed \<and> 
getVarBool s3 requestButtonPressed = False \<and> getVarBool s3  requestButton = NOT_PRESSED))"
and ei6: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
0< ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) "
and ei7: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
(\<exists> s2. toEnvP s2  \<and> substate s2 s1 \<and>
 toEnvNum s2 s1 = ltimeEnv s1 Ctrl  \<and> getPstate s2 Ctrl = redAfterMinimalRed \<and> 
(getVarBool s2 requestButtonPressed = True \<or> getVarBool s2 requestButton = PRESSED)))"
and ei8: "(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and>
 getPstate s2 Ctrl = redToGreen \<longrightarrow> getPstate s1 Ctrl = redToGreen) "
and ei9: "(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) "
and ei10: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"
and ei11: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) "
and ei12: "(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = green \<and>
toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow> getPstate s1 Ctrl = green)"
and ei13: "(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> 
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) "
and ei14: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) "
and ei15: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 trafficLight = RED) "
and ei16: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
 getPstate s1 Ctrl = minimalRed \<or> getPstate s1 Ctrl = redAfterMinimalRed \<or>
 getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green)"
and ei17: "(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and>
 toEnvNum s1 s2 < ltimeEnv s2 Ctrl - 1 \<and>  getPstate s2 Ctrl = minimalRed \<and>
 getVarBool s2 requestButtonPressed = False \<longrightarrow> getVarBool s1 requestButton = NOT_PRESSED)"
and ei18: "(\<forall> s2. toEnvP s2  \<and> substate s2 s0  \<and>
 getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 requestButtonPressed = True \<longrightarrow>
(\<exists> s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - 1 \<and> getVarBool s1 requestButton = PRESSED))"
and ei19: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 requestButtonPressed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = 1 \<and> getPstate s2 Ctrl = minimalRed \<and>
 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
 (getVarBool s2 requestButtonPressed \<or> getVarBool s1 requestButton = PRESSED)))"
and ei20: "(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 requestButtonPressed = False)"
and vc: "env (setVarAny s0 requestButtonValue) requestButtonValue \<and>
    getPstate (setVarAny s0 requestButtonValue) Ctrl = minimalRed \<and>
    \<not> getVarBool (setVarAny s0 requestButtonValue) Ctrl \<and>
    \<not> MINIMAL_RED_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButtonValue) Ctrl"
    by fast
  show "  (toEnvP (toEnv (setVarAny s0 requestButtonValue)) \<and>
     (\<forall>s1 s2 s3.
         substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3 (toEnv (setVarAny s0 requestButtonValue)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and>
         toEnvNum s1 s2 = Ctrl \<and>
         toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
         getVarBool s3 minimalRed = PRESSED)) \<and>
    toEnvP (toEnv (setVarAny s0 requestButtonValue)) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = T2) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redAfterMinimalRed \<and>
                (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> T2) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s2. toEnvP s2 \<and>
          substate s2 (toEnv (setVarAny s0 requestButtonValue)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setVarAny s0 requestButtonValue)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
    apply(rule conjI)
     apply(rule conjI)
    apply(simp)
  proof(rule allI; rule allI; rule allI)
    fix s1 s2 s3
    show "substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3 (toEnv (setVarAny s0 requestButtonValue)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and>
         toEnvNum s1 s2 = Ctrl \<and>
         toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
         getVarBool s3 minimalRed = PRESSED"
    proof cases
      assume 1: "s3 = (toEnv (setVarAny s0 requestButtonValue))"
      from ei2 ei0 vc substate_refl have " ((\<exists> s2. toEnvP s2 \<and> substate s2 s0
 \<and> toEnvNum s2 s0 = ltimeEnv s0 Ctrl  \<and>
 getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
 (\<forall> s2. toEnvP s2 \<and> substate s2 s0 \<longrightarrow> getPstate s2 Ctrl = minimalRed))"
        by auto
      thus ?thesis
      proof
        assume "\<exists>s2. toEnvP s2 \<and>
         substate s2 s0 \<and> toEnvNum s2 s0 = ltimeEnv s0 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = T2"
        then obtain g where 2: "toEnvP g \<and>
         substate g s0 \<and> toEnvNum g s0 = ltimeEnv s0 Ctrl \<and> getPstate g Ctrl = green \<and> ltimeEnv g Ctrl = T2" ..
        show ?thesis
        proof cases
          assume 4: "substate s2 g" 
          from ei11 2 have "(\<exists> s2. toEnvP s2 \<and> substate s2 g \<and> toEnvNum s2 g = ltimeEnv g Ctrl \<and>
getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)" by blast
          then obtain rg where 3: " toEnvP rg \<and> substate rg g \<and> toEnvNum rg g = ltimeEnv g Ctrl \<and>
getPstate rg Ctrl = redToGreen \<and> ltimeEnv rg Ctrl = RED_TO_GREEN_TIME_LIMIT" ..
          show ?thesis
          proof cases
            assume 5: "substate s2 rg"
            from ei0 have "0 < ltimeEnv s0 Ctrl" by ((cases s0); auto)
            with 2 3 toEnvNum3[of rg g s0] substate_trans[of rg g s0] have 6: "toEnvNum rg s0 > T2"
              by auto
            from 2 3 substate_trans have "substate rg s0" by blast
            with 5 6 toEnvNum3[of s2 rg s0] substate_trans[of s2 rg s0] have "toEnvNum s2 s0 > T2"
              by auto
            with 1 show ?thesis by auto
          next
            assume 5: "\<not> (substate s2 rg)"
            with 3 4 substate_refl substate_total have 6: "substate rg s2 \<and> rg \<noteq> s2" by auto
            show ?thesis
            proof
              assume 7: "substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3  (toEnv (setVarAny s0 requestButtonValue)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and>
         toEnvNum s1 s2 = Ctrl \<and>
         toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
              show "getVarBool s3 minimalRed = PRESSED"
              proof cases
                assume 8: "substate s1 rg"
               from ei0 have "0 < ltimeEnv s0 Ctrl" by ((cases s0); auto)
            with 2 3 toEnvNum3[of rg g s0] substate_trans[of rg g s0] have 6: "toEnvNum rg s0 > T2"
              by auto
            from 2 3 substate_trans have "substate rg s0" by blast
            with 8 6 toEnvNum3 have 9: "toEnvNum s1 s0 > T2" by auto
            from 1 7 9 have 10: "substate s2 s0" by ((simp split: if_splits); auto)
            with 7 9 toEnvNum3 have "toEnvNum s2 s0 \<ge> T2" by auto
            with 1 10 substate_refl toEnvNum3[of s2 s0 s3] have "toEnvNum s2 s3 > T2" by auto
            with 7 show ?thesis by auto
          next 
            assume 8: "\<not> substate s1 rg"
            from 4 7 substate_trans have 9: "substate s1 g" by blast
            from 2 4 substate_trans have 10: "substate s2 s0" by blast
            with 1 7 substate_refl substate_asym[of s0 s3]  have "toEnvNum s2 s0 + 1 < T2" by ((simp split: if_splits); auto)
            with 7 10 toEnvNum3 have "toEnvNum s1 s0 < T2" by auto
            with 2 9 toEnvNum3 have "toEnvNum s1 g < ltimeEnv g Ctrl" by auto
            with 2 7 9 ei12 have "getPstate s1 Ctrl = green" by blast
            with ei14 7 show ?thesis using 2 9 substate_trans by blast
          qed
        qed
      qed
    next
      assume 4: "\<not> substate s2 g"
      show ?thesis
      proof
        assume 7: "substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3  (toEnv (setVarAny s0 requestButtonValue)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and>
         toEnvNum s1 s2 = Ctrl \<and>
         toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
        have "getVarBool s2 minimalRed =NOT_PRESSED"
        proof cases
          assume 3: "s2 = (toEnv (setVarAny s0 requestButtonValue))"
          from vc have "getPstate s0 Ctrl \<noteq> green" by auto
          with ei0 substate_refl ei15 have "getVarBool s0 trafficLight = RED" by blast
          with 3 show ?thesis by auto
        next 
          assume 3: "s2 \<noteq> (toEnv (setVarAny s0 requestButtonValue))"
          with 1 7 have 5: "substate s2 s0" by ((simp split: if_splits); auto)
          from 4 2 5 substate_total substate_refl have 6: "substate g s2 \<and> s2 \<noteq> g" by blast
          with 2 7 gtimeE_inj have 9: "toEnvNum emptyState g \<noteq> toEnvNum emptyState s2" by blast
           from 5 6 toEnvNum3 have "toEnvNum s2 s0 \<le> toEnvNum g s0" by auto
          from le_imp_less_or_eq[OF this]
          show ?thesis
          proof
            assume "toEnvNum s2 s0 < toEnvNum g s0"
            with 2 have 8: "toEnvNum s2 s0 < ltimeEnv s0 Ctrl" by auto
            from vc have "getPstate s0 Ctrl = minimalRed" by auto
            with ei3 7 ei0 5 substate_refl 8 have "getPstate s2 Ctrl = minimalRed" by blast
            with 5 7 ei15 show ?thesis by auto
          next 
            assume "toEnvNum s2 s0 = toEnvNum g s0"
            with 9 have 10: "toEnvNum emptyState g +toEnvNum g s0 \<noteq> toEnvNum emptyState s2 +toEnvNum s2 s0"
              by auto
            from emptyState_substate 5 toEnvNum3 have 11: "toEnvNum emptyState s0 = toEnvNum emptyState s2 + toEnvNum s2 s0"
              by auto 
            from emptyState_substate 5 6 substate_trans[of g s2 s0]  toEnvNum3 
            have  "toEnvNum emptyState s0 = toEnvNum emptyState g + toEnvNum g s0"
              by auto
            with 10 11 show ?thesis by auto
          qed
        qed
        with 7 show " getVarBool s3 minimalRed = PRESSED" by auto
      qed
    qed
  next
    assume 2: " \<forall>s2. toEnvP s2 \<and> substate s2 s0 \<longrightarrow> getPstate s2 Ctrl = minimalRed "
    show " \<forall>s2. toEnvP s2 \<and> substate s2 s0 \<longrightarrow> getPstate s2 Ctrl = minimalRed \<Longrightarrow>
    substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3
      (toEnv (setVarAny s0 requestButtonValue)) \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and>
    toEnvNum s1 s2 = Ctrl \<and>
    toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
    getVarBool s3 minimalRed = PRESSED"
    proof cases
       assume 3: "s2 =  (toEnv (setVarAny s0 requestButtonValue))"
       from vc have "getPstate s0 Ctrl \<noteq> green" by auto
          with ei0 substate_refl ei15 have "getVarBool s0 trafficLight = RED" by blast
          with 3 show ?thesis by auto
        next 
          assume 3: "s2 \<noteq>   (toEnv (setVarAny s0 requestButtonValue))"
          show ?thesis
          proof
            assume 7: "substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3
     (toEnv (setVarAny s0 requestButtonValue)) \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and>
    toEnvNum s1 s2 = Ctrl \<and>
    toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
            with 1  3 have "substate s2 s0" by ((simp split: if_splits); auto)
            with 2 7 ei15  show "  getVarBool s3 minimalRed = PRESSED" by auto
          qed
        qed
      qed
    next
      assume 1: " s3 \<noteq>
  (toEnv (setVarAny s0 requestButtonValue))"
      show ?thesis
      proof
        print_state
        assume 7: "substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3
    (toEnv (setVarAny s0 requestButtonValue)) \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and>
    toEnvNum s1 s2 = Ctrl \<and>
    toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
        with 1 have "substate s3 s0" by ((simp split: if_splits); auto)
        with 7 reqs0         show " getVarBool s3 minimalRed = PRESSED" by blast
      qed
    qed
  next
    (*prove extraInv*)
