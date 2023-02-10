theory Proof_2_6
  imports Requirements VCTheoryLemmas
begin

theorem proof_2_6: "VC6 inv2 s0 requestButtonValue"
  apply(simp only: VC6_def inv2_def  R2_def extraInv_def)
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
          toEnvNum s1 s2 = Ctrl \<and> toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
          getVarBool s3 minimalRed = PRESSED)) \<and>
     toEnvP s0 \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow> 0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = T2) \<or>
           (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
     (\<forall>s1 s2.
         toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
         getPstate s1 Ctrl = minimalRed) \<and>
     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and> substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
         toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
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
                 getPstate s2 Ctrl = redAfterMinimalRed \<and> (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
     (\<forall>s1 s2.
         toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
         getPstate s1 Ctrl = redToGreen) \<and>
     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and> substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
         toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> 0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> T2) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
     (\<forall>s1 s2.
         toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
         getPstate s1 Ctrl = green) \<and>
     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
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
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
         getVarBool s1 Ctrl = NOT_PRESSED) \<and>
     (\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
           (\<exists>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = Ctrl \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 redAfterMinimalRed = NOT_PRESSED)) \<and>
    env (setVarAny s0 requestButtonValue) requestButtonValue \<and>
    getPstate (setVarAny s0 requestButtonValue) Ctrl = redAfterMinimalRed \<and>
    (getVarBool (setVarAny s0 requestButtonValue) redAfterMinimalRed \<or> getVarBool (setVarAny s0 requestButtonValue) Ctrl)"
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
    getPstate (setVarAny s0 requestButtonValue) Ctrl = redAfterMinimalRed \<and>
    (getVarBool (setVarAny s0 requestButtonValue) redAfterMinimalRed \<or> getVarBool (setVarAny s0 requestButtonValue) Ctrl)"
    by fast
  show " (toEnvP (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
     (\<forall>s1 s2 s3.
         substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and> toEnvNum s1 s2 = Ctrl \<and> toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
         getVarBool s3 minimalRed = PRESSED)) \<and>
    toEnvP (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = T2) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redAfterMinimalRed \<and> (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> T2) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s2. toEnvP s2 \<and>
          substate s2 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and> getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
    apply(rule conjI)
     apply(rule conjI)
    apply(simp)
  proof(rule allI; rule allI; rule allI)
    fix s1 s2 s3
    show "substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and>
         toEnvNum s1 s2 = Ctrl \<and>
         toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
         getVarBool s3 minimalRed = PRESSED"
    proof cases
      assume 1: "s3 = (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen))"
      show ?thesis
      proof
        print_state
        assume req_prems: "substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and> toEnvNum s1 s2 = Ctrl \<and> toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
        show "getVarBool s3 trafficLight = GREEN"
        proof cases
        assume 2: "getVarBool s0 requestButtonPressed"
        from ei0 substate_refl vc 2 ei19
        have " (\<exists>s2. toEnvP s2 \<and>
           substate s2 s0 \<and>
           toEnvNum s2 s0 = 1 \<and>
           getPstate s2 Ctrl = minimalRed \<and>
           ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool s2 requestButtonPressed \<or> getVarBool s0 requestButton = PRESSED))"
          by auto
        then obtain mr where 3: "toEnvP mr \<and> substate mr s0 \<and>
           toEnvNum mr s0 = 1 \<and>
           getPstate mr Ctrl = minimalRed \<and>
           ltimeEnv mr Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool mr requestButtonPressed \<or> getVarBool s0 requestButton = PRESSED)" ..
        show ?thesis
        proof cases
          assume 4: "substate s2 mr" 
          from 3 ei2 have "((\<exists> s2. toEnvP s2 \<and> substate s2 mr \<and> toEnvNum s2 mr = MINIMAL_RED_TIME_LIMIT  \<and>
 getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
 (\<forall> s2. toEnvP s2 \<and> substate s2 mr \<longrightarrow> getPstate s2 Ctrl = minimalRed))" by auto
          then show ?thesis
          proof
            assume " \<exists>s2. toEnvP s2 \<and> substate s2 mr \<and> toEnvNum s2 mr = MINIMAL_RED_TIME_LIMIT \<and> getPstate s2 Ctrl = green \<and>
 ltimeEnv s2 Ctrl = T2"
            then obtain g where 5: "toEnvP g \<and> substate g mr \<and> toEnvNum g mr = MINIMAL_RED_TIME_LIMIT \<and> getPstate g Ctrl = green \<and>
 ltimeEnv g Ctrl = T2" ..
            show ?thesis
            proof cases
              assume 6: "substate s2 g"
              with 5 toEnvNum3[of s2 g mr] req_prems have 7: "toEnvNum s2 mr \<ge> MINIMAL_RED_TIME_LIMIT" by auto
              from 6 5 substate_trans have "substate s2 mr" by blast
              with 3 7 toEnvNum3 req_prems have "toEnvNum s2 s0 > MINIMAL_RED_TIME_LIMIT" by auto
              with 1 req_prems show ?thesis by ((simp split: if_splits); auto)
            next
              assume 6: "\<not> substate s2 g"
              with 4 5 substate_total substate_asym have 7:  "substate g s2 \<and> g \<noteq> s2" by auto
              with req_prems 5 gtimeE_inj have "toEnvNum emptyState g \<noteq> toEnvNum  emptyState s2" by blast
              with 7 toEnvNum3[of emptyState g s2] emptyState_substate  have "toEnvNum g s2 > 0" by auto
              with 4 5 7  toEnvNum3 have "toEnvNum s2 mr < MINIMAL_RED_TIME_LIMIT" by auto
              with 4 3 req_prems ei3 have "getPstate s2 Ctrl = minimalRed" by force
              with ei15 req_prems show ?thesis
                by (metis "1" numeral_eq_iff substate.simps(2) substate.simps(6) substate.simps(7) toEnvP.simps(6) toEnvP.simps(7) verit_eq_simplify(14))
            qed
          next
            assume 5: "\<forall>s2. toEnvP s2 \<and> substate s2 mr \<longrightarrow> getPstate s2 Ctrl = minimalRed"
            with 4 req_prems show ?thesis by (metis "3" ei15 numeral_eq_iff semiring_norm(89) substate_trans)
          qed
        next
          assume 4: "\<not> substate s2 mr"
          show ?thesis
          proof cases
            assume "s2 =  toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)"
            with 1 req_prems show ?thesis by auto
          next
            assume "s2 \<noteq>  toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)"
            with req_prems 1 have 5: "substate s2 s0"  by (simp  split: if_splits)
            with 3 4 substate_total substate_asym have 6: "substate mr s2 \<and> mr \<noteq> s2" by auto
            from 5 emptyState_substate toEnvNum3  have 7: "toEnvNum emptyState s2 \<le> toEnvNum emptyState s0" by auto
            from 3 6 req_prems gtimeE_inj have "toEnvNum emptyState mr \<noteq> toEnvNum emptyState s2" by blast
            with 6 emptyState_substate toEnvNum3 have 8: "toEnvNum emptyState mr < toEnvNum emptyState s2" by auto
            from 3 emptyState_substate toEnvNum3 have "toEnvNum emptyState s0 = toEnvNum emptyState mr + 1" by auto
            with 8 have "toEnvNum emptyState s2 \<ge> toEnvNum emptyState s0" by auto
            with 7 have "toEnvNum emptyState s2 = toEnvNum emptyState s0" by auto
            with 5 req_prems ei0 gtimeE_inj have "s2 = s0" by blast
            with vc req_prems ei15 show ?thesis
              using "2" "5" ei20 by blast
          qed
        qed
      next
        assume 2: "\<not> getVarBool s0 requestButtonPressed"
        with vc ei0 ei5 substate_refl have "\<exists>s2. toEnvP s2 \<and>
           substate s2 s0 \<and>
           getPstate s2 Ctrl = minimalRed \<and>
           ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
           getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
           (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s0 \<and> s2 \<noteq> s3 \<longrightarrow>
                 getPstate s3 Ctrl = redAfterMinimalRed \<and> getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)"
          by auto
        then obtain mr where 3: "toEnvP mr \<and>
           substate mr s0 \<and>
           getPstate mr Ctrl = minimalRed \<and>
           ltimeEnv mr Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
           getVarBool mr redAfterMinimalRed = NOT_PRESSED \<and>
           (\<forall>s3. toEnvP s3 \<and> substate mr s3 \<and> substate s3 s0 \<and> mr \<noteq> s3 \<longrightarrow>
                 getPstate s3 Ctrl = redAfterMinimalRed \<and> getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and>
 getVarBool s3 Ctrl = NOT_PRESSED)" ..
        show ?thesis
        proof cases
           assume 4: "substate s2 mr" 
          from 3 ei2 have "((\<exists> s2. toEnvP s2 \<and> substate s2 mr \<and> toEnvNum s2 mr = MINIMAL_RED_TIME_LIMIT  \<and>
 getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
 (\<forall> s2. toEnvP s2 \<and> substate s2 mr \<longrightarrow> getPstate s2 Ctrl = minimalRed))" by auto
          then show ?thesis
          proof
            assume " \<exists>s2. toEnvP s2 \<and> substate s2 mr \<and> toEnvNum s2 mr = MINIMAL_RED_TIME_LIMIT \<and> getPstate s2 Ctrl = green \<and>
 ltimeEnv s2 Ctrl = T2"
            then obtain g where 5: "toEnvP g \<and> substate g mr \<and> toEnvNum g mr = MINIMAL_RED_TIME_LIMIT \<and> getPstate g Ctrl = green \<and>
 ltimeEnv g Ctrl = T2" ..
            show ?thesis
            proof cases
              assume 6: "substate s2 g"
              with 5 toEnvNum3[of s2 g mr] req_prems have 7: "toEnvNum s2 mr \<ge> MINIMAL_RED_TIME_LIMIT" by auto
              from 6 5 substate_trans have 8: "substate s2 mr" by blast
              from vc 3 have "mr \<noteq> s0" by auto
              with 3 ei0 gtimeE_inj have "toEnvNum emptyState mr \<noteq> toEnvNum emptyState s0" by auto
              with 3 emptyState_substate toEnvNum3 have "toEnvNum emptyState mr < toEnvNum emptyState s0" by auto
              with 3 7 8  toEnvNum3 req_prems have "toEnvNum s2 s0 > MINIMAL_RED_TIME_LIMIT"
                using emptyState_substate by auto
              with 1 req_prems show ?thesis by ((simp split: if_splits); auto)
            next
              assume 6: "\<not> substate s2 g"
              with 4 5 substate_total substate_asym have 7:  "substate g s2 \<and> g \<noteq> s2" by auto
              with req_prems 5 gtimeE_inj have "toEnvNum emptyState g \<noteq> toEnvNum  emptyState s2" by blast
              with 7 toEnvNum3[of emptyState g s2] emptyState_substate  have "toEnvNum g s2 > 0" by auto
              with 4 5 7  toEnvNum3 have "toEnvNum s2 mr < MINIMAL_RED_TIME_LIMIT" by auto
              with 4 3 req_prems ei3 have "getPstate s2 Ctrl = minimalRed" by force
              with ei15 req_prems show ?thesis
                by (metis "1" numeral_eq_iff substate.simps(2) substate.simps(6) substate.simps(7) toEnvP.simps(6) toEnvP.simps(7) verit_eq_simplify(14))
            qed
          next
            assume 5: "\<forall>s2. toEnvP s2 \<and> substate s2 mr \<longrightarrow> getPstate s2 Ctrl = minimalRed"
            with 4 req_prems show ?thesis by (metis "3" ei15 numeral_eq_iff semiring_norm(89) substate_trans)
          qed
        next
          assume 4: "\<not> substate s2 mr"
          show ?thesis
          proof cases
            assume "s2 =  toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)"
            with 1 req_prems show ?thesis by auto
          next
            assume "s2 \<noteq>  toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)"
            with req_prems 1 have 5: "substate s2 s0"  by (simp  split: if_splits)
            with 4 req_prems 3 substate_total substate_asym have "substate mr s2 \<and> mr \<noteq> s2" by blast
            with 3 5 req_prems have "getPstate s2 Ctrl = redAfterMinimalRed" by auto
            with ei15 req_prems show ?thesis
              using "5" by auto
          qed
        qed
      qed
    qed
  next
    assume 1: "s3 \<noteq> toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)"
    show ?thesis
    proof
      assume req_prems: " substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3 (toEnv (setPstate (setVarAny s0 requestButtonValue) Ctrl redToGreen)) \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and> toEnvNum s1 s2 = Ctrl \<and> toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
      with 1 have "substate s3 s0" by (simp split: if_splits)
      with req_prems reqs0
      show " getVarBool s3 minimalRed = PRESSED" by blast
    qed
  qed

