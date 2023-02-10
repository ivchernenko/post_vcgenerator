theory Proof_2_8
  imports Requirements VCTheoryLemmas
begin

theorem proof_2_8: "VC8 inv2 s0 requestButtonValue"
  apply(simp only: VC8_def inv2_def  R2_def extraInv_def)
proof
  print_state
  assume "  ((toEnvP s0 \<and>
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
    getPstate (setVarAny s0 requestButtonValue) Ctrl = redToGreen \<and>
    RED_TO_GREEN_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButtonValue) Ctrl"
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
    getPstate (setVarAny s0 requestButtonValue) Ctrl = redToGreen \<and>
    RED_TO_GREEN_TIME_LIMIT \<le> ltimeEnv (setVarAny s0 requestButtonValue) Ctrl"
    by fast
  show " (toEnvP
      (toEnv
        (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl green)) \<and>
     (\<forall>s1 s2 s3.
         substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3
          (toEnv
            (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
              green)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and> toEnvNum s1 s2 = Ctrl \<and> toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
         getVarBool s3 minimalRed = PRESSED)) \<and>
    toEnvP
     (toEnv
       (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl green)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = T2) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
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
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = redAfterMinimalRed \<and> (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> T2) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
             green)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s2. toEnvP s2 \<and>
          substate s2
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)"
    apply(rule conjI)
     apply(rule conjI)
    apply(simp)
  proof(rule allI; rule allI; rule allI)
    fix s1 s2 s3
    show "substate s1 s2 \<and>
         substate s2 s3 \<and>
         substate s3  (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         toEnvP s3 \<and>
         toEnvNum s1 s2 = Ctrl \<and>
         toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED \<longrightarrow>
         getVarBool s3 minimalRed = PRESSED"
    proof cases
      assume 1: "s3 =  (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green))"
      then show ?thesis by auto
  next
    assume 1: "s3 \<noteq>  (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green))"
    show ?thesis
    proof
      assume req_prems: " substate s1 s2 \<and>
    substate s2 s3 \<and>
    substate s3  (toEnv
             (setPstate (setVarBool (setVarBool (setVarAny s0 requestButtonValue) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl
               green)) \<and>
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    toEnvP s3 \<and> toEnvNum s1 s2 = Ctrl \<and> toEnvNum s2 s3 < T2 \<and> getVarBool s1 minimalRed \<noteq> PRESSED \<and> getVarBool s2 minimalRed = PRESSED"
      with 1 have "substate s3 s0" by (simp split: if_splits)
      with req_prems reqs0
      show " getVarBool s3 minimalRed = PRESSED" by blast
    qed
  qed

