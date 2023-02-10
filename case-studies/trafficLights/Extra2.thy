theory Extra2
  imports ExtraInv VCTheoryLemmas
begin

theorem extra2: "VC2 extraInv s0 requestButton_value"
  apply(simp only: VC2_def extraInv_def)
proof
  print_state
  assume VC: " (toEnvP s0 \<and>
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
    MINIMAL_RED_TIME_LIMIT
    \<le> ltimeEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl "
  then obtain ei0: "toEnvP s0" and 
 ei1: " (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = minimalRed \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and>
           ltimeEnv s1 Ctrl
           \<le> MINIMAL_RED_TIME_LIMIT)" 
 and ei2: "     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = minimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                 getPstate s2 Ctrl = green \<and>
                 ltimeEnv s2 Ctrl =
                 GREEN_TIME_LIMIT) \<or>
           (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow>
                 getPstate s2 Ctrl = minimalRed))"
and ei3:"    (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         getPstate s2 Ctrl = minimalRed \<and>
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
         getPstate s1 Ctrl = minimalRed)"
 and ei4: "     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate s1 s3 \<and> substate s3 s2 \<longrightarrow>
               getPstate s3 Ctrl = minimalRed) \<longrightarrow>
         toEnvNum s1 s2 =
         ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
 and ei5: " (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                 (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                       getPstate s3 Ctrl = redAfterMinimalRed \<and>
                       getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)))" and ei6:
"     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = redToGreen \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and>
           ltimeEnv s1 Ctrl
           \<le> RED_TO_GREEN_TIME_LIMIT)" 
and ei7: "     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = redToGreen \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                 getPstate s2 Ctrl =
                 redAfterMinimalRed \<and>
                 (getVarBool s2 redAfterMinimalRed =
                  PRESSED \<or>
                  getVarBool s2 Ctrl = PRESSED)))"
and ei8: "     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and>
         getPstate s2 Ctrl = redToGreen \<longrightarrow>
         getPstate s1 Ctrl = redToGreen)"
    and ei9: "     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate s1 s3 \<and> substate s3 s2 \<longrightarrow>
               getPstate s3 Ctrl = redToGreen) \<longrightarrow>
         toEnvNum s1 s2 =
         ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
 and ei10:
"     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = green \<longrightarrow>
           0 < ltimeEnv s1 Ctrl \<and>
           ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"
     and ei11: "     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = green \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                 getPstate s2 Ctrl = redToGreen \<and>
                 ltimeEnv s2 Ctrl =
                 RED_TO_GREEN_TIME_LIMIT))"
  and ei12: "     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         getPstate s2 Ctrl = green \<and>
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
         getPstate s1 Ctrl = green)" and ei13:
"     (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate s1 s3 \<and> substate s3 s2 \<longrightarrow>
               getPstate s3 Ctrl = green) \<longrightarrow>
         toEnvNum s1 s2 =
         ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
and ei14: "     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = green \<longrightarrow>
           getVarBool s1 minimalRed = PRESSED)" and
ei15: "     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl \<noteq> green \<longrightarrow>
           getVarBool s1 minimalRed = NOT_PRESSED)"
and ei16: "     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
           getPstate s1 Ctrl = minimalRed \<or>
           getPstate s1 Ctrl = redAfterMinimalRed \<or>
           getPstate s1 Ctrl = redToGreen \<or>
           getPstate s1 Ctrl = green)" and 
ei17: " (\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2 s0 \<and>
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
         getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
         getVarBool s1 Ctrl = NOT_PRESSED)" and
ei18: "     (\<forall>s2. toEnvP s2 \<and> substate s2 s0 \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
           (\<exists>s1. toEnvP s1 \<and>
                 substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED))" and
ei19: "     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = Ctrl \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)))"
 and ei20:
"     (\<forall>s1. toEnvP s1 \<and>
           substate s1 s0 \<and>
           getPstate s1 Ctrl = green \<longrightarrow>
           getVarBool s1 redAfterMinimalRed =
           NOT_PRESSED)"
and vc: " env (setVarAny s0 requestButton_value)
     requestButton_value \<and>
    getPstate (setVarAny s0 requestButton_value)
     Ctrl =
    minimalRed \<and>
    getVarBool (setVarAny s0 requestButton_value)
     Ctrl \<and>
    MINIMAL_RED_TIME_LIMIT
    \<le> ltimeEnv
        (setVarBool
          (setVarAny s0 requestButton_value)
          redAfterMinimalRed PRESSED)
        Ctrl "
    by fastforce
   have "toEnvP
     (toEnv
       (setPstate
         (setVarBool
           (setVarAny s0 requestButton_value)
           redAfterMinimalRed PRESSED)
         Ctrl redAfterMinimalRed))" by auto
  moreover from ei1   have "  (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and>
          ltimeEnv s1 Ctrl
          \<le> MINIMAL_RED_TIME_LIMIT)"
    by auto
  moreover from ei2 have " (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl = green \<and>
                ltimeEnv s2 Ctrl =
                GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow>
                getPstate s2 Ctrl = minimalRed))"
    by auto
  moreover from ei3 have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = minimalRed \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed)"
    by auto
  moreover from ei4 have " (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and>
              substate s1 s3 \<and> substate s3 s2 \<longrightarrow>
              getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 =
        ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
    by auto
  moreover  from ei5 have "  (\<forall>s1. toEnvP s1 \<and>
           substate s1 (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed))
 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                 (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                       getPstate s3 Ctrl = redAfterMinimalRed \<and>
                       getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)))"
    by auto
   moreover from ei6  have "(\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and>
          ltimeEnv s1 Ctrl
          \<le> RED_TO_GREEN_TIME_LIMIT)"
     by auto
   moreover from ei7 have "(\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                getPstate s2 Ctrl =
                redAfterMinimalRed \<and>
                (getVarBool s2 redAfterMinimalRed =
                 PRESSED \<or>
                 getVarBool s2 Ctrl = PRESSED)))"
     by auto
   moreover from ei8 have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and>
        getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen)"
     by auto
   moreover from ei9 have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and>
              substate s1 s3 \<and> substate s3 s2 \<longrightarrow>
              getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 =
        ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
     by auto
   moreover from ei10 have " (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and>
          ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"
     by auto
   moreover from ei11 have " \<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and>
                ltimeEnv s2 Ctrl =
                RED_TO_GREEN_TIME_LIMIT)"
     by auto
   moreover from ei12 have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = green \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green)"
     by auto
   moreover from ei13 have "(\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool
               (setVarAny s0 requestButton_value)
               redAfterMinimalRed PRESSED)
             Ctrl redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and>
              substate s1 s3 \<and> substate s3 s2 \<longrightarrow>
              getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 =
        ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"
     by auto
   moreover from ei14 have " (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED)"
     by auto
   moreover from ei0 ei15 vc substate_refl have "(\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED)" by auto
   moreover from ei16 have "(\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or>
          getPstate s1 Ctrl = redToGreen \<or>
          getPstate s1 Ctrl = green)"
     by auto
   moreover from ei17 have "(\<forall>s1 s2.
         toEnvP s1 \<and>
         toEnvP s2 \<and>
         substate s1 s2 \<and>
         substate s2  (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
         toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
         getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
         getVarBool s1 Ctrl = NOT_PRESSED)"
     by auto
   moreover from ei18  have " (\<forall>s2. toEnvP s2 \<and> substate s2
 (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed))
 \<and> getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
           (\<exists>s1. toEnvP s1 \<and>
                 substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED))"
     by auto
   moreover have " (\<forall>s1. toEnvP s1 \<and> substate s1  (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed))
 \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
           (\<exists>s2. toEnvP s2 \<and>
                 substate s2 s1 \<and>
                 toEnvNum s2 s1 = Ctrl \<and>
                 getPstate s2 Ctrl = minimalRed \<and>
                 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)))"
   proof -
     from ei0 ei1  vc substate_refl toEnvNum_id  have 1: "( toEnvP s0 \<and>
                 substate s0 (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed)) \<and>
                 toEnvNum s0 (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed))
 = Ctrl \<and>
                 getPstate s0 Ctrl = minimalRed \<and>
                 ltimeEnv s0 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                 (getVarBool s0 redAfterMinimalRed \<or> getVarBool (toEnv
             (setPstate
               (setVarBool
                 (setVarAny s0 requestButton_value)
                 redAfterMinimalRed PRESSED)
               Ctrl redAfterMinimalRed))
 Ctrl = PRESSED))" 
       by auto
     show ?thesis
     proof
       fix s1
       show " toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))"
       proof cases
         assume 2: "s1 = (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed))"
          show ?thesis 
          proof
            from 1 2  show "\<exists>s2. toEnvP s2 \<and>
         substate s2 s1 \<and>
         toEnvNum s2 s1 = Ctrl \<and>
         getPstate s2 Ctrl = minimalRed \<and>
         ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED)"
              by blast
          qed
        next
assume 2: "s1 \<noteq> (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed))"
  with ei19 show ?thesis by auto
qed
qed
qed
  moreover from ei20 have "(\<forall>s1. toEnvP s1 \<and>
           substate s1  (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
           getPstate s1 Ctrl = green \<longrightarrow>
           getVarBool s1 redAfterMinimalRed =
           NOT_PRESSED)"
    by auto
  ultimately  show "toEnvP
     (toEnv
       (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
         redAfterMinimalRed)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and> getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = minimalRed) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
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
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redToGreen \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
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
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
        getPstate s1 Ctrl = redToGreen) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
                getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        getPstate s2 Ctrl = green \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
        getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        (\<forall>s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
        toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 minimalRed = PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl \<noteq> green \<longrightarrow>
          getVarBool s1 minimalRed = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<longrightarrow>
          getPstate s1 Ctrl = minimalRed \<or>
          getPstate s1 Ctrl = redAfterMinimalRed \<or> getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
             redAfterMinimalRed)) \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s2. toEnvP s2 \<and>
          substate s2
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = PRESSED \<longrightarrow>
          (\<exists>s1. toEnvP s1 \<and>
                substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and> getVarBool s1 Ctrl = PRESSED)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                toEnvNum s2 s1 = Ctrl \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1
           (toEnv
             (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl
               redAfterMinimalRed)) \<and>
          getPstate s1 Ctrl = green \<longrightarrow>
          getVarBool s1 redAfterMinimalRed = NOT_PRESSED)" by blast
qed