theory Extra1
  imports ExtraInv
begin



definition EI1 where "EI1 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
 0<ltimeEnv s1 Ctrl \<and>  ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT)"

definition EI2 where "EI2 s \<equiv> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
 ((\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl  \<and>
 getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
 (\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed)))"

definition EI3 where "EI3 s \<equiv> 
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and>
 toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow> getPstate s1 Ctrl = minimalRed)"

definition EI4 where "EI4 s \<equiv> 
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed ) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"

definition EI5 where "EI5 s \<equiv>
(\<forall> s1 . toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = minimalRed \<and> ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<and> s3 \<noteq> s1 \<longrightarrow>
 getPstate s3 Ctrl = redAfterMinimalRed \<and> 
getVarBool s3 requestButtonPressed = False \<and> getVarBool s3  requestButton = NOT_PRESSED)))"

definition EI6 where "EI6 s \<equiv> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
0< ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT)"

definition EI7 where "EI7 s \<equiv> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
(\<exists> s2. toEnvP s2  \<and> substate s2 s1 \<and>
 toEnvNum s2 s1 = ltimeEnv s1 Ctrl  \<and> getPstate s2 Ctrl = redAfterMinimalRed \<and> 
(getVarBool s2 requestButtonPressed = True \<or> getVarBool s2 requestButton = PRESSED)))"

definition EI8 where "EI8 s \<equiv>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and>
 getPstate s2 Ctrl = redToGreen \<longrightarrow> getPstate s1 Ctrl = redToGreen)"

definition EI9 where "EI9 s \<equiv>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"

definition EI10 where "EI10 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow>
0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT)"

definition EI11 where "EI11 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s2 Ctrl \<and>
getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT))"

definition EI12 where "EI12 s \<equiv>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = green \<and>
toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow> getPstate s1 Ctrl = green)"

definition EI13 where "EI13 s \<equiv>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> 
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl)"

definition EI14 where "EI14 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) "

definition EI15 where "EI15 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 trafficLight = RED)"

definition EI16 where "EI16 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 Ctrl = minimalRed \<or> getPstate s1 Ctrl = redAfterMinimalRed \<or>
 getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green)"

definition EI17 where "EI17 s \<equiv>
(\<forall> s1 s2 s3. toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and>
 toEnvNum s1 s2 < ltimeEnv s2 Ctrl - 1 \<and> toEnvNum s2 s3 = 1 \<and>  getPstate s2 Ctrl = minimalRed \<and>
 getVarBool s3 requestButtonPressed = False \<longrightarrow> getVarBool s1 requestButton = NOT_PRESSED)"

definition EI18 where "EI18 s \<equiv>
(\<forall> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvNum s2 s3 = 1 \<and>
 getPstate s2 Ctrl = minimalRed \<and> getVarBool s3 requestButtonPressed = True \<longrightarrow>
(\<exists> s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - 1 \<and> getVarBool s1 requestButton = PRESSED))"

definition EI19 where "EI19 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 requestButtonPressed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = 1 \<and> getPstate s2 Ctrl = minimalRed \<and>
 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT))"

definition EI20 where "EI20 s \<equiv>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 requestButtonPressed = False)"


theorem extra1: "VC1 extraInv s0"
  apply(simp only: VC1_def extraInv_def)
  by auto

end

