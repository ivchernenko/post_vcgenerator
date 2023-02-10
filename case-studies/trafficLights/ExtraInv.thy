theory ExtraInv
  imports trafficLights
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
 0<ltimeEnv s1 Ctrl \<and>  ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
 ((\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl  \<and>
 getPstate s2 Ctrl = green \<and> ltimeEnv s2 Ctrl = GREEN_TIME_LIMIT) \<or>
 (\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<longrightarrow> getPstate s2 Ctrl = minimalRed))) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and>
 toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow> getPstate s1 Ctrl = minimalRed) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = minimalRed ) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
(\<forall> s1 . toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and>
 getVarBool s1 requestButtonPressed = False \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = minimalRed \<and> ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
getVarBool s2 requestButtonPressed = False \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
 getPstate s3 Ctrl = redAfterMinimalRed \<and> 
getVarBool s3 requestButtonPressed = False \<and> getVarBool s3  requestButton = NOT_PRESSED))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
0< ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
(\<exists> s2. toEnvP s2  \<and> substate s2 s1 \<and>
 toEnvNum s2 s1 = ltimeEnv s1 Ctrl  \<and> getPstate s2 Ctrl = redAfterMinimalRed \<and> 
(getVarBool s2 requestButtonPressed = True \<or> getVarBool s2 requestButton = PRESSED))) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and>
 getPstate s2 Ctrl = redToGreen \<longrightarrow> getPstate s1 Ctrl = redToGreen) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = redToGreen) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow>
0 < ltimeEnv s1 Ctrl \<and> ltimeEnv s1 Ctrl \<le> GREEN_TIME_LIMIT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
getPstate s2 Ctrl = redToGreen \<and> ltimeEnv s2 Ctrl = RED_TO_GREEN_TIME_LIMIT)) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = green \<and>
toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow> getPstate s1 Ctrl = green) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> 
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s2 \<longrightarrow> getPstate s3 Ctrl = green) \<longrightarrow>
toEnvNum s1 s2 = ltimeEnv s2 Ctrl - ltimeEnv s1 Ctrl) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 trafficLight = RED) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 Ctrl = minimalRed \<or> getPstate s1 Ctrl = redAfterMinimalRed \<or>
 getPstate s1 Ctrl = redToGreen \<or> getPstate s1 Ctrl = green) \<and>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and>
 toEnvNum s1 s2 < ltimeEnv s2 Ctrl - 1 \<and>  getPstate s2 Ctrl = minimalRed \<and>
 getVarBool s2 requestButtonPressed = False \<longrightarrow> getVarBool s1 requestButton = NOT_PRESSED) \<and>
(\<forall> s2. toEnvP s2  \<and> substate s2 s  \<and>
 getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 requestButtonPressed = True \<longrightarrow>
(\<exists> s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl - 1 \<and> getVarBool s1 requestButton = PRESSED)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 requestButtonPressed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 = 1 \<and> getPstate s2 Ctrl = minimalRed \<and>
 ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
 (getVarBool s2 requestButtonPressed \<or> getVarBool s1 requestButton = PRESSED))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 requestButtonPressed = False)
"

end

