theory ExtraInv_new
  imports Requirements
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow> ltimeEnv s1 Ctrl \<le> MINIMAL_RED_TIME_LIMIT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow> ltimeEnv s1 Ctrl \<le> RED_TO_GREEN_TIME_LIMIT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 trafficLight = RED) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 Ctrl \<in> {minimalRed, redAfterMinimalRed, redToGreen, green}) \<and>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> getPstate s5 Ctrl \<noteq> green \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 trafficLight \<noteq> GREEN \<and> getVarBool s2 trafficLight = GREEN \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T2+T3 \<and> getVarBool s4 trafficLight = RED \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 trafficLight = GREEN)))) \<and>
(\<forall> s5. toEnvP s5 \<and> substate s5 s \<and> getPstate s5 Ctrl = green \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 trafficLight \<noteq> GREEN \<and> getVarBool s2 trafficLight = GREEN \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s5 \<and> toEnvNum s2 s4 \<le> T2+T3 \<and> getVarBool s4 trafficLight = RED \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 trafficLight = GREEN)) \<or>
toEnvNum s2 s5 < T3 + ltimeEnv s5 Ctrl \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s5 \<longrightarrow> getVarBool s3 trafficLight = GREEN) ))"

theorem extra_1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def)
  by auto

end