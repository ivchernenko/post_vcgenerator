theory Requirements
  imports ExtraInv
begin

abbreviation T1:: nat where
 "T1 \<equiv> MINIMAL_RED_TIME_LIMIT + RED_TO_GREEN_TIME_LIMIT"
abbreviation T2:: nat where "T2 \<equiv> GREEN_TIME_LIMIT"
abbreviation T3:: nat where "T3 \<equiv> 10"

definition R1 where "R1 s \<equiv> toEnvP s \<and> 
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> 
toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
toEnvNum s2 s \<ge> T1 \<and>
 getVarBool s1 trafficLight = RED \<and>
getVarBool s1 requestButton = NOT_PRESSED \<and>
getVarBool s2 requestButton = PRESSED \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s\<and>
toEnvNum s2 s4 \<le> T1 \<and>
getVarBool s4 trafficLight = GREEN \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4\<and>
s3 \<noteq> s4 \<longrightarrow>
getVarBool s3 trafficLight = RED)))"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and>
substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3\<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < T2 \<and>
getVarBool s1 trafficLight \<noteq> GREEN \<and>
getVarBool s2 trafficLight = GREEN \<longrightarrow>
getVarBool s3 trafficLight = GREEN)"

definition R3 where "R3 s \<equiv> toEnvP s \<and> 
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> 
toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
toEnvNum s2 s \<ge> T2+T3 \<and>
 getVarBool s1 trafficLight \<noteq> GREEN \<and>
getVarBool s2 trafficLight = GREEN \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s\<and>
toEnvNum s2 s4 \<le> T2+T3 \<and>
getVarBool s4 trafficLight = RED \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4\<and>
s3 \<noteq> s4 \<longrightarrow>
getVarBool s3 trafficLight = GREEN)))"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and>
substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3\<and>
toEnvNum s1 s2 = 1 \<and> 
getVarBool s1 trafficLight \<noteq> RED \<and>
getVarBool s2 trafficLight = RED \<and>
(\<forall> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s
 \<longrightarrow> getVarBool s4 requestButton = NOT_PRESSED) \<longrightarrow>
getVarBool s3 trafficLight = RED)"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and>
substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3\<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < T1 \<and>
getVarBool s1 trafficLight \<noteq> RED \<and>
getVarBool s2 trafficLight = RED \<longrightarrow>
getVarBool s3 trafficLight = RED)"

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"
definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"
definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"
definition inv4 where "inv4 s \<equiv> R4 s \<and> extraInv s"
definition inv5 where "inv5 s \<equiv> R5 s \<and> extraInv s"

end