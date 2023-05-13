theory Requirements
  imports Thermopot
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
getVarBool s1 boilingMode' \<and> getVarInt s2 temperature' < BOILING_POINT' \<longrightarrow>
getVarBool s2 lid' = LOCKED')"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
getVarBool s1 maintainingMode' \<and> \<not> (getVarBool s2 boilingButton' = PRESSED') \<and> getVarInt s2 temperature' \<ge> getVarInt s2 selectedTemp' \<longrightarrow> getVarBool s2 heater' = False)"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
getVarBool s1 maintainingMode' \<and> \<not> getVarBool s2 boilingButton' = PRESSED' \<and> getVarInt s2 temperature' < getVarInt s2 selectedTemp' - 5 \<longrightarrow>
getVarBool s2 heater' = True)"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 button1' \<longrightarrow> getVarInt s1 selectedTemp' = TEMP1')"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> 
\<not> getVarBool s1 boilingMode' \<and> \<not> getVarBool s1 maintainingMode' \<longrightarrow> getVarBool s2 heater' = False)"

end