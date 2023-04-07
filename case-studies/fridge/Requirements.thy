theory Requirements
  imports Fridge
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 fridgeDoor' = CLOSED' \<and> getVarBool s2 fridgeDoor' = OPEN' \<longrightarrow> getVarBool s2 lighting')"

definition R2 where "R2 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 fridgeDoor' = OPEN' \<and> getVarBool s2 fridgeDoor' = CLOSED' \<longrightarrow> \<not> getVarBool s2 lighting')"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> toEnvNum s1 s \<ge> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>  getVarBool s1 fridgeDoor' = OPEN' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
(getVarBool s3 doorSignal' \<or> getVarBool s3 fridgeDoor' = CLOSED') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow>
 \<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN')))"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and> toEnvP s1 \<and> toEnvP s2 \<and>
 toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
getVarBool s1 fridgeDoor' = CLOSED' \<and> getVarBool s2 fridgeDoor' = OPEN' \<longrightarrow>
\<not> getVarBool s3 doorSignal')"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> 
getVarBool s1 fridgeCompressor' = False \<and> getVarBool s2 fridgeTempGreaterMax' \<longrightarrow> getVarBool s2 fridgeCompressor' = True)"

end