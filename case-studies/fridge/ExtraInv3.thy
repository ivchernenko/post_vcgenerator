theory ExtraInv3
  imports Requirements
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 FridgeDoorController' = FridgeDoorController'closed' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and> getVarBool s1 fridgeDoor' = OPEN' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
(getVarBool s3 doorSignal' \<or> getVarBool s3 fridgeDoor' = CLOSED') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> 
\<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN')))) \<and>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and> getVarBool s1 fridgeDoor' = OPEN' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
(getVarBool s3 doorSignal' \<or> getVarBool s3 fridgeDoor' = CLOSED') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> 
\<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN')) \<or>
toEnvNum s1 s4 < ltime s4 FridgeDoorController' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> \<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN'))) \<and>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 FridgeDoorController' = FridgeDoorController'longOpen' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and> getVarBool s1 fridgeDoor' = OPEN' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
(getVarBool s3 doorSignal' \<or> getVarBool s3 fridgeDoor' = CLOSED') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> 
\<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN')))) \<and>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 FridgeDoorController' = STOP \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and> getVarBool s1 fridgeDoor' = OPEN' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
(getVarBool s3 doorSignal' \<or> getVarBool s3 fridgeDoor' = CLOSED') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> 
\<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN')))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow>
 ltime s1 FridgeDoorController' \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'closed' \<longrightarrow>
\<not>getVarBool s1 lighting' \<and> \<not> getVarBool s1 doorSignal') \<and>
(\<forall>  s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow> 
getVarBool s1 lighting' \<and> \<not> getVarBool s1 doorSignal') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'longOpen' \<longrightarrow>
getVarBool s1 lighting' \<and> getVarBool s1 doorSignal') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = STOP \<longrightarrow>
\<not>getVarBool s1 lighting' \<and> \<not> getVarBool s1 doorSignal') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 Init' \<in> {Init'begin', STOP}) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 FridgeDoorController'  \<in>
 {FridgeDoorController'closed', FridgeDoorController'open', FridgeDoorController'longOpen', STOP}) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 FridgeCompressorController' \<in> {FridgeCompressorController'checkTemp', STOP}) \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s \<and>  getPstate s2 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s2  \<and>  toEnvNum s1 s2  < ltime s2 FridgeDoorController' \<longrightarrow>
 getVarBool s1 fridgeDoor' = OPEN')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init' = Init'begin' \<longrightarrow> toEnvNum emptyState s1 = 1)
"

end
