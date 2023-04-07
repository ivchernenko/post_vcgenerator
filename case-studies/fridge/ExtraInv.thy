theory ExtraInv
  imports Requirements
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init' = Init'begin' \<longrightarrow> toEnvNum emptyState s1 = 1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init' = STOP \<longrightarrow>
(\<exists> s2. toEnvP s1 \<and> substate s2 s1 \<and> getPstate s2 Init' = Init'begin' \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow> getPstate s3 Init' = STOP))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'closed' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
( (getPstate s2 Init' = Init'begin' \<or> getPstate s2 FridgeDoorController' = FridgeDoorController'open' \<or>
 getPstate s2 FridgeDoorController' = FridgeDoorController'longOpen') \<and>
getVarBool s3 fridgeDoor' = CLOSED') \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 FridgeDoorController' = FridgeDoorController'closed') \<and>
(\<forall> s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> getVarBool s5 fridgeDoor' = CLOSED'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow>
 ltime s1 FridgeDoorController' \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 toEnvNum s2 s1 = ltime s1 FridgeDoorController' \<and> getPstate s2 FridgeDoorController' = FridgeDoorController'closed' \<and>
getVarBool s3 fridgeDoor' = OPEN' )) \<and> 
(\<forall> s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 FridgeDoorController' = FridgeDoorController'open' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 FridgeDoorController' \<longrightarrow> 
getPstate s1 FridgeDoorController' = FridgeDoorController'open') \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 + 1 < ltime s3 FridgeDoorController' \<longrightarrow> getVarBool s2 fridgeDoor' \<noteq> CLOSED')) \<and>
(\<forall> s1 . toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = FridgeDoorController'longOpen' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> 
getPstate s2 FridgeDoorController' = FridgeDoorController'open' \<and> ltime s2 FridgeDoorController' = OPEN_DOOR_TIME_LIMIT' \<and> 
getVarBool s3 fridgeDoor' \<noteq> CLOSED' \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 FridgeDoorController' = FridgeDoorController'longOpen') \<and>
(\<forall>  s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> getVarBool s5 fridgeDoor' \<noteq> CLOSED'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeDoorController' = STOP \<longrightarrow>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> s2 \<noteq> s1 \<longrightarrow> getPstate s2 FridgeDoorController' = STOP \<and> getPstate s2 Init' \<noteq> Init'begin')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeCompressorController' = FridgeCompressorController'checkTemp' \<and>
getVarBool s1 fridgeCompressor' = True \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and>
 getPstate s2 FridgeCompressorController' =  FridgeCompressorController'checkTemp' \<and> getVarBool s3 fridgeTempGreaterMax' \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow>
 getPstate s4 FridgeCompressorController' = FridgeCompressorController'checkTemp' \<and> getVarBool s4 fridgeCompressor' = True) \<and>
(\<forall> s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> \<not> getVarBool s5 fridgeTempGreaterMax' \<and> 
 getVarBool s5 fridgeTempGreaterMin'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeCompressorController' = FridgeCompressorController'checkTemp' \<and>
getVarBool s1 fridgeCompressor' = False \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP  s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> (getPstate s2 Init' = Init'begin' \<or>
getPstate s2 FridgeCompressorController' = FridgeCompressorController'checkTemp'  \<and> \<not> getVarBool s3 fridgeTempGreaterMax') \<and>
\<not> getVarBool s3 fridgeTempGreaterMin' \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow>
 getPstate s4 FridgeCompressorController' = FridgeCompressorController'checkTemp' \<and> getVarBool s4 fridgeCompressor' = False) \<and>
(\<forall> s5.  toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow> \<not> getVarBool s5 fridgeTempGreaterMax' \<and> 
 getVarBool s5 fridgeTempGreaterMin'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 FridgeCompressorController' = STOP \<longrightarrow>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> s2 \<noteq> s1 \<longrightarrow> getPstate s2 FridgeCompressorController'  = STOP \<and>
 getPstate s2 Init' \<noteq> Init'begin')) \<and>
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
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 FridgeCompressorController' \<in> {FridgeCompressorController'checkTemp', STOP})" 

end