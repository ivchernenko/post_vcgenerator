theory Requirements
  imports Escalator
begin

definition R1 where "R1 s \<equiv> toEnvP s \<and>
 (\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
\<not> getVarBool s1 up' \<and> \<not> getVarBool s1 down' \<and> getVarBool s2 userAtTop' \<and> getVarBool s2 directionSwitch' = UP' \<and> 
\<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<longrightarrow>
getVarBool s2 up' = True)"

definition R2 where "R2 s\<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> DELAY'TIMEOUT \<and>
(getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<and> \<not> getVarBool s2 userAtTop' \<and> \<not> getVarBool s2 userAtBottom' \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
(getVarBool s4 up' = False \<and> getVarBool s4 down' = False \<or> getVarBool s4 userAtTop' \<or> getVarBool s4 userAtBottom') \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
(getVarBool s3 up' = True \<or> getVarBool s3 down' = True) \<and> \<not> getVarBool s3 userAtTop' \<and> \<not> getVarBool s3 userAtBottom')))"

definition R3 where "R3 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
getVarBool s1 up' = True \<and> (getVarBool s2 userAtTop' \<or>  getVarBool s2 userAtBottom') \<and>
 \<not> getVarBool s1 alarmButton' \<and> \<not> getVarBool s1 stuck' \<and> \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<longrightarrow>
getVarBool s2 up' = True)"

definition R4 where "R4 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2 s3. toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and>
toEnvNum s1 s2 = 1 \<and> 1 \<le> toEnvNum s2 s3 \<and> toEnvNum s2 s3 < SUSPENSION_TIME'TIMEOUT \<and>
(getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<and> getVarBool s2 stuck' \<longrightarrow>
getVarBool s3 up' = False \<and> getVarBool s3 down' = False)"

definition R5 where "R5 s \<equiv> toEnvP s \<and>
(\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> 1 \<and>
(getVarBool s1 up' = True \<or> getVarBool s1 down' = True) \<and> getVarBool s2 alarmButton' \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> 1 \<and>
getVarBool s4 up' = False \<and> getVarBool s4 down' = False \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
getVarBool s3 up' = True \<or> getVarBool s3 down' = True)))"

definition env where "env s \<equiv> True"

end