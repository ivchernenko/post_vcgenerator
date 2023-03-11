theory ExtraInv
  imports Escalator
begin

definition extraInv where " extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'motionless \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
((getPstate s2 Ctrl' = Ctrl'goUp \<or> getPstate s2 Ctrl' = Ctrl'goDown) \<and> ltime s2 Ctrl' = DELAY'TIMEOUT \<and>
 \<not> (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or> 
getPstate s2 Ctrl' = Ctrl'stuckState \<and> ltime s2 Ctrl' = SUSPENSION_TIME'TIMEOUT \<and>  \<not> getVarBool s2 moving') \<and> \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3  stuck' \<and>
(\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = 1 \<longrightarrow>
getPstate s4 Ctrl' = Ctrl'motionless \<and> \<not> getVarBool s5 alarmButton' \<and> \<not> getVarBool s5 stuck' \<and>
\<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<or>
(\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and>  substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = 1 \<longrightarrow>
getPstate s4 Ctrl' = Ctrl'motionless \<and> \<not> getVarBool s5 alarmButton' \<and> \<not> getVarBool s5 stuck' \<and>
\<not> (getVarBool s5 userAtTop' \<or> getVarBool s5 userAtBottom'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s\<and> getPstate s1 Ctrl' = Ctrl'goUp \<longrightarrow> ltime s1 Ctrl' \<le> DELAY'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'goUp \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> toEnvNum s2 s1 = ltime s1 Ctrl' \<and>
((getPstate s2 Ctrl' = Ctrl'motionless \<or> getPstate s2 Ctrl' = Ctrl'goUp) \<and>
(getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or> 
getPstate s2 Ctrl' = Ctrl'stuckState \<and> ltime s2 Ctrl' = SUSPENSION_TIME'TIMEOUT \<and>  getVarBool s2 moving' \<and>
 getVarBool s2 direction' = UP') \<and>
 \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3  stuck')) \<and>
(\<forall> s3. toEnvP s3 \<and>  substate s3 s \<and>
 getPstate s3 Ctrl' = Ctrl'goUp \<longrightarrow> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Ctrl'  \<longrightarrow>  getPstate s1 Ctrl' = Ctrl'goUp) \<and>
 (\<forall> s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 Ctrl' - 1 \<longrightarrow> 
\<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and>
\<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s\<and> getPstate s1 Ctrl' = Ctrl'goDown \<longrightarrow> ltime s1 Ctrl' \<le> DELAY'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'goDown \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> toEnvNum s2 s1 = ltime s1 Ctrl' \<and>
((getPstate s2 Ctrl' = Ctrl'motionless \<or> getPstate s2 Ctrl' = Ctrl'goDown) \<and>
 (getVarBool s3 userAtTop' \<or> getVarBool s3 userAtBottom') \<or> 
getPstate s2 Ctrl' = Ctrl'stuckState \<and> ltime s2 Ctrl' = SUSPENSION_TIME'TIMEOUT \<and>  getVarBool s2 moving' \<and>
 getVarBool s2 direction' = DOWN') \<and>
 \<not> getVarBool s3 alarmButton' \<and> \<not> getVarBool s3  stuck')) \<and>
(\<forall> s3.  toEnvP s3 \<and>  substate s3 s  \<and> getPstate s3 Ctrl' = Ctrl'goDown \<longrightarrow> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Ctrl'  \<longrightarrow> getPstate s1 Ctrl' = Ctrl'goDown) \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 Ctrl' - 1 \<longrightarrow>
 \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and>
\<not> (getVarBool s2 userAtTop' \<or> getVarBool s2 userAtBottom'))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'stuckState \<longrightarrow> ltime s1 Ctrl' \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = UP' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>toEnvNum s2 s1 = ltime s1 Ctrl' \<and>
(getPstate s2 Ctrl' = Ctrl'goUp \<or> getPstate s2 Ctrl' = Ctrl'stuckState \<and> getVarBool s2 moving' \<and> getVarBool s2 direction' = UP')
 \<and> \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'stuckState \<and> getVarBool s1 moving' \<and> getVarBool s1 direction' = DOWN' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>toEnvNum s2 s1 = ltime s1 Ctrl' \<and>
(getPstate s2 Ctrl' = Ctrl'goDown \<or> getPstate s2 Ctrl' = Ctrl'stuckState \<and> getVarBool s2 moving' \<and>
 getVarBool s2 direction' = DOWN') \<and> \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck')) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'stuckState \<and> \<not> getVarBool s1 moving' \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>toEnvNum s2 s1 = ltime s1 Ctrl' \<and>
(getPstate s2 Ctrl' = Ctrl'motionless \<or> getPstate s2 Ctrl' = Ctrl'stuckState \<and> \<not> getVarBool s2 moving') \<and> \<not> getVarBool s3 alarmButton' \<and> getVarBool s3 stuck'))\<and>
(\<forall> s3. toEnvP s3 \<and> substate s3 s \<and>  getPstate s3 Ctrl' = Ctrl'stuckState \<longrightarrow> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Ctrl' \<longrightarrow> getPstate s1 Ctrl' = Ctrl'stuckState \<and>
 getVarBool s1 moving' = getVarBool s3 moving' \<and> getVarBool s1 direction' = getVarBool s3 direction')  \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 < ltime s3 Ctrl' - 1 \<longrightarrow>
 \<not> getVarBool s2 alarmButton' \<and> \<not> getVarBool s2 stuck' \<and> getVarBool s2 up' = False \<and> getVarBool s2 down' = False)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'emergency \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> getPstate s2 Ctrl' \<noteq> Ctrl'emergency \<and>
getVarBool s3 alarmButton' \<and>
(\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and> toEnvNum s4 s5 = 1 \<longrightarrow>
getPstate s4 Ctrl' = Ctrl'emergency \<and> getVarBool s5 up' = False \<and> getVarBool s5 down' = False))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'motionless \<longrightarrow>
 getVarBool s1 up' = False \<and> getVarBool s1 down' = False \<and> \<not> getVarBool s1 moving') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'goUp \<longrightarrow>
getVarBool s1 up' = True \<and> getVarBool s1 down' = False \<and> getVarBool s1 moving' \<and> getVarBool s1 direction'= UP') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl' = Ctrl'goDown \<longrightarrow>
getVarBool s1 up' = False \<and> getVarBool s1 down' = True \<and> getVarBool s1 moving' \<and> getVarBool s1 direction'= DOWN') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 Ctrl' = Ctrl'motionless \<or> getPstate s1 Ctrl' = Ctrl'goUp \<or> getPstate s1 Ctrl' = Ctrl'goDown \<or>
getPstate s1 Ctrl' = Ctrl'stuckState \<or> getPstate s1 Ctrl' = Ctrl'emergency)
"

end