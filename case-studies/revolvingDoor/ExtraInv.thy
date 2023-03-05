theory ExtraInv
  imports RevolvingDoor
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'motionless \<longrightarrow>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1  \<longrightarrow> getPstate s2 Controller = Controller'motionless \<and> \<not> getVarBool s2 user) \<or>
(\<exists> s2 s3. toEnvP s2 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 getPstate s2 Controller = Controller'rotating \<and> ltime s2 Controller = DELAY'TIMEOUT \<and> \<not> getVarBool s3 user \<and>
\<not> getVarBool s3 pressure \<and> (\<forall> s4 s5. toEnvP s4 \<and> toEnvP s5 \<and> substate s3 s4 \<and> substate s4 s5 \<and> substate s5 s1 \<and>
toEnvNum s4 s5 = 1 \<longrightarrow> getPstate s4 Controller = Controller'motionless \<and> \<not> getVarBool s5 user))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<longrightarrow> 
 ltime s1 Controller \<le> DELAY'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 toEnvNum s2 s1 = ltime s1 Controller \<and>
((getPstate s2 Controller = Controller'motionless \<or> getPstate s2 Controller = Controller'rotating) \<and>
 getVarBool s3 user \<or> getPstate s2 Controller = Controller'suspended) \<and> \<not> getVarBool s3 pressure)) \<and>
(\<forall> s1 s2 s3. toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and>
getPstate s3 Controller = Controller'rotating \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s1 s3 < ltime s3 Controller \<longrightarrow>
getPstate s1 Controller = Controller'rotating \<and> \<not> getVarBool s2 user) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> 
(getPstate s2 Controller = Controller'motionless \<and> getVarBool s3 user \<or>
 getPstate s2 Controller = Controller'suspended) \<and> \<not> getVarBool s3 pressure \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 Controller = Controller'rotating))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<longrightarrow>
 ltime s1 Controller \<le> SUSPENSION_TIME'TIMEOUT) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and>
 toEnvNum s2 s1 = ltime s1 Controller \<and>
(getPstate s2 Controller \<noteq> Controller'motionless \<or> getVarBool s3 user) \<and> getVarBool s3 pressure)) \<and>
(\<forall> s1 s2 s3. toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s1 s3 < ltime s3 Controller \<and> getPstate s3 Controller = Controller'suspended \<longrightarrow>
getPstate s1 Controller = Controller'suspended \<and> \<not> getVarBool s2 pressure) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<longrightarrow>
(\<exists> s2 s3. toEnvP s2 \<and> toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> toEnvNum s2 s3 = 1 \<and> 
(getPstate s2 Controller = Controller'motionless \<and> getVarBool s3 user \<or>
 getPstate s2 Controller = Controller'rotating) \<and> getVarBool s3 pressure \<and>
(\<forall> s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 Controller = Controller'suspended))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'motionless \<longrightarrow>
 getVarBool s1 rotation = False \<and> getVarBool s1 brake = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'rotating \<longrightarrow>
 getVarBool s1 rotation = True \<and> getVarBool s1 brake = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller = Controller'suspended \<longrightarrow>
 getVarBool s1 rotation = False \<and> getVarBool s1 brake = True) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 Controller = Controller'motionless \<or> getPstate s1 Controller = Controller'rotating \<or>
getPstate s1 Controller = Controller'suspended)
"

end