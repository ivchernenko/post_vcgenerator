theory ExtraInv_new
  imports Requirements
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'minimalOpened' \<longrightarrow> ltime s1 Controller' \<le> 10) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Controller' = Controller'isOpened' \<longrightarrow> ltime s1 Controller' \<le> 90) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> (getPstate s1 Controller' = Controller'isClosed' \<or> getPstate s1 Controller' = STOP) \<longrightarrow>
 \<not> getVarBool s1 open') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and>
 (getPstate s1 Controller' = Controller'minimalOpened' \<or> getPstate s1 Controller' = Controller'isOpened') \<longrightarrow> 
  getVarBool s1 open') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = EntranceController'isClosed' \<longrightarrow> \<not>getVarBool s1 enter') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 EntranceController' = EntranceController'isOpened' \<longrightarrow> getVarBool s1 enter') \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 Controller' \<in>
 {Controller'isClosed', Controller'minimalOpened', Controller'isOpened', STOP}) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 EntranceController' \<in>
 {EntranceController'isClosed', EntranceController'isOpened', STOP}) \<and>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 Controller' = Controller'isClosed' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> getVarBool s1 open' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> 100 \<and> \<not> getVarBool s3 open' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> getVarBool s2 open')))) \<and>
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 Controller' = Controller'isOpened' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> getVarBool s1 open' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> 100 \<and> \<not> getVarBool s3 open' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> getVarBool s2 open')) \<or>
toEnvNum s1 s4 < 10 +ltime s4 Controller' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> getVarBool s2 open'))) \<and> 
(\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> getPstate s4 Controller' = Controller'minimalOpened' \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> getVarBool s1 open' \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> 100 \<and> \<not> getVarBool s3 open' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> getVarBool s2 open')) \<or>
toEnvNum s1 s4 < ltime s4 Controller' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> getVarBool s2 open'))) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Controller' = Controller'minimalOpened' \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> toEnvNum s1 s2 = 1 \<and>
 toEnvNum s2 s3 + 1 < ltime s3 Controller' \<longrightarrow> \<not> (\<not> getVarBool s1 open' \<and> getVarBool s2 open'))) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Controller' = Controller'isOpened' \<longrightarrow>
(\<forall> s1 s2. toEnvP s1 \<and> toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> toEnvNum s1 s2 = 1 \<and>
 toEnvNum s2 s3 + 1 < 10 \<longrightarrow> \<not> (\<not> getVarBool s1 open' \<and> getVarBool s2 open')))
"
theorem extra_1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def)
  by auto

end
