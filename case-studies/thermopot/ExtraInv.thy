theory ExtraInv
  imports Requirements VCTheoryLemmas
begin

definition extraInv where "extraInv s \<equiv> toEnvP s \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 HeaterController' = HeaterController'begin' \<longrightarrow> 
getVarBool s1 boilingMode' = False \<and> getVarBool s1 maintainingMode' = False \<and> getVarBool s1 heater' = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 HeaterController' = HeaterController'heating' \<longrightarrow>
 getVarBool s1 boilingMode' = True \<and> getVarBool s1 maintainingMode' = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 HeaterController' =  HeaterController'maintaining' \<longrightarrow>
getVarBool s1 boilingMode' = False \<and> getVarBool s1 maintainingMode' = True) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 HeaterController' = STOP \<longrightarrow> 
getVarBool s1 boilingMode' = False \<and> getVarBool s1 maintainingMode' = False \<and> getVarBool s1 heater' = False) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> (getPstate s1 Init' = Init'begin' \<longleftrightarrow> toEnvNum emptyState s1 = 1)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> (getPstate s1 HeaterController' = STOP \<longleftrightarrow> toEnvNum emptyState s1 = 1)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> (getPstate s1 TempSelection' = STOP \<longleftrightarrow> toEnvNum emptyState s1 = 1)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
 getPstate s1 HeaterController' \<in> {HeaterController'begin', HeaterController'heating', HeaterController'maintaining', STOP})\<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> getPstate s1 TempSelection' \<in> {TempSelection'tempSelection', STOP}) "

theorem extra_1: "VC1 extraInv s0"
  apply(unfold VC1_def extraInv_def)
  by simp


end