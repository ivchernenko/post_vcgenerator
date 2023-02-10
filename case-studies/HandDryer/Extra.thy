theory Extra
  imports HandDryer VCTheoryLemmas
begin

theorem extra2: "VC2 extraInv s0 hands_value"
  apply(simp only: VC2_def extraInv_def dryer_def
waiting_def drying_def)
  by auto

theorem extra3: "VC3 extraInv s0 hands_value"
  apply(simp only: VC3_def extraInv_def dryer_def
waiting_def drying_def)
  by auto

theorem extra5: "VC5 extraInv s0 hands_value"
  apply(simp only: VC5_def extraInv_def dryer_def
waiting_def drying_def)
  apply(auto)
proof -
  assume 1: " toEnvP s0"
   " \<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
         getPstate s1 Ctrl =
         Suc (Suc (Suc (Suc 0))) \<or>
         getPstate s1 Ctrl =
         Suc (Suc (Suc (Suc (Suc 0))))"
    "env (setVarAny s0 ON) ON "
   " getPstate s0 Ctrl =
    Suc (Suc (Suc (Suc (Suc 0)))) "
   " hands_value "
   " 0 < ltimeEnv s0 Ctrl "
   " ltimeEnv s0 Ctrl \<le> 10 "
  "\<forall>s1. toEnvP s1 \<and>
         substate s1 s0 \<and>
         Suc (toEnvNum s1 s0) = ltimeEnv s0 Ctrl \<longrightarrow>
         getVarBool s1 (Suc 0) \<and>
         getVarBool s1 (Suc (Suc 0)) "
   " \<forall>s1. toEnvP s1 \<and>
         substate s1 s0 \<and>
         Suc (toEnvNum s1 s0) < ltimeEnv s0 Ctrl \<longrightarrow>
         \<not> getVarBool s1 (Suc 0) \<and>
         getVarBool s1 (Suc (Suc 0))"
  with toEnvNum_id  have "Suc (toEnvNum s0 s0) = ltimeEnv s0 Ctrl \<or>
Suc (toEnvNum s0 s0) <ltimeEnv s0 Ctrl" by auto
  with 1 substate_refl
  show "getVarBool s0 (Suc (Suc 0))" by auto
qed

theorem extra6: "VC6 extraInv s0 hands_value"
  apply(simp only: VC6_def extraInv_def dryer_def
waiting_def drying_def)
  by auto

theorem extra7: "VC7 extraInv s0 hands_value"
  apply(simp only: VC7_def extraInv_def dryer_def
waiting_def drying_def)
  apply(auto)
proof -
  assume 1: "toEnvP s0 "
    "\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
         getPstate s1 Ctrl =
         Suc (Suc (Suc (Suc 0))) \<or>
         getPstate s1 Ctrl =
         Suc (Suc (Suc (Suc (Suc 0)))) "
   " env (setVarAny s0 OFF) OFF "
    "getPstate s0 Ctrl =
    Suc (Suc (Suc (Suc (Suc 0)))) "
    "\<not> hands_value "
   " ltimeEnv s0 Ctrl \<noteq> 10 "
    "0 < ltimeEnv s0 Ctrl "
   " ltimeEnv s0 Ctrl \<le> 10 "
   " \<forall>s1. toEnvP s1 \<and>
         substate s1 s0 \<and>
         Suc (toEnvNum s1 s0) = ltimeEnv s0 Ctrl \<longrightarrow>
         getVarBool s1 (Suc 0) \<and>
         getVarBool s1 (Suc (Suc 0)) "
    "\<forall>s1. toEnvP s1 \<and>
         substate s1 s0 \<and>
         Suc (toEnvNum s1 s0) < ltimeEnv s0 Ctrl \<longrightarrow>
         \<not> getVarBool s1 (Suc 0) \<and>
         getVarBool s1 (Suc (Suc 0))"
with toEnvNum_id  have "Suc (toEnvNum s0 s0) = ltimeEnv s0 Ctrl \<or>
Suc (toEnvNum s0 s0) <ltimeEnv s0 Ctrl" by auto
  with 1 substate_refl
  show "getVarBool s0 (Suc (Suc 0))" by auto
qed

end