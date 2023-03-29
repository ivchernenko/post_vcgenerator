theory Proofs5
  imports Requirements VCTheoryLemmas
begin

definition inv5 where "inv5 s \<equiv> R5 s \<and> extraInv s"

thm extraInv_def

lemma minimalOpened_R5: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 < 9 \<and> getPstate s0 Controller' = Controller'minimalOpened' \<and>
ltime s0 Controller' = 10  \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s2. toEnvP s2 \<and> substate s2 s \<and> getPstate s2 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltime s2 Init'init' \<longrightarrow>
            getPstate s1 Init'init' = Controller'minimalOpened')) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> (getPstate s1 Init'init' = Controller'isOpened' \<or> getPstate s1 Init'init' = Controller'minimalOpened') \<longrightarrow>
      getVarBool s1 Controller'minimalOpened') 
\<longrightarrow> \<not> (\<not> getVarBool s1 open' \<and> getVarBool s2 open')"
  using substate_trans
  by (smt (verit, ccfv_SIG) BitM_inc_eq eval_nat_numeral(2) inc.simps(2) nat_add_left_cancel_less plus_1_eq_Suc toEnvNum3)

lemma isOpened_timeout_R5: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 < 9 \<and> getPstate s0 Controller' = Controller'isOpened' \<and>
ltime s0 Controller' = 90  \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow> ltime s1 Init'init' \<le> 90) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Init'init' = Controller'isOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Init'init' \<longrightarrow> getPstate s1 Init'init' = Controller'isOpened') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 + 1 < ltime s3 Init'init' \<longrightarrow> \<not> getVarBool s2 Init')) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> (getPstate s1 Init'init' = Controller'isOpened' \<or> getPstate s1 Init'init' = Controller'minimalOpened') \<longrightarrow>
      getVarBool s1 Controller'minimalOpened') 
\<longrightarrow>  \<not>(\<not> getVarBool s1 open' \<and> getVarBool s2 open')"
  apply(rule impI)
  apply(rule cut_rl[of "toEnvNum s1 s0 < ltime s0 Controller'"])
  using substate_trans
   apply meson
  using toEnvNum3 by auto

lemma isOpened_R5: "toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s0 \<and> substate s1 s2 \<and> substate s2 s0 \<and> substate s0 s \<and>
toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s0 < 9 \<and> getPstate s0 Controller' = Controller'isOpened' \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'minimalOpened' \<longrightarrow> ltime s1 Init'init' \<le> 10) \<and>
(\<forall>s2. toEnvP s2 \<and> substate s2 s \<and> getPstate s2 Init'init' = Controller'minimalOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s2 \<and> toEnvNum s1 s2 < ltime s2 Init'init' \<longrightarrow>
            getPstate s1 Init'init' = Controller'minimalOpened')) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> (getPstate s1 Init'init' = Controller'isOpened' \<or> getPstate s1 Init'init' = Controller'minimalOpened') \<longrightarrow>
      getVarBool s1 Controller'minimalOpened') \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow> ltime s1 Init'init' \<le> 90) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'init' = Controller'isOpened' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'init' \<and>
          getPstate s2 Init'init' = Controller'minimalOpened' \<and>
          ltime s2 Init'init' = 10 \<and> \<not> getVarBool s3 EntranceController'isOpened')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Init'init' = Controller'isOpened' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Init'init' \<longrightarrow> getPstate s1 Init'init' = Controller'isOpened') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 + 1 < ltime s3 Init'init' \<longrightarrow> \<not> getVarBool s2 Init'))
\<longrightarrow> \<not> (\<not> getVarBool s1 open' \<and> getVarBool s2 open')"
  apply(rule impI)
  apply(cases "toEnvNum s1 s0 < ltime s0 Controller'")
  using substate_trans
   apply meson 
  apply(rule exE[of " (\<lambda> s2. \<exists> s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s0 = ltime s0 Init'init' \<and>
          getPstate s2 Init'init' = Controller'minimalOpened' \<and> ltime s2 Init'init' = 10  \<and> \<not> getVarBool s3 EntranceController'isOpened')"])
apply blast
  apply(drule exE)
   prefer 2
   apply assumption
  subgoal for s3 s4
    apply(rule cut_rl[of "substate s3 s0"])
    apply(cases "substate s2 s3")
     apply(rule impE[OF minimalOpened_R5[of s1 s2 s3 s]])
    using substate_trans toEnvNum3
       apply (smt (verit) leD le_neq_implies_less le_trans less_or_eq_imp_le toEnvNum_substate1)
      apply assumption
     apply(rule cut_rl[of "s1=s3"])
    using substate_trans
      apply meson
     apply(rule cut_rl[of "toEnvNum s1 s0 = toEnvNum s3 s0"])
    using toEnvNum_eq_imp_eq2 substate_trans
      apply meson
     apply(rule le_antisym)
      apply(rule cut_rl[of "substate s3 s2 \<and> s2 \<noteq> s3"])
    using toEnvNum_substate2  toEnvNum_eq_imp_eq2 toEnvNum3[of s1 s2 s0]
       apply (metis Suc_leI order.order_iff_strict plus_1_eq_Suc)
    using substate_linear substate_refl
      apply meson
     apply arith
    using substate_trans by meson
  done

theorem proof_5_1: "VC1 inv5 s0"
  apply(unfold VC1_def inv5_def R5_def extraInv_def)
  by auto

theorem proof_5_2: "VC2 R5 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC2_def)
  apply simp
  apply(unfold R5_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  subgoal premises vc_prems
   apply((rule allI)+)
    apply(rule impI)
    apply(simp split: if_splits)
using vc_prems
  by (metis One_nat_def) 
  done

theorem proof_5_500: "VC500 R5 env s0 PdOut_value paid_value opened_value"
  apply(unfold VC500_def)
  apply simp
  apply(unfold R5_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  subgoal premises vc_prems
    apply((rule allI)+)
    apply(rule impI)
    apply(simp split: if_splits)
    subgoal for s1 s2
      apply(rule cut_rl[of "toEnvNum s2 s0 <10"])
      using vc_prems substate_refl apply(metis One_nat_def) 
      by simp
    using vc_prems by(metis One_nat_def) 
  done

end
