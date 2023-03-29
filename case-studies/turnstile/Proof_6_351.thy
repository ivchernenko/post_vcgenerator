theory Proof_6_351
  imports Proofs6
begin

theorem proof_6_351: "VC351 inv6 env s0 PdOut paid_value  opened_value"
  apply(unfold VC351_def)
  apply simp
  apply(unfold inv6_def R6_def)
  apply(rule impI)
  apply(erule conjE)
  apply(erule conjE)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)
  subgoal premises vc_prems
    apply(rule allI)
    apply(rule impI)
    apply(simp split: if_splits)
    using vc_prems(1,3) substate_refl[of s0] apply blast
    using vc_prems(2) by auto
