theory Proof_R2_VC65
  imports Proofs2 ExtraInv_VC65
begin

theorem proof_2_65: "VC65 inv2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC65_def inv2_def R2_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
  apply(unfold extraInv_def)[1]
   apply(erule conjE)
   apply(erule conjE)
  subgoal premises prems
    apply(insert prems(2))
    apply(erule conjE)
    apply((erule conjE)+)
    subgoal premises invs0
      apply((rule allI)+)
      apply(rule impI)
      apply(simp split: if_splits)
      using prems(1) apply simp
      using invs0
       apply (metis substate_toEnvNum_id)
      using invs0(2) by auto
    done
  using extra_65 by(auto simp add: VC65_def)

end
