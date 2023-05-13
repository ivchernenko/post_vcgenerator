theory Proof_R5_VC66
  imports Proofs5 ExtraInv_VC66
begin

theorem proof_5_66: "VC66 inv5 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC66_def inv5_def R5_def)
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
  using extra_66 by(auto simp add: VC66_def)