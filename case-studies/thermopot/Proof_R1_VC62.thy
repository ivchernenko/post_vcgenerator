theory Proof_R1_VC62
  imports Proofs1 ExtraInv_VC62
begin

theorem proof_1_62: "VC62 inv1 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC62_def inv1_def R1_def)
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
      using invs0(1,2) by auto
    done
  using extra_62 by (auto simp add: VC62_def)

end