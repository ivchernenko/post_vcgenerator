theory Proof_R2_VC63
  imports Proofs2 ExtraInv_VC63
begin

theorem proof_2_63: "VC63 inv2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC63_def inv2_def R2_def)
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
       apply (meson substate_refl)
      using invs0(2) by auto
    done
  using extra_63 by(auto simp add: VC63_def)

end