theory Proof_R2_VC277
  imports Proofs2 ExtraInv3_VC277
begin

theorem proof_1_277: "VC277 inv2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC277_def inv2_def R2_def)
  apply rule+
    apply simp
   apply(unfold extraInv_def)[1]
   apply(erule conjE)
   apply(erule conjE)
  subgoal premises prems
    apply(insert prems(2))
    apply(erule conjE)
    subgoal premises invs0
      apply(insert invs0(2))
      apply((erule conjE)+)
      subgoal premises ei
        apply((rule allI)+)
        apply(rule impI)
        apply(simp split: if_splits)
         apply(insert prems(1))[1]
         apply simp
        using ei(1) ei(7) substate_toEnvNum_id apply blast
        using invs0(1) by auto
      done
    done
  using extra_277 by(auto simp add: VC277_def)

end