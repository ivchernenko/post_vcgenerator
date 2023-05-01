theory Proof_R1_VC377
  imports Proofs1 ExtraInv3_VC377
begin

theorem proof_1_377: "VC377 inv1 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC377_def inv1_def R1_def)
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
        using ei(1) ei(8) substate_toEnvNum_id apply blast
        using invs0(1) by auto
      done
    done
  using extra_377 by(auto simp add: VC377_def)

end

