theory Proof_R4_VC352
  imports Proofs4 ExtraInv3_VC352
begin

theorem proof_4_352: "VC352 inv4 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC352_def inv4_def R4_def)
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
      subgoal premises invs0
        apply(insert invs0(2))
        apply((erule conjE)+)
        subgoal premises extraInvs0
   apply((rule allI)+)
          apply(rule impI)
 apply(insert prems(1))
            apply simp
    apply(simp split: if_splits del: One_nat_def)      
          using extraInvs0(1) extraInvs0(14) extraInvs0(6) le_antisym substate_toEnvNum_id
            apply (metis zero_less_numeral)
          subgoal for s1 s2
            apply(rule cut_rl[of "toEnvNum s1 s0 < OPEN_DOOR_TIME_LIMIT'TIMEOUT"])
            apply(insert extraInvs0(14))
            apply(erule  allE[of _ s0])
             apply(erule impE)
            using extraInvs0(1) apply simp
     using extraInvs0(1) apply simp
      apply (metis (no_types, opaque_lifting) invs0(2) substate_refl substate_trans verit_la_disequality)
     using toEnvNum3 by auto
   using invs0(1) by auto
  done
  done
  using extra_352 by(auto simp add: VC352_def)

end
    