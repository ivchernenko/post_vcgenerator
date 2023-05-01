theory Proof_R4_VC252
  imports Proofs4 ExtraInv3_VC252
begin

theorem proof_4_252: "VC252 inv4 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC252_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)[1]
   apply(erule conjE)
   apply(erule conjE)
  subgoal premises prems
   apply((rule allI)+)
    apply(rule impI)
    apply(simp split: if_splits del: One_nat_def)
      apply(insert prems(1))[1]
    apply simp
    using prems(2)
    using substate_refl apply presburger
    subgoal for s1 s2
    apply(rule cut_rl[of "toEnvNum s2 s0 < OPEN_DOOR_TIME_LIMIT'TIMEOUT"])
      using prems(2)
      apply (meson substate_refl)
      by auto
    using prems(2)
    by meson 
  using extra_252 by (auto simp add: VC252_def)

end