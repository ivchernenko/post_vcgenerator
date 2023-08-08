theory Proof_R4_VC8
  imports Proofs4 ExtraInv_VC8
begin

abbreviation s where "s s0 requestButton_value \<equiv>
 (toEnv (setPstate (setVarBool (setVarBool (setVarAny s0 requestButton_value) minimalRed PRESSED) redAfterMinimalRed NOT_PRESSED) Ctrl green))"

theorem proof_4_8: "VC8 inv4 s0 requestButton_value"
  apply(unfold VC8_def inv4_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(rule allI)+
  subgoal for s1 s2 s3
    apply(cases "s3 = s s0 requestButton_value")
     apply(erule conjE)
     apply(erule conjE)
     apply(erule conjE)
    subgoal premises vc_prems
      apply(insert vc_prems(3))
      apply(unfold extraInv_def)[1]
      apply(erule conjE)+
      subgoal premises ei
        using vc_prems(1,5) apply simp
        apply(insert ei(1) ei(18))
        apply(erule allE[of _ s0])
        using substate_refl apply simp
        apply(erule allE[of _ s1])
        apply(erule allE[of _ s2])
        by (metis One_nat_def Suc_0_div_numeral(1) getVarBool.simps(2) getVarBool.simps(4) getVarBool.simps(6) getVarBool.simps(7) numerals(1) one_div_two_eq_zero toEnvP.simps(4) toEnvP.simps(6) toEnvP.simps(7) zero_neq_one)
      done
         apply(erule conjE)+
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
     apply(erule allE[of _ s3])
    by simp
  using extra_8 by(auto simp add: VC8_def)

end

