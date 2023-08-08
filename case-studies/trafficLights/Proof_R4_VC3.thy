theory Proof_R4_VC3
  imports Proofs4
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED))"

theorem proof_4_3: "VC3 R4 s0 requestButton_value"
  apply(unfold VC3_def R4_def)
 (* by (metis getVarBool.simps(2) getVarBool.simps(4) substate_refl substate_trans toEnvP.simps(1))*)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(rule allI)+
  subgoal  for s1 s2 s3
    apply(cases "s3 = s s0 requestButton_value")
     apply(erule conjE)+
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
    apply(erule allE[of _ s0])
    apply(rule impI)
    apply(erule impE)
    using substate_refl apply (simp split: if_splits)
    using substate_toEnvNum_id apply blast
     apply simp
     apply(erule conjE)+
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
     apply(erule allE[of _ s3])
    by simp
  done

end
