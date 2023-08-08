theory Proof_R4_VC2
  imports Proofs4
begin 
abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setPstate (setVarBool (setVarAny s0 requestButton_value) redAfterMinimalRed PRESSED) Ctrl redAfterMinimalRed)) "

theorem proof_4_2: "VC2 R4 s0 requestButton_value"
  apply(unfold VC2_def R4_def)
  (*  by (metis getVarBool.simps(2) getVarBool.simps(4) getVarBool.simps(7) substate_refl substate_trans toEnvP.simps(1))*)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(rule allI)+
  subgoal  for s1 s2 s3
    apply(cases "s3 = s s0 requestButton_value")
     prefer 2
     apply(erule conjE)+
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
     apply(erule allE[of _ s3])
     apply simp
     apply(erule conjE)+
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
    apply(erule allE[of _ s0])
    apply(rule impI)
    apply(erule impE)
    using substate_refl apply (simp split: if_splits)
    using substate_toEnvNum_id apply blast
    by simp
  done

end

   