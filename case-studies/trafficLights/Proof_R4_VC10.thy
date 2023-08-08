theory Proof_R4_VC10
  imports Proofs4
begin

abbreviation s where "s s0 requestButton_value \<equiv>
 (toEnv (setPstate (setVarBool (setVarAny s0 requestButton_value) minimalRed NOT_PRESSED) Ctrl minimalRed))"

theorem proof_4_10: "VC10 R4 s0 requestButton_value"
  apply(unfold VC10_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(rule allI)+
  subgoal premises vc_prems for s1 s2 s3
    apply(cases "s3 = s s0 requestButton_value")
     apply simp
    apply(insert vc_prems)
     apply(erule conjE)+
     apply(erule allE[of _ s1])
     apply(erule allE[of _ s2])
     apply(erule allE[of _ s3])
    by simp
  done

end