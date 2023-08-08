theory Proof_R1_VC10
  imports Proofs1 ExtraInv_VC10
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setPstate (setVarBool (setVarAny s0 requestButton_value) minimalRed NOT_PRESSED) Ctrl minimalRed))"

theorem proof_1_10: "VC10 inv1 s0 requestButton_value"
  apply(unfold VC10_def inv1_def R1_def)
  apply(rule impI)
  apply(rule cut_rl[of "extraInv (s s0 requestButton_value)"])
   apply(rule conjI)
    apply(rule conjI)
     apply simp
    apply(erule conjE)
    apply(unfold extraInv_def)[1]
  subgoal premises vc_prems
    apply(insert vc_prems(1))
    apply((erule conjE)+)
    subgoal premises ei
      apply(cases "getVarBool s0 requestButtonPressed")
      using ei(4) vc_prems(2,3) substate_refl[of s0]  apply (simp split: if_splits)
      apply(rule P5_left2req[OF ei(15)])
      using vc_prems(3) by simp
    done
  using extra_10 by(auto simp add: VC10_def)

end
       
