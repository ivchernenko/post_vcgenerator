theory Proof_R3_VC10
  imports Proofs3 ExtraInv_VC10
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setPstate (setVarBool (setVarAny s0 requestButton_value) minimalRed NOT_PRESSED) Ctrl minimalRed))"

theorem proof_3_10: "VC10 inv3 s0 requestButton_value"
  apply(unfold VC10_def inv3_def R3_def)
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
      apply(rule P5_left2req[OF ei(7)])
      using vc_prems(3) by simp
    done
  using extra_10 by(auto simp add: VC10_def)
