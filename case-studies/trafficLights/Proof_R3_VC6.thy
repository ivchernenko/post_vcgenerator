theory Proof_R3_VC6
  imports Proofs3 ExtraInv_VC6
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redToGreen))"

theorem proof_3_6: "VC6 inv3 s0 requestButton_value"
  apply(unfold VC6_def inv3_def R3_def)
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
  using extra_6 by(auto simp add: VC6_def)
