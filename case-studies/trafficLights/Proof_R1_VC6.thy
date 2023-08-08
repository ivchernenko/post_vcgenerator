theory Proof_R1_VC6
  imports Proofs1 ExtraInv_VC6
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redToGreen))"

theorem proof_1_6: "VC6 inv1 s0 requestButton_value"
  apply(unfold VC6_def inv1_def R1_def)
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
      apply(rule P5_disj2req[OF ei(11)])
      using vc_prems(3) by simp
    done
  using extra_6 by(auto simp add: VC6_def)

end
