theory Proof_R3_VC9
  imports Proofs3 ExtraInv_VC9
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setVarAny s0 requestButton_value))"

theorem proof_3_9: "VC9 inv3 s0 requestButton_value"
  apply(unfold VC9_def inv3_def R3_def)
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
  using extra_9 by(auto simp add: VC9_def)