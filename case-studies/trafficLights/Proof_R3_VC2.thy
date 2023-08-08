theory Proof_R3_VC2
  imports Proofs3 ExtraInv_VC2
begin

theorem proof_3_2: "VC2 inv3 s0 requestButton_value"
  apply(unfold VC2_def inv3_def R3_def)
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
  using extra_2 by(auto simp add: VC2_def)
