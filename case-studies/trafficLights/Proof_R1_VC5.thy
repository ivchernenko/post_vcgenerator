theory Proof_R1_VC5
  imports Proofs1 ExtraInv_VC5
begin

abbreviation s where "s s0 requestButton_value \<equiv> 
 (toEnv (setVarAny s0 requestButton_value))"

theorem proof_1_5: "VC5 inv1 s0 requestButton_value"
  apply(unfold VC5_def inv1_def R1_def)
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
       apply(rule P5_disj2req[OF ei(13)])
      using vc_prems(3) apply simp
      apply(rule P5_left2req[OF ei(15)])
      using vc_prems(3) by simp
    done
  using extra_5 by(auto simp add: VC5_def)

end
