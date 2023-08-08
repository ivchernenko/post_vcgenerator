theory Proof_R1_VC7
  imports Proofs1 ExtraInv_VC7
begin

abbreviation s where "s s0 requestButton_value \<equiv>
 (toEnv (setVarAny s0 requestButton_value))"

theorem proof_1_2: "VC7 inv1 s0 requestButton_value"
  apply(unfold VC7_def inv1_def R1_def)
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
      apply(rule P5_left2req[OF ei(14)])
      using vc_prems(3) by simp
    done
  using extra_7 by(auto simp add: VC7_def)
