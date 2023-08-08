theory Proof_R3_VC4
  imports Proofs3 ExtraInv_VC4
begin

abbreviation s where "s s0 requestButton_value \<equiv>
(toEnv (setPstate (setVarAny s0 requestButton_value) Ctrl redAfterMinimalRed))"

theorem proof_3_4: "VC4 inv3 s0 requestButton_value"
  apply(unfold VC4_def inv3_def R3_def)
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
  using extra_4 by(auto simp add: VC4_def)
