theory ExtraInv3_VC277
  imports ExtraInv3 RequirementLemmas
begin

theorem extra_3_277: "VC277 extraInv3 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC277_def extraInv3_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
    apply(erule conjE)
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(2))
    apply((erule conjE)+)
    subgoal premises ei
      apply(insert vc_prems(1) ei(1))
      apply(rule conjI)
       apply((rule ex_imp_ex[OF ei(2) ei(2)]);auto)
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using ei(5) apply simp
      apply(rule conjI)
      using ei(6) apply simp
      apply(rule conjI)
      using ei(7) apply simp
      apply(rule conjI)
      using ei(8) apply simp
      apply(rule conjI)
      using ei(9) apply simp
      apply(rule conjI)
      using ei(10) apply simp
      apply(rule conjI)
      using ei(11) apply simp
      apply(rule conjI)
      using ei(12) apply simp
      using ei(13) by simp
    done
  done

end
