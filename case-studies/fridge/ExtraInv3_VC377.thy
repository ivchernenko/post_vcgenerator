theory ExtraInv3_VC377
  imports ExtraInv3 RequirementLemmas
begin

theorem extra_377: "VC377 extraInv env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC377_def extraInv_def)
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
      using ei(2) apply simp
      apply(rule conjI)
       apply((rule ex_or_all_imp_ex_or_all[OF ei(3) ei(3)]);auto)
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
      apply(rule conjI)
      using ei(13) apply simp
      apply(rule conjI)
      using ei(14) apply auto[1]
      using ei(15) by simp
    done
  done

end
