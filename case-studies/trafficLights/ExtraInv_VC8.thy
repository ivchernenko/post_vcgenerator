theory ExtraInv_VC8
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_8: "VC8 extraInv s0 trafficLight_value"
  apply(unfold VC8_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(1))
    apply((erule conjE)+)
    subgoal premises ei
      apply(insert vc_prems(2) ei(1))
      apply(rule conjI)
      using ei(2) apply simp
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using ei(5) substate_refl apply simp
      apply(rule conjI)
      using ei(6) apply simp
      apply(rule conjI)
      using ei(7) apply auto[1]
      apply(rule conjI)
      apply((rule P5_ex_imp_ex_or_all[OF ei(7) ei(8)]); (auto))
      apply(rule conjI)
      using ei(9) apply simp
      apply(rule conjI)
      apply(insert ei(3))[1]
       apply((rule P5_ex_or_all_imp_ex[OF ei(11) ei(10)]); (auto))
      apply(rule conjI)
      using ei(11) apply auto[1]
      apply(rule conjI)
      using ei(12) apply auto[1]
      apply(rule conjI)
      using ei(13) apply auto[1]
      apply(rule conjI)
      using ei(14) apply auto[1]
      apply(rule conjI)
      using ei(15) apply auto[1]
      apply(rule conjI)
      using ei(16) apply auto[1]
      apply(rule conjI)
      using ei(17) apply auto[1]
      using ei(18) by auto
    done
  done

end