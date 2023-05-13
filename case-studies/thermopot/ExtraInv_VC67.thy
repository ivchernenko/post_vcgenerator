theory ExtraInv_VC67
  imports ExtraInv
begin

theorem extra_67: "VC67 extraInv env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC67_def extraInv_def)
  apply(rule impI)
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems
    apply(insert prems(2))
    apply((erule conjE)+)
    subgoal premises ei
      apply(insert ei(1))
      apply(rule conjI)
       apply simp
      apply(rule conjI)
      using ei(2) ei(3) prems(1) apply simp
      apply(rule conjI)
      using ei(3) apply simp
      apply(rule conjI)
      using ei(4) apply simp
      apply(rule conjI)
      using ei(5) prems(1) apply simp
      apply(rule conjI)
      using ei(6) prems(1) toEnvP_imp_gtime_gt_0 apply simp
      apply(rule conjI)
      using ei(7) prems(1) toEnvP_imp_gtime_gt_0 apply simp
      apply(rule conjI)
      using ei(8) prems(1) toEnvP_imp_gtime_gt_0 apply simp
      apply(rule conjI)
      using ei(9) apply simp
      using ei(10) by simp
    done
  done

end