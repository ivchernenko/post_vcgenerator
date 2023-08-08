theory ExtraInv_VC4
  imports ExtraInv_new RequirementLemmas
begin

theorem extra_4: "VC4 extraInv s0 trafficLight_value"
  apply(unfold VC4_def extraInv_def)
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
      using ei(5) apply simp
      apply(rule conjI)
      using ei(6) apply simp
      apply(rule conjI)
       apply((rule P5_ex_imp_ex[OF ei(7) ei(7)]); (auto))
      apply(rule conjI)
      using ei(8) apply auto[1]
      apply(rule conjI)
      using ei(9) apply simp
      apply(rule conjI)
      using ei(10) apply auto[1]
      apply(rule conjI)
      using ei(11) apply auto[1]
      apply(rule conjI)
       apply(insert ei(2))[1]
      apply(cases "getVarBool s0 requestButtonPressed")
        apply((rule P5_ex_or_all_imp_ex_or_all[OF ei(13) ei(12)]); (auto))
       apply((rule P5_ex_imp_ex_or_all[OF ei(15) ei(12)]); (auto))
      apply(rule conjI)
      using ei(13) apply auto[1]
      apply(rule conjI)
       apply(cases "getVarBool s0 requestButtonPressed")
      using ei(14) apply auto[1]
       apply((rule P5_ex_imp_ex[OF ei(15) ei(14)]); (auto))
      apply(rule conjI)
      using ei(15) apply auto[1]
      apply(rule conjI)
      using ei(16) apply auto[1]
      apply(rule conjI)
       apply(cases "getVarBool s0 requestButtonPressed")
        apply(rule allI)
        apply(rule impI)
        apply(rule allI)+
        apply(rule impI)
        apply(simp split: if_splits)
        using substate_toEnvNum_id apply blast
      using ei(16)
         apply (smt (verit) One_nat_def substate.simps(2) substate.simps(6) substate.simps(7) substate_asym substate_refl toEnvP.simps(6))
      using ei(17) apply auto[1]
      using ei(17) apply auto[1]
      using ei(18) by auto
    done
  done

end
      
      
     