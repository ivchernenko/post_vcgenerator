theory ExtraInv_VC2
  imports ExtraInv_new VCTheoryLemmas RequirementLemmas
begin

abbreviation s where "s s0 trafficLight_value \<equiv>
  (toEnv (setPstate (setVarBool (setVarAny s0 trafficLight_value) redAfterMinimalRed PRESSED) Ctrl redAfterMinimalRed))"

theorem extra_2: "VC2 extraInv s0 trafficLight_value"
  apply(unfold VC2_def extraInv_def)
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
       apply(rule allI)
      subgoal for s5
        apply(cases "s5 = s s0 trafficLight_value")
         apply(rule impI)
         apply((rule allI)+)
        subgoal for s1 s2
          apply(cases "s2 = s5")
           apply(rule impI)
           apply(rule exI[of _ s2])
          using substate_refl  ei(5) apply simp
          apply(insert ei(7))
          apply(erule allE[of _ s0])
          apply(erule impE)
          using substate_refl apply simp
          apply(erule allE[of _ s1])
          apply(erule allE[of _ s2])
          apply(rule impI)
          apply(erule impE)
          using substate_refl apply(simp split: if_splits)
          apply(erule exE)
          subgoal for s4
            apply(rule exI[of _ s4])
            by simp
          done
        using ei(7) by auto
      apply(rule conjI)
      using ei(8) apply auto[1]
      apply(rule conjI)
      using ei(9) apply simp
      apply(rule conjI)
      using ei(10) apply auto[1]
      apply(rule conjI)
      using ei(11) apply auto[1]
      apply(rule conjI)
       apply(cases "getVarBool s0 requestButtonPressed")
      apply(insert ei(2))[2]
        apply((rule P5_ex_or_all_imp_ex_or_all[OF ei(13) ei(12)]); (auto))
       apply((rule P5_ex_imp_ex_or_all[OF ei(15) ei(12)]); (auto))
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

