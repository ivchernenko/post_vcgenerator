theory Extra339
  imports ExtraInv VCTheoryLemmas
begin

abbreviation s where "s s0 PdOut_value paid_value opened_value \<equiv>
 (toEnv
             (setPstate
               (setVarBool
                 (setPstate
                   (setVarBool
                     (setVarBool
                       (setVarBool (setVarBool (setVarBool s0 Init' PdOut_value) Init'init' paid_value) Controller'isClosed'
                         opened_value)
                       Controller'minimalOpened' True)
                     EntranceController'isOpened' False)
                   Init'init' Controller'minimalOpened')
                 EntranceController'isClosed' True)
               Controller'isClosed' EntranceController'isOpened'))"

theorem extra339: "VC339 extraInv env s0 PdOut_value paid_value opened_value"
  apply(unfold VC339_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises vc_prems
    apply(insert vc_prems(2))
    apply((erule conjE)+)
    subgoal premises ei
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(2) apply simp
      apply(rule conjI)
       apply(insert ei(1) ei(3))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
         apply(erule allE[of _ s0])
         apply(erule impE)
        using vc_prems(1) substate_refl apply simp
         apply(erule exE)
        subgoal for s2
          apply(rule exI[of _ s2])
          by simp
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(4) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(5) apply simp
      apply(rule conjI)
       apply(insert ei(1) ei(6))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
        apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 PdOut_value paid_value opened_value"])
        using vc_prems(1) substate_refl toEnvNum_id apply simp
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(7) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(8) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(9) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(10) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(11) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(12) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(13) apply simp
     apply(rule conjI)
      using vc_prems(1) ei(1) ei(14) apply simp
     apply(rule conjI)
       apply(insert ei(1) ei(15))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
        apply(rule exI[of _ s0])
         apply(rule exI[of _ "s s0 PdOut_value paid_value opened_value"])
         apply(insert vc_prems(1) substate_refl toEnvNum_id)
        apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
         apply(rule conjI)
          apply simp
        using substate_antisym
         apply (metis (no_types, lifting))
        by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(16) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(17) apply simp
      apply(rule conjI)
       apply(insert ei(1) ei(18))[1]
       apply(rule allI)
      subgoal for s1
        apply(cases "s1 = (s s0 PdOut_value paid_value opened_value)")
         apply(rule impI)
         apply(erule allE[of _ s0])
         apply(erule impE)
        using vc_prems(1) substate_refl apply simp
         apply(erule exE)
         apply(erule exE)
        subgoal for s2 s3
          apply(rule exI[of _ s2])
          apply(rule exI[of _ s3])
          apply(rule cut_rl[of "toEnvNum s2 s1 = ltime s1 Controller'minimalOpened'"])
           apply simp
          apply(rule cut_rl[of "s2 \<noteq> (s s0 PdOut_value paid_value opened_value) "])
           apply simp
           apply (meson toEnvP.simps(3) toEnvP.simps(9))
          using substate_trans  substate_antisym[of s0  s2] substate_refl by auto
        by simp
      apply(rule conjI)
       apply(insert ei(1) ei(19))[1]
       apply(rule allI)
      subgoal for s3
        using vc_prems(1) substate_refl by auto
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(20) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(21) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(22) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(23) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(24) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(25) substate_refl apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(26) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(27) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(28) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(29) apply simp
      using vc_prems(1) ei(1) ei(30) by simp
    done
  done

end
          