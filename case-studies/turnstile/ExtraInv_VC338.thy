theory ExtraInv_VC338
  imports ExtraInv_new VCTheoryLemmas
begin

abbreviation s where " s s0 PdOut'value paid'value opened'value \<equiv>
 (toEnv
   (setPstate
     (setVarBool
       (setPstate
         (setVarBool
           (setPstate
             (setVarBool
               (setVarBool
                 (setVarBool (setVarBool (setVarBool s0 PdOut' PdOut'value) paid' paid'value) opened'
                   opened'value)
                 Controller'minimalOpened' True)
               EntranceController'isOpened' False)
             Init'init' Controller'minimalOpened')
           EntranceController'isClosed' True)
         Controller'isClosed' EntranceController'isOpened')
       Controller'isOpened' False)
     Controller'minimalOpened' STOP))"

theorem proof_4_338: "VC338 extraInv env s0 PdOut_value paid_value opened_value"
  apply(simp only: VC338_def extraInv_def)
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
      apply(rule allI)
      subgoal for s4
        apply(cases "s4 = s s0 PdOut_value paid_value opened_value")
         apply(rule impI)
         apply(rule allI)
        subgoal for s1
          apply(cases "s1 = s4")
           apply(rule impI)
           apply(rule disjI2)
           apply(rule conjI)
            apply simp
           apply(rule allI)
          subgoal for s2
            using substate_antisym[of s1 s2] ei(5) by auto
          apply(insert ei(10))
          apply(erule allE[of _ s0])
          apply(erule impE)
          using substate_refl apply simp
          apply(erule allE[of _ s1])
          apply(rule impI)
          apply(erule impE)
           apply(simp split: if_splits)
          apply(rule disjI1)
          apply(erule exE)
          subgoal for s3
            apply(rule exI[of _ s3])
            by simp
          done
        using ei(12) by simp
      apply(rule conjI)
      using ei(13) apply simp
      using ei(14) by simp
    done
  done

end
