theory ExtraInv3_VC252
  imports ExtraInv3 VCTheoryLemmas
begin

abbreviation  s where "s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value \<equiv>
 (toEnv
       (setVarBool
         (setVarBool
           (setPstate
             (setVarBool
               (setVarBool
                 (setVarBool
                   (setVarBool (setVarBool (setVarBool s0 Init' fridgeTempGreaterMin_value) Init'begin' fridgeTempGreaterMax_value)
                     FridgeDoorController'closed' freezerTempGreaterMin_value)
                   FridgeDoorController'open' freezerTempGreaterMax_value)
                 FridgeDoorController'longOpen' fridgeDoor_value)
               lighting' OPEN')
             Init'begin' FridgeDoorController'open')
           FridgeCompressorController'checkTemp' OPEN')
         FreezerCompressorController'checkTemp' OPEN'))"

theorem extra_252: "VC252 extraInv env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC252_def extraInv_def)
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
       apply(rule allI)
      subgoal for s4 
        apply(cases "s4 = s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value")
         apply(rule impI)
         apply(rule allI)
        subgoal for s1
        apply(cases "s1 = s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value")
           apply(rule impI)
           apply(rule disjI2)
           apply(rule conjI)
            apply simp
           apply(rule allI)
          subgoal for s2
            using  substate_antisym[of s1 s2] vc_prems(1) substate_refl[of s0] ei(7) ei(1)
            by auto
          apply(insert ei(2))
          apply(erule allE[of _ s0])
          apply(erule impE)
          using ei(1) substate_refl vc_prems(1) apply simp
          apply(rule impI)
          apply(erule allE[of _ s1])
          apply(erule impE)
          apply(simp split: if_splits)
          apply(rule disjI1)
          apply(erule exE)
          subgoal for s3
            apply(rule exI[of _ s3])
            by simp
          done
        using ei(1) ei(3) by simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(4) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(5) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(6) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(7) apply simp
      apply(rule conjI)
      using vc_prems(1) ei(1) ei(7) ei(8) substate_refl apply simp
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
      using vc_prems(1) ei(1) ei(15) by simp
    done
  done

end
