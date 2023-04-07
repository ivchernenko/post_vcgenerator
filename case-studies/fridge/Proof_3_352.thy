theory Proof_3_352
  imports Proofs3
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
               doorSignal' OPEN')
             Init'begin' FridgeDoorController'longOpen')
           FridgeCompressorController'checkTemp' OPEN')
         FreezerCompressorController'checkTemp' OPEN'))"

theorem proof_3_352: "VC352 inv3 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC352_def inv3_def R3_def)
 apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply simp
   apply(unfold extraInv_def)[1]
   apply(erule conjE)
   apply(erule conjE)
   apply((rule allI)+)
  subgoal premises vc_prems for s1
    apply(insert vc_prems(2))
    apply(erule conjE)
    subgoal premises invs0
      apply(rule impI)
      apply((erule conjE)+)
      apply(erule le_imp_less_or_eq[THEN disjE])
      apply(rule cut_rl[of " \<exists>s3. toEnvP s3 \<and>
         substate s1 s3 \<and>
         substate s3 s0 \<and>
         toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
         (getVarBool s3 doorSignal' \<or> getVarBool s3 FridgeDoorController'longOpen' = CLOSED') \<and>
         (\<forall>s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow>
               \<not> getVarBool s2 doorSignal' \<and> getVarBool s2 FridgeDoorController'longOpen' = OPEN')"])
      apply(erule exE)
    subgoal for s4
      apply(rule exI[of _ s4])
      by simp
     apply(insert invs0(1))[1]
     apply(erule conjE)
     apply(erule allE[of _ s1])
     apply(simp split: if_splits)
apply(rule cut_rl[of "\<forall> s5. toEnvP s5 \<and> substate s1 s5 \<and> substate s5 (s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value) \<longrightarrow>
pred3 s1 (s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value) s5"])
     apply(erule allE[of _ s1])
     apply(erule impE)
    using substate_refl apply blast
     apply(unfold pred3_def)
     apply(erule impE)
      apply(insert substate_refl substate_trans substate_antisym)[1]
    apply blast
     apply assumption
      apply(rule allI)
      subgoal premises prems for s5
        apply(induction rule: state_ind)
        using prems apply simp
         apply(rule impI)

        apply(rule exI[of _ "(s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value freezerTempGreaterMax_value
       fridgeDoor_value)"])
        apply(insert vc_prems(1))
         apply(((rule conjI),(simp split: if_splits))+)
        using substate_trans substate_antisym apply blast

      subgoal for s5
          apply(rule impI)
          apply(cases " (getVarBool (predEnv s5) doorSignal' \<or> getVarBool (predEnv s5) FridgeDoorController'longOpen' = CLOSED')")
           apply(rule exI[of _ "predEnv s5"])
           apply(rule conjI)
        apply(rule toEnvP_substate_pred_imp_toEnvP_pred[of s1])
           apply blast
      apply(rule conjI)
          using substate_refl apply simp
       apply(rule conjI)
      using predEnv_substate substate_trans apply blast
       apply(rule conjI)
      using toEnvNum3[of s1 "predEnv s5"
 "(s s0  fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value) "]
      using prems(4) apply fastforce
             apply(rule conjI)
        apply blast
      using substate_antisym apply blast
      apply(drule impE)
        prefer 3
        apply assumption
       apply(((rule conjI),blast)+)
      using substate_imp_substatete_predEnv_or_eq apply blast
      apply(drule exE)
       prefer 2
       apply assumption
      subgoal for s4
        apply(rule exI[of _ s4])
       apply(rule conjI)
         apply blast
        apply(rule conjI)
        using predEnv_substate substate_trans apply blast
        apply(((rule conjI),blast)+)
        using predEnv_substate_imp_substate_or_eq
        by (smt (z3) substate_trans)
      done
    done
  done
  done
