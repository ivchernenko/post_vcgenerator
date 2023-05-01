theory Proof_R3_VC277
  imports ExtraInv3_VC277
begin

definition inv3 where "inv3 s0 \<equiv> R3 s0 \<and> extraInv s0"

abbreviation s where "s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value \<equiv>
 (toEnv
       (setVarBool
         (setVarBool
           (setVarBool
             (setVarBool
               (setVarBool (setVarBool (setVarBool s0 Init' fridgeTempGreaterMin_value) Init'begin' fridgeTempGreaterMax_value)
                 FridgeDoorController'closed' freezerTempGreaterMin_value)
               FridgeDoorController'open' freezerTempGreaterMax_value)
             FridgeDoorController'longOpen' fridgeDoor_value)
           FridgeCompressorController'checkTemp' OPEN')
         FreezerCompressorController'checkTemp' OPEN'))"

theorem proof_3_277: "VC277 inv3 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC277_def inv3_def R3_def)
  apply(rule impI)
   apply(rule cut_rl[of "extraInv (s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value)"])
   apply(rule conjI)
    apply(rule conjI)
     apply simp
   apply(erule conjE)
    apply(erule conjE)
   apply((rule allI)+)
  subgoal premises vc_prems for s1
    apply(insert vc_prems(3))
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
    subgoal premises req_prems
      apply(insert vc_prems(1))
      apply(unfold extraInv_def)
      apply((erule conjE)+)
      subgoal premises extraInvs
        apply(insert extraInvs(2))
        apply(erule allE[of _ " (s s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value freezerTempGreaterMax_value
            fridgeDoor_value)"])
        apply(erule impE)
        using vc_prems(2) apply simp
        apply(erule allE[of _ s1])
        using req_prems by simp
      done
    done
  done
  using extra_277 by (auto simp add: VC277_def)

end
