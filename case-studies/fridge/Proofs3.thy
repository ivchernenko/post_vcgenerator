theory Proofs3
  imports ExtraInv VCTheoryLemmas
begin

definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"

thm extraInv_def

definition pred3 where "pred3 s1 s s5 \<equiv>
 substate s1 s5 \<and> substate s5 s \<and>
      toEnvP s1 \<and> toEnvP s5 \<and> OPEN_DOOR_TIME_LIMIT'TIMEOUT = toEnvNum s1 s \<and> getVarBool s1 fridgeDoor' = OPEN' \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s5 \<and> s2 \<noteq> s5 \<longrightarrow>
 \<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN')  \<longrightarrow>
      (\<exists>s3. toEnvP s3 \<and>
            substate s1 s3 \<and>
            substate s3 s \<and>
            toEnvNum s1 s3 \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and>
            (getVarBool s3 doorSignal' \<or> getVarBool s3 fridgeDoor' = CLOSED') \<and>
            (\<forall>s2. toEnvP s2 \<and> substate s5 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow>
                  \<not> getVarBool s2 doorSignal' \<and> getVarBool s2 fridgeDoor' = OPEN'))"

lemma open_R3: "substate s1 s0 \<and> toEnvP s1 \<and> toEnvP s0 \<and> toEnvNum s1 s0 = OPEN_DOOR_TIME_LIMIT'TIMEOUT - 1 \<and>
 getVarBool s1 fridgeDoor' = OPEN' \<and> getPstate s0 FridgeDoorController' = FridgeDoorController'open' \<and>
 ltime s0 FridgeDoorController' < OPEN_DOOR_TIME_LIMIT'TIMEOUT \<and> substate s0 s \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'begin' = FridgeDoorController'closed' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          ( (getPstate s2 Init' = Init'begin' \<or>getPstate s2 Init'begin' = FridgeDoorController'open' \<or>
 getPstate s2 Init'begin' = FridgeDoorController'longOpen') \<and>
           getVarBool s3 FridgeDoorController'longOpen' = CLOSED') \<and>
          (\<forall>s4. toEnvP s4 \<and> substate s3 s4 \<and> substate s4 s1 \<longrightarrow> getPstate s4 Init'begin' = FridgeDoorController'closed') \<and>
          (\<forall>s5. toEnvP s5 \<and> substate s3 s5 \<and> substate s5 s1 \<and> s3 \<noteq> s5 \<longrightarrow>
                getVarBool s5 FridgeDoorController'longOpen' = CLOSED'))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'begin' = FridgeDoorController'open' \<longrightarrow>
      ltime s1 Init'begin' \<le> OPEN_DOOR_TIME_LIMIT'TIMEOUT) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Init'begin' = FridgeDoorController'open' \<longrightarrow>
      (\<exists>s2 s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s1 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s1 = ltime s1 Init'begin' \<and>
          getPstate s2 Init'begin' = FridgeDoorController'closed' \<and> getVarBool s3 FridgeDoorController'longOpen' = OPEN')) \<and>
(\<forall>s3. toEnvP s3 \<and> substate s3 s \<and> getPstate s3 Init'begin' = FridgeDoorController'open' \<longrightarrow>
      (\<forall>s1. toEnvP s1 \<and> substate s1 s3 \<and> toEnvNum s1 s3 < ltime s3 Init'begin' \<longrightarrow>
            getPstate s1 Init'begin' = FridgeDoorController'open') \<and>
      (\<forall>s2. toEnvP s2 \<and> substate s2 s3 \<and> toEnvNum s2 s3 + 1 < ltime s3 Init'begin' \<longrightarrow>
            getVarBool s2 FridgeDoorController'longOpen' \<noteq> CLOSED'))  \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s0 \<and> (getVarBool s2 doorSignal' \<or> getVarBool s2 fridgeDoor' = CLOSED'))"
  apply(rule impI)
  apply(rule exE[of "(\<lambda> s2. \<exists> s3.
          toEnvP s2 \<and>
          toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s0 \<and>
          toEnvNum s2 s3 = 1 \<and>
          toEnvNum s2 s0 = ltime s0 Init'begin' \<and>
          getPstate s2 Init'begin' = FridgeDoorController'closed' \<and> getVarBool s3 FridgeDoorController'longOpen' = OPEN')"])
   apply blast
  apply(erule exE)
  subgoal for s2 s3
    apply(rule cut_rl[of "substate s1 s2"])
     apply(rule exI[of _ s2])
     apply(rule cut_rl[of "substate s2 s"])
    apply(rule cut_rl[of "\<exists>s4 s5.
              toEnvP s4 \<and>
              substate s4 s5 \<and>
              substate s5 s2 \<and>
              toEnvNum s4 s5 = 1 \<and>
              (
               (getPstate s4 Init' = Init'begin' \<or> getPstate s4 Init'begin' = FridgeDoorController'open' \<or>
                getPstate s4 Init'begin' = FridgeDoorController'longOpen') \<and>
               getVarBool s5 FridgeDoorController'longOpen' = CLOSED') \<and>
              (\<forall>s6. toEnvP s6 \<and> substate s5 s6 \<and> substate s6 s2 \<longrightarrow> getPstate s6 Init'begin' = FridgeDoorController'closed') \<and>
              (\<forall>s7. toEnvP s7 \<and> substate s5 s7 \<and> substate s7 s2 \<and> s5 \<noteq> s7 \<longrightarrow>
                    getVarBool s7 FridgeDoorController'longOpen' = CLOSED')"])
       apply (metis substate_refl substate_trans)
      apply blast
    using substate_trans
     apply meson
    apply(rule toEnvNum_le_imp_substate[of s1 s0 s2])
    using substate_trans[of s2 s3 s0] by arith
  done

theorem proof_3_1: "VC1 inv3 s0"
  apply(unfold VC1_def inv3_def R3_def extraInv_def)
  apply auto
  done

end
