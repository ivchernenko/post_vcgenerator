theory Proof_1_2
  imports HandDryer VCTheoryLemmas Extra
begin


theorem proof_1_2:
"VC2 inv1 s0 hands_value"
  apply(simp only: VC2_def inv1_def R1_def dryer_def)
  apply(rule impI; rule conjI)
proof -
  assume VC: "((toEnvP s0 \<and>
      (\<forall>s1 s2.
          substate s1 s2 \<and>
          substate s2 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvNum s1 s2 = hands \<and>
          getVarBool s1 hands = OFF \<and>
          getVarBool s1 (Suc (Suc 0)) = OFF \<and>
          getVarBool s2 hands = ON \<longrightarrow>
          (\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> hands \<and>
                getVarBool s4 (Suc (Suc 0)) = ON \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 hands = ON)))) \<and>
     extraInv s0) \<and>
    env (setVarAny s0 hands_value) hands_value \<and>
    getPstate (setVarAny s0 hands_value) Ctrl =
    waiting \<and>
    getVarBool (setVarAny s0 hands_value) hands =
    ON"
  show " toEnvP
     (toEnv
       (setPstate
         (setVarBool (setVarAny s0 hands_value)
           (Suc (Suc 0)) ON)
         Ctrl drying)) \<and>
    (\<forall>s1 s2.
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (setPstate
             (setVarBool (setVarAny s0 hands_value)
               (Suc (Suc 0)) ON)
             Ctrl drying)) \<and>
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        toEnvNum s1 s2 = hands \<and>
        getVarBool s1 hands = OFF \<and>
        getVarBool s1 (Suc (Suc 0)) = OFF \<and>
        getVarBool s2 hands = ON \<longrightarrow>
        (\<exists>s4. toEnvP s4 \<and>
              substate s2 s4 \<and>
              substate s4
               (toEnv
                 (setPstate
                   (setVarBool
                     (setVarAny s0 hands_value)
                     (Suc (Suc 0)) ON)
                   Ctrl drying)) \<and>
              toEnvNum s2 s4 \<le> hands \<and>
              getVarBool s4 (Suc (Suc 0)) = ON \<and>
              (\<forall>s3. toEnvP s3 \<and>
                    substate s2 s3 \<and>
                    substate s3 s4 \<and>
                    s3 \<noteq> s4 \<longrightarrow>
                    getVarBool s3 hands = ON)))"
    apply(rule conjI)
     apply(simp)
  proof(rule allI; rule allI; rule impI)
    fix s1 s2
    assume req_prems: " substate s1 s2 \<and>
       substate s2
        (toEnv
          (setPstate
            (setVarBool (setVarAny s0 hands_value)
              (Suc (Suc 0)) ON)
            Ctrl drying)) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = hands \<and>
       getVarBool s1 hands = OFF \<and>
       getVarBool s1 (Suc (Suc 0)) = OFF \<and>
       getVarBool s2 hands = ON "
    show " \<exists>s4. toEnvP s4 \<and>
            substate s2 s4 \<and>
            substate s4
             (toEnv
               (setPstate
                 (setVarBool
                   (setVarAny s0 hands_value)
                   (Suc (Suc 0)) ON)
                 Ctrl drying)) \<and>
            toEnvNum s2 s4 \<le> hands \<and>
            getVarBool s4 (Suc (Suc 0)) = ON \<and>
            (\<forall>s3. toEnvP s3 \<and>
                  substate s2 s3 \<and>
                  substate s3 s4 \<and>
                  s3 \<noteq> s4 \<longrightarrow>
                  getVarBool s3 hands = ON)"
    proof cases
      assume 1: "s2 = (toEnv
                     (setPstate
                       (setVarBool
                         (setVarAny s0 hands_value)
                         (Suc (Suc 0)) ON)
                       Ctrl drying))"
      have " (toEnvP s2 \<and>
         substate s2 s2 \<and>
         substate s2
          (toEnv
            (setPstate
              (setVarBool (setVarAny s0 hands_value)
                (Suc (Suc 0)) ON)
              Ctrl drying)) \<and>
         toEnvNum s2 s2 \<le> hands \<and>
         getVarBool s2 (Suc (Suc 0)) = ON) \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate s2 s3 \<and>
               substate s3 s2 \<and>
               s3 \<noteq> s2 \<longrightarrow>
               getVarBool s3 hands = ON)"
      proof
        from 1 show "toEnvP s2 \<and>
    substate s2 s2 \<and>
    substate s2
     (toEnv
       (setPstate
         (setVarBool (setVarAny s0 hands_value)
           (Suc (Suc 0)) ON)
         Ctrl drying)) \<and>
    toEnvNum s2 s2 \<le> hands \<and>
    getVarBool s2 (Suc (Suc 0)) = ON" by auto
      next
        from substate_asym show " \<forall>s3. toEnvP s3 \<and>
         substate s2 s3 \<and>
         substate s3 s2 \<and> s3 \<noteq> s2 \<longrightarrow>
         getVarBool s3 hands = ON"
          by auto
      qed
      thus ?thesis by blast
    next
       assume 1: "s2 \<noteq> (toEnv
                     (setPstate
                       (setVarBool
                         (setVarAny s0 hands_value)
                         (Suc (Suc 0)) ON)
                       Ctrl drying))"
       with req_prems have 2: "substate s2 s0" 
         by (simp split: if_splits)
       from VC req_prems 2 obtain "\<exists>s4. toEnvP s4 \<and>
           substate s2 s4 \<and>
           substate s4 s0 \<and>
           toEnvNum s2 s4 \<le> hands \<and>
           getVarBool s4 (Suc (Suc 0)) = ON \<and>
           (\<forall>s3. toEnvP s3 \<and>
                 substate s2 s3 \<and>
                 substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                 getVarBool s3 hands = ON)"by auto
       then obtain s4 where 3: "toEnvP s4 \<and>
           substate s2 s4 \<and>
           substate s4 s0 \<and>
           toEnvNum s2 s4 \<le> hands \<and>
           getVarBool s4 (Suc (Suc 0)) = ON \<and>
           (\<forall>s3. toEnvP s3 \<and>
                 substate s2 s3 \<and>
                 substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                 getVarBool s3 hands = ON)" ..
       have "toEnvP s4 \<and>
      substate s2 s4 \<and>
      substate s4
       (toEnv
         (setPstate
           (setVarBool (setVarAny s0 hands_value)
             (Suc (Suc 0)) ON)
           Ctrl drying)) \<and>
      toEnvNum s2 s4 \<le> hands \<and>
      getVarBool s4 (Suc (Suc 0)) = ON \<and>
      (\<forall>s3. toEnvP s3 \<and>
            substate s2 s3 \<and>
            substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
            getVarBool s3 hands = ON)"
         using 3 by auto
       thus ?thesis ..
     qed
   qed
     next
assume VC: "((toEnvP s0 \<and>
      (\<forall>s1 s2.
          substate s1 s2 \<and>
          substate s2 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvNum s1 s2 = hands \<and>
          getVarBool s1 hands = OFF \<and>
          getVarBool s1 (Suc (Suc 0)) = OFF \<and>
          getVarBool s2 hands = ON \<longrightarrow>
          (\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> hands \<and>
                getVarBool s4 (Suc (Suc 0)) = ON \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 hands = ON)))) \<and>
     extraInv s0) \<and>
    env (setVarAny s0 hands_value) hands_value \<and>
    getPstate (setVarAny s0 hands_value) Ctrl =
    waiting \<and>
    getVarBool (setVarAny s0 hands_value) hands =
    ON"
  with extra2 show " extraInv
     (toEnv
       (setPstate
         (setVarBool (setVarAny s0 hands_value)
           (Suc (Suc 0)) ON)
         Ctrl drying))"
    by (auto simp add: VC2_def dryer_def)
qed

end