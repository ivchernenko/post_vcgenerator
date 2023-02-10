theory Proof_1_5
  imports HandDryer VCTheoryLemmas Extra
begin


theorem proof_1_5:
"VC5 inv1 s0 hands_value"
  apply(simp only: VC5_def inv1_def R1_def dryer_def)
  apply(rule impI; rule conjI)
proof -
  assume VC: " ((toEnvP s0 \<and>
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
    drying \<and>
    getVarBool (setVarAny s0 hands_value) hands =
    ON \<and>
    \<not> 10 \<le> ltimeEnv
             (reset (setVarAny s0 hands_value) Ctrl)
             Ctrl"
  show " toEnvP
     (toEnv
       (reset (setVarAny s0 hands_value) Ctrl)) \<and>
    (\<forall>s1 s2.
        substate s1 s2 \<and>
        substate s2
         (toEnv
           (reset (setVarAny s0 hands_value)
             Ctrl)) \<and>
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
                 (reset (setVarAny s0 hands_value)
                   Ctrl)) \<and>
              toEnvNum s2 s4 \<le> hands \<and>
              getVarBool s4 (Suc (Suc 0)) = ON \<and>
              (\<forall>s3. toEnvP s3 \<and>
                    substate s2 s3 \<and>
                    substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                    getVarBool s3 hands = ON)))"
    apply(rule conjI)
     apply(simp)
  proof(rule allI; rule allI; rule impI)
    fix s1 s2
    assume req_prems: " substate s1 s2 \<and>
       substate s2
        (toEnv
                 (reset (setVarAny s0 hands_value)
                   Ctrl)) \<and>
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
                 (reset (setVarAny s0 hands_value)
                   Ctrl)) \<and>
            toEnvNum s2 s4 \<le> hands \<and>
            getVarBool s4 (Suc (Suc 0)) = ON \<and>
            (\<forall>s3. toEnvP s3 \<and>
                  substate s2 s3 \<and>
                  substate s3 s4 \<and>
                  s3 \<noteq> s4 \<longrightarrow>
                  getVarBool s3 hands = ON)"
    proof cases
      assume 1: "s2 =   (toEnv
                 (reset (setVarAny s0 hands_value)
                   Ctrl))"
      from VC obtain EI: "extraInv s0" by auto
      with extraInv_def VC have "0< ltimeEnv s0 Ctrl"
        by auto
      hence "ltimeEnv s0 Ctrl > 1 \<or> ltimeEnv s0 Ctrl = 1"
        by auto
      then have 3: "getVarBool s0 dryer = ON"
      proof
        assume 2: "hands < ltimeEnv s0 Ctrl"
        from EI extraInv_def VC 
        have "\<forall>s1. toEnvP s1 \<and>
       substate s1 s0 \<and>
       toEnvNum s1 s0 + hands < ltimeEnv s0 Ctrl \<longrightarrow>
       getVarBool s1 hands = OFF \<and>
       getVarBool s1 dryer = ON" by auto
        with 2 VC substate_refl toEnvNum_id 
        show ?thesis by auto
      next
        assume 2: "ltimeEnv s0 Ctrl = hands"
        from EI VC extraInv_def have "\<forall>s1. toEnvP s1 \<and>
       substate s1 s0 \<and>
       toEnvNum s1 s0 + hands = ltimeEnv s0 Ctrl \<longrightarrow>
       getVarBool s1 hands = ON \<and>
       getVarBool s1 dryer = ON" by auto
         with 2 VC substate_refl toEnvNum_id 
         show ?thesis by auto
       qed
       from req_prems 1 have 4: "substate s1 s0"
         by ( simp split: if_splits)
       from req_prems 1 have "toEnvNum s1 s0 = 0"
         by ( simp split: if_splits)
       with 4 substate_toEnvNum_id req_prems VC
       have "s1=s0" by blast
       with dryer_def req_prems 3 show ?thesis 
         by auto
    next
       assume 1: "s2 \<noteq>    (toEnv
                 (reset (setVarAny s0 hands_value)
                   Ctrl))"
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
                 (reset (setVarAny s0 hands_value)
                   Ctrl)) \<and>
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
    drying \<and>
    getVarBool (setVarAny s0 hands_value) hands =
    ON \<and>
    \<not> 10 \<le> ltimeEnv
             (reset (setVarAny s0 hands_value) Ctrl)
             Ctrl"
   with VC5_def extra5 show " extraInv
     (toEnv (reset (setVarAny s0 hands_value) Ctrl))"
     by auto
 qed
       
end