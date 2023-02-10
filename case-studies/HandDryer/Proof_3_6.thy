theory Proof_3_6
  imports HandDryer VCTheoryLemmas Extra
begin

theorem proof_3_6:
"VC6 inv3 s0 hands_value"
  apply(simp only: VC6_def inv3_def  R3_def 
  dryer_def)
  apply(rule impI)
  apply(rule conjI)
   apply(rule conjI)
    apply(simp)
proof -
  define s:: state where
"s =(toEnv
          (setPstate (setVarAny s0 hands_value) Ctrl
            waiting))"
  assume VC: "   ((toEnvP s0 \<and>
      (\<forall>s1 s2.
          substate s1 s2 \<and>
          substate s2 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvNum s1 s2 = hands \<and>
          10 \<le> toEnvNum s2 s0 \<and>
          getVarBool s1 hands = ON \<and>
          getVarBool s1 (Suc (Suc 0)) = ON \<and>
          getVarBool s2 hands = OFF \<longrightarrow>
          (\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> 10 \<and>
                (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
                 getVarBool s4 hands = ON) \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 (Suc (Suc 0)) =
                      ON \<and>
                      getVarBool s3 hands =
                      OFF)))) \<and>
     extraInv s0) \<and>
    env (setVarAny s0 hands_value) hands_value \<and>
    getPstate (setVarAny s0 hands_value) Ctrl =
    drying \<and>
    getVarBool (setVarAny s0 hands_value) hands \<noteq>
    ON \<and>
    10 \<le> ltimeEnv (setVarAny s0 hands_value)
           Ctrl"
  show "\<forall>s1 s2.
       substate s1 s2 \<and>
       substate s2
        (toEnv
          (setPstate (setVarAny s0 hands_value) Ctrl
            waiting)) \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = hands \<and>
       10 \<le> toEnvNum s2
              (toEnv
                (setPstate (setVarAny s0 hands_value)
                  Ctrl waiting)) \<and>
       getVarBool s1 hands = ON \<and>
       getVarBool s1 (Suc (Suc 0)) = ON \<and>
       getVarBool s2 hands = OFF \<longrightarrow>
       (\<exists>s4. toEnvP s4 \<and>
             substate s2 s4 \<and>
             substate s4
              (toEnv
                (setPstate (setVarAny s0 hands_value)
                  Ctrl waiting)) \<and>
             toEnvNum s2 s4 \<le> 10 \<and>
             (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
              getVarBool s4 hands = ON) \<and>
             (\<forall>s3. toEnvP s3 \<and>
                   substate s2 s3 \<and>
                   substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                   getVarBool s3 (Suc (Suc 0)) =
                   ON \<and>
                   getVarBool s3 hands = OFF))"
    apply(simp only: s_def[symmetric])
  proof(rule allI; rule allI; rule impI)
    fix s1 s2
    assume req_prems: "substate s1 s2 \<and>
       substate s2 s \<and>
       toEnvP s1 \<and>
       toEnvP s2 \<and>
       toEnvNum s1 s2 = hands \<and>
       10 \<le> toEnvNum s2 s \<and>
       getVarBool s1 hands = ON \<and>
       getVarBool s1 (Suc (Suc 0)) = ON \<and>
       getVarBool s2 hands = OFF"
    then obtain "10 \<le> toEnvNum s2 s" by auto
    from le_imp_less_or_eq[OF this]
    show " \<exists>s4. toEnvP s4 \<and>
            substate s2 s4 \<and>
            substate s4 s \<and>
            toEnvNum s2 s4 \<le> 10 \<and>
            (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
             getVarBool s4 hands = ON) \<and>
            (\<forall>s3. toEnvP s3 \<and>
                  substate s2 s3 \<and>
                  substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                  getVarBool s3 (Suc (Suc 0)) = ON \<and>
                  getVarBool s3 hands = OFF)"
    proof
      assume 1: "10 < toEnvNum s2 s"
      with req_prems substate_eq_or_predEnv
 toEnvNum_id s_def  have 2: "substate s2 s0" 
        by (simp add: s_def split: if_splits)
      from VC obtain "\<forall>s1 s2.
          substate s1 s2 \<and>
          substate s2 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvNum s1 s2 = hands \<and>
          10 \<le> toEnvNum s2 s0 \<and>
          getVarBool s1 hands = ON \<and>
          getVarBool s1 (Suc (Suc 0)) = ON \<and>
          getVarBool s2 hands = OFF \<longrightarrow>
          (\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> 10 \<and>
                (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
                 getVarBool s4 hands = ON) \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 (Suc (Suc 0)) =
                      ON \<and>
                      getVarBool s3 hands =
                      OFF))"
        by auto
      with req_prems 1 2 have "\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> 10 \<and>
                (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
                 getVarBool s4 hands = ON) \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 (Suc (Suc 0)) =
                      ON \<and>
                      getVarBool s3 hands =
                      OFF)"
        by (auto simp add: s_def split: if_splits)
      then obtain s4 where 3: " toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> 10 \<and>
                (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
                 getVarBool s4 hands = ON) \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 (Suc (Suc 0)) =
                      ON \<and>
                      getVarBool s3 hands =
                      OFF)" ..
      have  "(toEnvP s4 \<and>
      substate s2 s4 \<and>
      substate s4 s \<and>
      toEnvNum s2 s4 \<le> 10 \<and>
      (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
       getVarBool s4 hands = ON)) \<and>
      (\<forall>s3. toEnvP s3 \<and>
            substate s2 s3 \<and>
            substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
            getVarBool s3 (Suc (Suc 0)) = ON \<and>
            getVarBool s3 hands = OFF)"
      proof
        from 3 show "toEnvP s4 \<and>
      substate s2 s4 \<and>
      substate s4 s \<and>
      toEnvNum s2 s4 \<le> 10 \<and>
      (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
       getVarBool s4 hands = ON)" 
          by (simp add: s_def)
      next
        from 3 show "\<forall>s3. toEnvP s3 \<and>
         substate s2 s3 \<and>
         substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
         getVarBool s3 (Suc (Suc 0)) = ON \<and>
         getVarBool s3 hands = OFF"
          by simp
      qed
      thus ?thesis by auto
    next
      assume 4: "10 = toEnvNum s2 s"
      from substate_asym have 5:
"\<forall>s3. toEnvP s3 \<and>
               substate s2 s3 \<and>
               substate s3 s2 \<and> s3 \<noteq> s2 \<longrightarrow>
               getVarBool s3 (Suc (Suc 0)) = ON \<and>
               getVarBool s3 hands = OFF"
        by auto
      show ?thesis
      proof -
        define s5:: state where "s5=s2"
        have "toEnvP s5 \<and> substate s2 s5 \<and>
substate s5 s \<longrightarrow>pred3 s2 s s5" 
        proof(induction rule: state_down_ind)
          case 1
          then show ?case 
            using req_prems s_def by auto
        next
          case 2
          then show ?case 
            apply(simp only: pred3_def)
          proof
            assume 6: " \<forall>s3. toEnvP s3 \<and>
         substate s2 s3 \<and>
         substate s3 s \<and> s3 \<noteq> s \<longrightarrow>
         getVarBool s3 (Suc (Suc 0)) = ON \<and>
         getVarBool s3 hands = OFF"
            from VC have "\<exists> s3. ~ (toEnvP s3 \<and>
         substate s2 s3 \<and>
         substate s3 s \<and> s3 \<noteq> s \<longrightarrow>
         getVarBool s3 (Suc (Suc 0)) = ON \<and>
         getVarBool s3 hands = OFF)"
              apply(simp only: extraInv_def)
            proof -
              assume "((toEnvP s0 \<and>
      (\<forall>s1 s2.
          substate s1 s2 \<and>
          substate s2 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvNum s1 s2 = hands \<and>
          10 \<le> toEnvNum s2 s0 \<and>
          getVarBool s1 hands = ON \<and>
          getVarBool s1 (Suc (Suc 0)) = ON \<and>
          getVarBool s2 hands = OFF \<longrightarrow>
          (\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> 10 \<and>
                (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
                 getVarBool s4 hands = ON) \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 (Suc (Suc 0)) =
                      ON \<and>
                      getVarBool s3 hands =
                      OFF)))) \<and>
     toEnvP s0 \<and>
     (getPstate s0 Ctrl = drying \<longrightarrow>
      0 < ltimeEnv s0 Ctrl \<and>
      ltimeEnv s0 Ctrl \<le> 10 \<and>
      (\<forall>s1. toEnvP s1 \<and>
            substate s1 s0 \<and>
            toEnvNum s1 s0 + hands =
            ltimeEnv s0 Ctrl \<longrightarrow>
            getVarBool s1 hands = ON \<and>
            getVarBool s1 dryer = ON) \<and>
      (\<forall>s1. toEnvP s1 \<and>
            substate s1 s0 \<and>
            toEnvNum s1 s0 + hands
            < ltimeEnv s0 Ctrl \<longrightarrow>
            getVarBool s1 hands = OFF \<and>
            getVarBool s1 dryer = ON)) \<and>
     (\<forall>s1. toEnvP s1 \<and> substate s1 s0 \<longrightarrow>
           getPstate s1 Ctrl = waiting \<or>
           getPstate s1 Ctrl = drying)) \<and>
    env (setVarAny s0 hands_value) hands_value \<and>
    getPstate (setVarAny s0 hands_value) Ctrl =
    drying \<and>
    getVarBool (setVarAny s0 hands_value) hands \<noteq>
    ON \<and>
    10 \<le> ltimeEnv (setVarAny s0 hands_value)
           Ctrl"
              then obtain 7:
 " 0 < ltimeEnv s0 Ctrl \<and> ltimeEnv s0 Ctrl \<le> 10 \<and>
(\<forall>s1. toEnvP s1 \<and>
            substate s1 s0 \<and>
            toEnvNum s1 s0 + hands =
            ltimeEnv s0 Ctrl \<longrightarrow>
            getVarBool s1 hands = ON \<and>
            getVarBool s1 dryer = ON)" by auto
              from shiftEnv_substate have 8:
"substate (shiftEnv s0 (ltimeEnv s0 Ctrl - 1)) s0"
                by auto
from VC obtain  9: "toEnvP s0" by auto
            from 7 obtain 10:
 "0 < ltimeEnv s0 Ctrl" by auto
            from 9 10 ltime_le_toEnvNum[of s0 Ctrl]
shift_spec have 11: "toEnvP (shiftEnv s0 (ltimeEnv s0 Ctrl - 1))"
              by auto
              have
"toEnvNum (shiftEnv s0 (ltimeEnv s0 Ctrl - 1)) s0
+ 1 = ltimeEnv s0 Ctrl"
              proof -
                from VC obtain  9: "toEnvP s0" by auto
            from 7 obtain 10:
 "0 < ltimeEnv s0 Ctrl" by auto
                with 9 10 ltime_le_toEnvNum[of s0 Ctrl] 
toEnvNum_shift show ?thesis 
                  by auto
              qed
              with 7 8 11 have 12:
"getVarBool (shiftEnv s0 (ltimeEnv s0 Ctrl - 1)) 
hands = ON \<and>
 getVarBool (shiftEnv s0 (ltimeEnv s0 Ctrl - 1))
dryer = ON" by auto
              have 13:"substate s2 (shiftEnv s0 (ltimeEnv s0 Ctrl - 1))"
              proof -
                from 4 req_prems substate_eq_or_predEnv
 toEnvNum_id s_def  have 2: "substate s2 s0" 
                  by (simp add: s_def split: if_splits)
                from 7 obtain 14: "ltimeEnv s0 Ctrl \<le> 10" by auto
      from req_prems obtain "toEnvP s2"
        by auto
                with 2 9 10 4 14  substate_shift[of s2 s0 "ltimeEnv s0 Ctrl - 1"]
                show ?thesis 
                  by (auto simp add: s_def split: if_splits)
              qed
              have 14: "substate (shiftEnv s0 (ltimeEnv s0 Ctrl - hands)) s0"
                using shiftEnv_substate by auto
              have 15: "substate s0 s" using substate_refl
                by (auto simp add: s_def)
              with 14 have 16:  "substate (shiftEnv s0 (ltimeEnv s0 Ctrl - hands)) s"
                using substate_trans by blast
              have  " (shiftEnv s0 (ltimeEnv s0 Ctrl - hands)) \<noteq> s"
              proof
                assume "shiftEnv s0 (ltimeEnv s0 Ctrl - hands) = s"
                with shiftEnv_substate
                have "substate s s0" by auto
                with 15 substate_asym 
                have "s0 = s" by auto
                with s_def show False by auto
              qed
              with 11 12 13 16 show ?thesis
                by auto
            qed
            with 6 show " \<exists>s4. toEnvP s4 \<and>
         substate s s4 \<and>
         substate s4 s \<and>
         toEnvNum s2 s4 \<le> 10 \<and>
         (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
          getVarBool s4 hands = ON) \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate s s3 \<and>
               substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 (Suc (Suc 0)) = ON \<and>
               getVarBool s3 hands = OFF)" by auto
          qed              
        next
          case (3 s5)
          then show ?case 
            apply(simp only: pred3_def)
          proof
            from 3(3) have  6: " (\<forall>s3. toEnvP s3 \<and>
          substate s2 s3 \<and>
          substate s3 s5 \<and> s3 \<noteq> s5 \<longrightarrow>
          getVarBool s3 (Suc (Suc 0)) = ON \<and>
          getVarBool s3 hands = OFF) \<Longrightarrow>
    (\<exists>s4. toEnvP s4 \<and>
          substate s5 s4 \<and>
          substate s4 s \<and>
          toEnvNum s2 s4 \<le> 10 \<and>
          (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
           getVarBool s4 hands = ON) \<and>
          (\<forall>s3. toEnvP s3 \<and>
                substate s5 s3 \<and>
                substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                getVarBool s3 (Suc (Suc 0)) = ON \<and>
                getVarBool s3 hands = OFF)) "
              by (auto simp add: pred3_def)
            assume 7: " \<forall>s3. toEnvP s3 \<and>
         substate s2 s3 \<and>
         substate s3 (predEnv s5) \<and>
         s3 \<noteq> predEnv s5 \<longrightarrow>
         getVarBool s3 (Suc (Suc 0)) = ON \<and>
         getVarBool s3 hands = OFF"
            show "\<exists>s4. toEnvP s4 \<and>
         substate (predEnv s5) s4 \<and>
         substate s4 s \<and>
         toEnvNum s2 s4 \<le> 10 \<and>
         (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
          getVarBool s4 hands = ON) \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate (predEnv s5) s3 \<and>
               substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
               getVarBool s3 (Suc (Suc 0)) = ON \<and>
               getVarBool s3 hands = OFF)"
            proof cases
              assume 10: "(getVarBool (predEnv s5) (Suc (Suc 0)) = OFF \<or>
          getVarBool (predEnv s5) hands = ON)"
              from predEnv_substate 3 
substate_trans have 8:  "substate (predEnv s5) s"
                by blast
              from 3(2) substate_eq_or_predEnv req_prems 
              have 9: "substate s2 (predEnv s5)" 
                by auto
              have "toEnvP (predEnv s5) \<and>
         substate (predEnv s5) (predEnv s5) \<and>
         substate (predEnv s5) s \<and>
         toEnvNum s2 (predEnv s5) \<le> 10 \<and>
         (getVarBool (predEnv s5) (Suc (Suc 0)) = OFF \<or>
          getVarBool (predEnv s5) hands = ON) \<and>
         (\<forall>s3. toEnvP s3 \<and>
               substate (predEnv s5) s3 \<and>
               substate s3 (predEnv s5) \<and>
 s3 \<noteq> (predEnv s5) \<longrightarrow>
               getVarBool s3 (Suc (Suc 0)) = ON \<and>
               getVarBool s3 hands = OFF)"
              proof -
                from predEnvP_or_emptyState[of s5]
                have "toEnvP (predEnv s5)"
                proof      
                  assume "toEnvP (predEnv s5)"
                  thus ?thesis by assumption
                next
                  assume   "predEnv s5 = emptyState"
                  with 9 req_prems show ?thesis
                    by (cases s2; auto)
                qed
                moreover from substate_refl have
" substate (predEnv s5) (predEnv s5)" by auto
                moreover from 8 
                have "substate (predEnv s5) s"
                  by assumption
                moreover from 4 8 9 toEnvNum3
                have "toEnvNum s2 (predEnv s5) \<le> 10"
                  by auto
                moreover from 10
                have "(getVarBool (predEnv s5) (Suc (Suc 0)) = OFF \<or>
     getVarBool (predEnv s5) hands = ON)"
                  by assumption
                moreover from substate_asym
                have "\<forall>s3. toEnvP s3 \<and>
          substate (predEnv s5) s3 \<and>
          substate s3 (predEnv s5) \<and>
          s3 \<noteq> predEnv s5 \<longrightarrow>
          getVarBool s3 (Suc (Suc 0)) = ON \<and>
          getVarBool s3 hands = OFF" by auto
                ultimately show ?thesis by auto
              qed
              thus ?thesis by auto
            next
              assume 10: "\<not> (getVarBool (predEnv s5) (Suc (Suc 0)) = OFF \<or>
        getVarBool (predEnv s5) hands = ON)"
              with substate_eq_or_predEnv 7
              have " \<forall>s3. toEnvP s3 \<and>
         substate s2 s3 \<and>
         substate s3  s5 \<and>
         s3 \<noteq> s5 \<longrightarrow>
         getVarBool s3 (Suc (Suc 0)) = ON \<and>
         getVarBool s3 hands = OFF"
                by auto
              from 6[OF this] obtain s4 where 11:
"toEnvP s4 \<and>
       substate s5 s4 \<and>
       substate s4 s \<and>
       toEnvNum s2 s4 \<le> 10 \<and>
       (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
        getVarBool s4 hands = ON) \<and>
       (\<forall>s3. toEnvP s3 \<and>
             substate s5 s3 \<and>
             substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
             getVarBool s3 (Suc (Suc 0)) = ON \<and>
             getVarBool s3 hands = OFF)" ..
              have "(toEnvP s4 \<and>
      substate (predEnv s5) s4 \<and>
      substate s4 s \<and>
      toEnvNum s2 s4 \<le> 10 \<and>
      (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
       getVarBool s4 hands = ON)) \<and>
      (\<forall>s3. toEnvP s3 \<and>
            substate (predEnv s5) s3 \<and>
            substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
            getVarBool s3 (Suc (Suc 0)) = ON \<and>
            getVarBool s3 hands = OFF)" 
              proof
                from 11 predEnv_substate substate_trans 
                show "toEnvP s4 \<and>
      substate (predEnv s5) s4 \<and>
      substate s4 s \<and>
      toEnvNum s2 s4 \<le> 10 \<and>
      (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
       getVarBool s4 hands = ON)" by blast
              next 
                show "\<forall>s3. toEnvP s3 \<and>
            substate (predEnv s5) s3 \<and>
            substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
            getVarBool s3 (Suc (Suc 0)) = ON \<and>
            getVarBool s3 hands = OFF"
                proof(rule allI; rule impI)
                  fix s3
                  assume 12: "toEnvP s3 \<and>
            substate (predEnv s5) s3 \<and>
            substate s3 s4 \<and> s3 \<noteq> s4"
                  with  11 3(1) predEnv_substate_imp_eq_or_substate
                  have "s3 = predEnv s5 \<or> substate s5 s3"
                    by auto 
                  with 10 11 12 show "getVarBool s3 (Suc (Suc 0)) = ON \<and>
            getVarBool s3 hands = OFF"
                    by auto

                qed
              qed
              thus ?thesis by auto
            qed
          qed
        qed
        with s5_def req_prems substate_refl
 pred3_def 5 show ?thesis by auto
      qed
    qed
  qed
next
  assume "((toEnvP s0 \<and>
      (\<forall>s1 s2.
          substate s1 s2 \<and>
          substate s2 s0 \<and>
          toEnvP s1 \<and>
          toEnvP s2 \<and>
          toEnvNum s1 s2 = hands \<and>
          10 \<le> toEnvNum s2 s0 \<and>
          getVarBool s1 hands = ON \<and>
          getVarBool s1 (Suc (Suc 0)) = ON \<and>
          getVarBool s2 hands = OFF \<longrightarrow>
          (\<exists>s4. toEnvP s4 \<and>
                substate s2 s4 \<and>
                substate s4 s0 \<and>
                toEnvNum s2 s4 \<le> 10 \<and>
                (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
                 getVarBool s4 hands = ON) \<and>
                (\<forall>s3. toEnvP s3 \<and>
                      substate s2 s3 \<and>
                      substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                      getVarBool s3 (Suc (Suc 0)) =
                      ON \<and>
                      getVarBool s3 hands =
                      OFF)))) \<and>
     extraInv s0) \<and>
    env (setVarAny s0 hands_value) hands_value \<and>
    getPstate (setVarAny s0 hands_value) Ctrl =
    drying \<and>
    getVarBool (setVarAny s0 hands_value) hands \<noteq>
    ON \<and>
    10 \<le> ltimeEnv (setVarAny s0 hands_value)
           Ctrl "
  with extra6 show " extraInv
     (toEnv
       (setPstate (setVarAny s0 hands_value) Ctrl
         waiting))"
    by (auto simp add: VC6_def)
qed

end