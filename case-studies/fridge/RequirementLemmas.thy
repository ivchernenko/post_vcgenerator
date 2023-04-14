theory RequirementLemmas
  imports VCTheoryLemmas
begin

lemma ex_or_all_imp_ex_or_all: "
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T1 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2)) \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T2 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2)) \<Longrightarrow>
substate s0 s \<Longrightarrow>
toEnvNum s0 s = 1 \<Longrightarrow>
R s \<or> S s \<and> T1 s0 < T2 s \<and> T2 s > 0 \<Longrightarrow>
toEnvP s \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
P1 s0 \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T2 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2))"
  apply(rule cut_rl[of "\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow> s1=s \<or> substate s1 s0"])
  apply(rule allI)
  subgoal for s4
    apply(cases "s4 = s")
     apply(rule impI)
     apply(rule allI)
    subgoal for s1
      apply(cases "s1=s")
       apply(rule impI)
      using substate_refl substate_antisym toEnvNum_id  apply metis
      apply(rule impI)
       apply(erule allE[of _ s0])
        apply(erule impE)
        using substate_refl apply simp
        apply(rotate_tac -1)
        apply(erule allE[of _ s1])
        apply(erule impE)
        using toEnvNum3
        apply (metis linorder_not_less not_add_less1 order_le_less_trans)
        apply(rotate_tac -1)
        apply(erule disjE)
        using substate_trans apply metis
        apply(erule disjE)
        using substate_refl apply blast
        apply(rule disjI2)
        apply(rule conjI)
        using toEnvNum3
        apply (smt (verit) add_le_imp_le_left dual_order.trans ex_least_nat_le leD less_imp_add_positive less_one linorder_le_less_linear nless_le) 
        by auto
      by (smt (verit))
    by (metis substate_antisym substate_or_substate_pair substate_refl)

 lemma ex_imp_ex_or_all: "
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) ) \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T2 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2)) \<Longrightarrow>
substate s0 s \<Longrightarrow>
toEnvNum s0 s = 1 \<Longrightarrow>
R s \<or> S s \<and> 0 < T2 s \<and> T2 s > 0 \<Longrightarrow>
toEnvP s \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
P1 s0 \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T2 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2))"  
   apply(rule cut_rl[of 
"\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < 0 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2))"])
    apply(rule ex_or_all_imp_ex_or_all[of _ P1 _ _ _ _ ])
   by auto
   
lemma ex_or_all_imp_ex: "
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T1 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2)) \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2))) \<Longrightarrow>
substate s0 s \<Longrightarrow>
toEnvNum s0 s = 1 \<Longrightarrow>
R s  \<Longrightarrow>
toEnvP s \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
P1 s0 \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)))"
  apply(rule cut_rl[of 
"\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < 0 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2))"])
  apply simp
  apply(rule ex_or_all_imp_ex_or_all[of s0 P1])
  by auto

lemma ex_imp_ex: "
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2))) \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2))) \<Longrightarrow>
substate s0 s \<Longrightarrow>
toEnvNum s0 s = 1 \<Longrightarrow>
R s  \<Longrightarrow>
toEnvP s \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
P1 s0 \<Longrightarrow>
\<forall> s4. toEnvP s4 \<and> substate s4 s \<and> P2 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)))"
  apply(rule cut_rl[of
"\<forall> s4. toEnvP s4 \<and> substate s4 s0 \<and> P1 s4 \<longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s4 \<and> toEnvNum s1 s4 \<le> T \<and> Q s1 \<longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> toEnvNum s1 s3 \<le> T \<and> R s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> S s2)) \<or>
toEnvNum s1 s4 < T1 s4 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s4 \<longrightarrow> S s2))"])
   apply(rule ex_or_all_imp_ex[of s0 P1])
  by auto

end
