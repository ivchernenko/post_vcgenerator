theory Proof_1
  imports trafficLights Requirements VCTheoryLemmas
begin

lemma minimalRed_not_vc3: "toEnvP s1 \<and> substate s1 s \<and> toEnvNum emptyState s1 > MINIMAL_RED_TIME_LIMIT \<and>
getPstate s1 Ctrl = minimalRed \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl) \<or>
toEnvNum emptyState s1 \<le> MINIMAL_RED_TIME_LIMIT \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getVarBool s2 trafficLight = GREEN \<and> toEnvNum s2 s1 \<le> ltimeEnv s1 Ctrl)"
  by (metis (no_types, lifting) leD order_le_less substate_trans)

lemma redAfterMinimalRed_not_vc3: "toEnvP s1 \<and> substate s1 s \<and> toEnvNum emptyState s1 > MINIMAL_RED_TIME_LIMIT + 1  \<and>
getPstate s1 Ctrl =redAfterMinimalRed \<and> getVarBool s1 requestButtonPressed \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl) \<or>
toEnvNum emptyState s1 \<le> MINIMAL_RED_TIME_LIMIT \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green)) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
      (\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = Ctrl \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getVarBool s2 trafficLight = GREEN \<and> toEnvNum s2 s1 \<le>MINIMAL_RED_TIME_LIMIT + 1)"
  apply(rule impI)
 apply(rule cut_rl[of "(\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = Ctrl \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))"])
  using minimalRed_not_vc3
   apply (metis (no_types, opaque_lifting) order.order_iff_strict substate_trans toEnvNum3 toEnvP.simps(2))
  by auto
 

lemma minimalRed_notPressed: "  toEnvP s1 \<and>
          substate s1 s \<and>
          MINIMAL_RED_TIME_LIMIT + Ctrl < toEnvNum emptyState s1 \<and>
          getPstate s1 Ctrl = redAfterMinimalRed \<and>
          \<not> getVarBool s1 redAfterMinimalRed \<and>
          (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
                (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl) \<or>
                toEnvNum emptyState s1 \<le> MINIMAL_RED_TIME_LIMIT \<and>
                (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green)) \<and>
          (\<forall>s1. toEnvP s1 \<and>
                substate s1 s \<and>
                getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
                (\<exists>s2. toEnvP s2 \<and>
                      substate s2 s1 \<and>
                      getPstate s2 Ctrl = minimalRed \<and>
                      ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                      getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                      (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                            getPstate s3 Ctrl = redAfterMinimalRed \<and>
                            getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
          (\<forall>s1 s2.
              toEnvP s1 \<and>
              toEnvP s2 \<and>
              substate s1 s2 \<and>
              substate s2 s \<and>
              toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
              getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
              getVarBool s1 Ctrl = NOT_PRESSED) \<and>
          (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED) \<Longrightarrow>
          \<exists>s2. toEnvP s2 \<and>
               substate s2 s1 \<and>
               getPstate s2 Ctrl = minimalRed \<and>
               ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
               getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
               (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                     getPstate s3 Ctrl = redAfterMinimalRed \<and>
                     getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
          toEnvP x \<and>
          substate x s1 \<and>
          getPstate x Ctrl = minimalRed \<and>
          ltimeEnv x Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
          getVarBool x redAfterMinimalRed = NOT_PRESSED \<and>
          (\<forall>s3. toEnvP s3 \<and> substate x s3 \<and> substate s3 s1 \<and> x \<noteq> s3 \<longrightarrow>
                getPstate s3 Ctrl = redAfterMinimalRed \<and>
                getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
          \<exists>s3. toEnvP s3 \<and> substate s3 s1 \<and> toEnvNum s3 s1 = T1 \<and> getVarBool s3 minimalRed = NOT_PRESSED \<Longrightarrow>
          \<not> (toEnvNum x s1 \<le> T1 - MINIMAL_RED_TIME_LIMIT \<and> MINIMAL_RED_TIME_LIMIT < toEnvNum emptyState x) \<Longrightarrow>
          toEnvNum x s1 \<noteq> T1 - MINIMAL_RED_TIME_LIMIT + Ctrl \<Longrightarrow>
          T1 - MINIMAL_RED_TIME_LIMIT + Ctrl < toEnvNum x s1 \<Longrightarrow>
          toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < T1 \<longrightarrow> getVarBool s2 Ctrl = NOT_PRESSED"
  apply(cases "substate s2 x")
  using toEnvNum3[of s2 x s1] substate_trans[of x s1 s]
  apply (smt (verit) Nat.add_diff_assoc2 add.commute add_lessD1 less_diff_conv less_diff_conv2 less_or_eq_imp_le linordered_semidom_class.add_diff_inverse trans_le_add2 verit_comp_simplify1(3))
  using  substate_asym
  by (metis substate_total)

lemma toEnvP_gtime_ge_0: "toEnvP s \<Longrightarrow> toEnvNum emptyState s > 0"
  apply(cases s)
  by auto

lemma minimalRed_firstIter: "toEnvP s1 \<and>
    substate s1 s \<and>
    MINIMAL_RED_TIME_LIMIT + Ctrl < toEnvNum emptyState s1 \<and>
    getPstate s1 Ctrl = redAfterMinimalRed \<and>
    \<not> getVarBool s1 redAfterMinimalRed \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl) \<or>
          toEnvNum emptyState s1 \<le> MINIMAL_RED_TIME_LIMIT \<and>
          (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green)) \<and>
    (\<forall>s1. toEnvP s1 \<and>
          substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
          (\<exists>s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
    (\<forall>s1 s2.
        toEnvP s1 \<and>
        toEnvP s2 \<and>
        substate s1 s2 \<and>
        substate s2 s \<and>
        toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
        getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
        getVarBool s1 Ctrl = NOT_PRESSED) \<and>
    (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED) \<Longrightarrow>
    \<exists>s2. toEnvP s2 \<and>
         substate s2 s1 \<and>
         getPstate s2 Ctrl = minimalRed \<and>
         ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
         getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
         (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
               getPstate s3 Ctrl = redAfterMinimalRed \<and>
               getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
    toEnvP x \<and>
    substate x s1 \<and>
    getPstate x Ctrl = minimalRed \<and>
    ltimeEnv x Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
    getVarBool x redAfterMinimalRed = NOT_PRESSED \<and>
    (\<forall>s3. toEnvP s3 \<and> substate x s3 \<and> substate s3 s1 \<and> x \<noteq> s3 \<longrightarrow>
          getPstate s3 Ctrl = redAfterMinimalRed \<and>
          getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
    \<not> (toEnvNum x s1 \<le> T1 - MINIMAL_RED_TIME_LIMIT \<and> MINIMAL_RED_TIME_LIMIT < toEnvNum emptyState x) \<Longrightarrow>
    toEnvNum x s1 \<noteq> T1 - MINIMAL_RED_TIME_LIMIT + Ctrl \<Longrightarrow>
    \<not> T1 - MINIMAL_RED_TIME_LIMIT + Ctrl < toEnvNum x s1 \<Longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s3 s1 \<and> toEnvNum s3 s1 = T1 \<and> getVarBool s3 trafficLight = RED) \<Longrightarrow>
     toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < T1 \<longrightarrow> getVarBool s2 Ctrl = NOT_PRESSED"
  apply(cases "substate s2 x")
   apply(rule cut_rl[of "toEnvNum emptyState s1 \<le> T1"])
    apply(rule cut_rl[of "toEnvNum emptyState s1 > T1"])
     apply arith
  using toEnvP_gtime_ge_0 toEnvNum3[of emptyState _ s1]
    apply (metis diff_add_inverse2 diff_is_0_eq emptyState_substate linorder_not_less minus_nat.diff_0)
   apply(rule cut_rl[of "toEnvNum emptyState x \<le> MINIMAL_RED_TIME_LIMIT \<and> toEnvNum x s1 \<le> T1 - MINIMAL_RED_TIME_LIMIT"])
   apply (metis \<open>\<And>s2. substate emptyState s2 \<and> substate s2 s1 \<Longrightarrow> toEnvNum emptyState s1 = toEnvNum emptyState s2 + toEnvNum s2 s1\<close> diff_add_inverse emptyState_substate le_antisym ltime_le_toEnvNum nat_add_left_cancel_le)
   apply arith
  using substate_total substate_asym
  by metis
  

lemma minimalRed_notPressed_or_green: "toEnvP s1 \<and>
         substate s1 s \<and>
         MINIMAL_RED_TIME_LIMIT + Ctrl < toEnvNum emptyState s1 \<and>
         getPstate s1 Ctrl = redAfterMinimalRed \<and>
         \<not> getVarBool s1 redAfterMinimalRed \<and>
         (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
               (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl) \<or>
               toEnvNum emptyState s1 \<le> MINIMAL_RED_TIME_LIMIT \<and>
               (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green)) \<and>
         (\<forall>s1. toEnvP s1 \<and>
               substate s1 s \<and>
               getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
               (\<exists>s2. toEnvP s2 \<and>
                     substate s2 s1 \<and>
                     getPstate s2 Ctrl = minimalRed \<and>
                     ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                     getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                     (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                           getPstate s3 Ctrl = redAfterMinimalRed \<and>
                           getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
         (\<forall>s1 s2.
             toEnvP s1 \<and>
             toEnvP s2 \<and>
             substate s1 s2 \<and>
             substate s2 s \<and>
             toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
             getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
             getVarBool s1 Ctrl = NOT_PRESSED) \<and>
         (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED) \<Longrightarrow>
         \<exists>s2. toEnvP s2 \<and>
              substate s2 s1 \<and>
              getPstate s2 Ctrl = minimalRed \<and>
              ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
              getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
              (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                    getPstate s3 Ctrl = redAfterMinimalRed \<and>
                    getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
         toEnvP x \<and>
         substate x s1 \<and>
         getPstate x Ctrl = minimalRed \<and>
         ltimeEnv x Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
         getVarBool x redAfterMinimalRed = NOT_PRESSED \<and>
         (\<forall>s3. toEnvP s3 \<and> substate x s3 \<and> substate s3 s1 \<and> x \<noteq> s3 \<longrightarrow>
               getPstate s3 Ctrl = redAfterMinimalRed \<and>
               getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s3 s1 \<and> toEnvNum s3 s1 = T1 \<and> getVarBool s3 trafficLight = RED) \<Longrightarrow>
         (\<exists>s2. toEnvP s2 \<and> substate s2 s1 \<and> getVarBool s2 minimalRed = PRESSED \<and> toEnvNum s2 s1 \<le> T1) \<or>
         (\<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < T1 \<longrightarrow> getVarBool s2 requestButton = NOT_PRESSED)"
  apply(cases "toEnvNum x s1 \<le> T1 - MINIMAL_RED_TIME_LIMIT \<and> toEnvNum emptyState x > MINIMAL_RED_TIME_LIMIT")
   apply(rule disjI1)
   apply(rule cut_rl[of "(\<exists>s2. toEnvP s2 \<and> substate s2 x \<and> getVarBool s2 minimalRed = PRESSED \<and>
 toEnvNum s2 x \<le> MINIMAL_RED_TIME_LIMIT)"])
  using toEnvNum3[of _ x s1]
    apply (smt (z3) add_le_mono diff_add_inverse substate_trans)
  using substate_trans minimalRed_not_vc3
   apply (smt (verit) nat_le_linear)
  apply(rule disjI2)
  apply(cases "toEnvNum x s1 = T1 - MINIMAL_RED_TIME_LIMIT + 1")
   apply(rule cut_rl[of "\<forall>s2. toEnvP s2 \<and> (substate x s2 \<and> substate s2 s1 \<and>  x \<noteq> s2 \<or>
 substate s2 x \<and> toEnvNum s2 x <  MINIMAL_RED_TIME_LIMIT - 1)  \<longrightarrow> getVarBool s2 Ctrl = NOT_PRESSED"])
  apply (smt (verit) Nat.add_diff_assoc \<open>\<And>s1a. substate s1a x \<and> substate x s1 \<Longrightarrow> toEnvNum s1a s1 = toEnvNum s1a x + toEnvNum x s1\<close> diff_add_inverse le_add1 less_diff_conv less_diff_conv2 substate_total trans_le_add2)
   apply (smt (z3) substate_trans)
   apply(cases "toEnvNum x s1 > T1 - MINIMAL_RED_TIME_LIMIT + 1")
   apply(rule allI)
   apply ((rule minimalRed_notPressed);blast)
  apply(rule allI)
  by ((rule minimalRed_firstIter);blast)


lemma redAfterMinimalRed_notPressed_not_vc3: "toEnvP s1 \<and> substate s1 s \<and> toEnvNum emptyState s1 > MINIMAL_RED_TIME_LIMIT + 1  \<and>
getPstate s1 Ctrl =redAfterMinimalRed \<and> \<not>getVarBool s1 requestButtonPressed \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green \<and> toEnvNum s2 s1 = ltimeEnv s1 Ctrl) \<or>
toEnvNum emptyState s1 \<le> MINIMAL_RED_TIME_LIMIT \<and>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> getPstate s2 Ctrl = green)) \<and>
(\<forall>s1. toEnvP s1 \<and>
      substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
      (\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
            (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                  getPstate s3 Ctrl = redAfterMinimalRed \<and>
                  getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))) \<and>
(\<forall>s1 s2.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    substate s1 s2 \<and>
    substate s2 s \<and>
    toEnvNum s1 s2 < ltimeEnv s2 Ctrl - Ctrl \<and>
    getPstate s2 Ctrl = minimalRed \<and> getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<longrightarrow>
    getVarBool s1 Ctrl = NOT_PRESSED) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 trafficLight = GREEN) \<Longrightarrow>
(\<exists> s3. toEnvP s3 \<and> substate s3 s1 \<and> toEnvNum s3 s1 = T1 \<and> getVarBool s3 trafficLight = RED)
 \<Longrightarrow>
(\<exists> s2. toEnvP s2 \<and> substate s2 s1 \<and> getVarBool s2 trafficLight = GREEN \<and> toEnvNum s2 s1 \<le>T1) \<or>
(\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < T1 \<longrightarrow> getVarBool s2 requestButton = NOT_PRESSED)"
  apply(rule cut_rl[of " (\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
            (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                  getPstate s3 Ctrl = redAfterMinimalRed \<and>
                  getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))"])
  apply(rule exE[of "(\<lambda> s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
            (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                  getPstate s3 Ctrl = redAfterMinimalRed \<and>
                  getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED))"])
    apply fast
   apply((rule minimalRed_notPressed_or_green);blast)
  by blast
  