theory Proof_5
  imports Requirements VCTheoryLemmas
begin

lemma minimalRed_red_at_least_T1: "toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = minimalRed \<and> 
(\<forall>s1 s2.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
    getPstate s1 Ctrl = minimalRed) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) 
 \<Longrightarrow> (\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < ltimeEnv s1 Ctrl \<longrightarrow>
getVarBool s2 trafficLight = RED)"
  by (metis numeral_eq_iff substate_trans verit_eq_simplify(14))



lemma redAfterMinimalRed_pressed_red_at_least_T1: 
"toEnvP s1 \<and>
       substate s1 s \<and>
       getPstate s1 Ctrl = redAfterMinimalRed \<and>
       (\<forall>s1 s2.
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
           getPstate s1 Ctrl = minimalRed) \<and>
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
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
             (\<exists>s2. toEnvP s2 \<and>
                   substate s2 s1 \<and>
                   toEnvNum s2 s1 = Ctrl \<and>
                   getPstate s2 Ctrl = minimalRed \<and>
                   ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                   (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) \<Longrightarrow>
       (\<And>s1 s.
           toEnvP s1 \<and>
           substate s1 s \<and>
           getPstate s1 Ctrl = minimalRed \<and>
           (\<forall>s1 s2.
               toEnvP s1 \<and>
               toEnvP s2 \<and>
               substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
               getPstate s1 Ctrl = minimalRed) \<and>
           (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) \<Longrightarrow>
           \<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < ltimeEnv s1 Ctrl \<longrightarrow>
                getVarBool s2 minimalRed = NOT_PRESSED) \<Longrightarrow>
       getVarBool s1 redAfterMinimalRed \<Longrightarrow>
       toEnvP x \<and>
       substate x s1 \<and>
       toEnvNum x s1 = Ctrl \<and>
       getPstate x Ctrl = minimalRed \<and>
       ltimeEnv x Ctrl = MINIMAL_RED_TIME_LIMIT \<and> (getVarBool x redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED) \<Longrightarrow>
       toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> MINIMAL_RED_TIME_LIMIT \<longrightarrow> getVarBool s2 minimalRed = NOT_PRESSED"
  apply(rule impI)
  apply(rule disjE[of "substate s2 x" "substate x s2 \<and> x \<noteq> s2"])
using substate_total substate_refl
  apply metis   
  apply(rule cut_rl[of "(\<forall> s2. toEnvP s2 \<and> substate s2 x \<and> toEnvNum s2 x < ltimeEnv x Ctrl \<longrightarrow>
getVarBool s2 trafficLight = RED)"])
  apply(drule allE[of _ s2 "getVarBool s2 minimalRed = NOT_PRESSED"])
     apply (metis dual_order.strict_trans1 less_add_one toEnvNum3)
    apply assumption
   apply(rule minimalRed_red_at_least_T1[of _ s])
  using substate_trans
   apply (smt (verit))
  apply(rule cut_rl[of "s2 = s1"])
   apply (metis cong_exp_iff_simps(10) cong_exp_iff_simps(13) inc.simps(2) mod_add_self1 numeral_inc numerals(1))
  apply(rule cut_rl[of "toEnvNum emptyState s2 = toEnvNum emptyState s1"])
  using gtimeE_inj apply fast
  apply(rule cut_rl[of "toEnvNum emptyState s2 \<le> toEnvNum emptyState s1 \<and> toEnvNum emptyState s2 \<ge> toEnvNum emptyState s1"])
   apply arith
  apply(rule conjI)
  using emptyState_substate[of s2] toEnvNum3[of emptyState s2 s1] apply arith
  by (metis \<open>substate emptyState s2 \<and> substate s2 s1 \<Longrightarrow> toEnvNum emptyState s1 = toEnvNum emptyState s2 + toEnvNum s2 s1\<close> \<open>substate emptyState s2\<close> add_le_same_cancel1 le_refl less_one linorder_le_less_linear shift_toEnvNum substate_asym substate_shift)

lemma redAfterMinimalRed_notPressed_red_at_least_T1:
" toEnvP s1 \<and>
       substate s1 s \<and>
       getPstate s1 Ctrl = redAfterMinimalRed \<and>
       (\<forall>s1 s2.
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
           getPstate s1 Ctrl = minimalRed) \<and>
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
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
             (\<exists>s2. toEnvP s2 \<and>
                   substate s2 s1 \<and>
                   toEnvNum s2 s1 = Ctrl \<and>
                   getPstate s2 Ctrl = minimalRed \<and>
                   ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                   (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) \<Longrightarrow>
       (\<And>s1 s.
           toEnvP s1 \<and>
           substate s1 s \<and>
           getPstate s1 Ctrl = minimalRed \<and>
           (\<forall>s1 s2.
               toEnvP s1 \<and>
               toEnvP s2 \<and>
               substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
               getPstate s1 Ctrl = minimalRed) \<and>
           (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) \<Longrightarrow>
           \<forall>s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 < ltimeEnv s1 Ctrl \<longrightarrow>
                getVarBool s2 minimalRed = NOT_PRESSED) \<Longrightarrow>
       \<not> getVarBool s1 redAfterMinimalRed \<Longrightarrow>
       toEnvP x \<and>
       substate x s1 \<and>
       getPstate x Ctrl = minimalRed \<and>
       ltimeEnv x Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
       getVarBool x redAfterMinimalRed = NOT_PRESSED \<and>
       (\<forall>s3. toEnvP s3 \<and> substate x s3 \<and> substate s3 s1 \<and> x \<noteq> s3 \<longrightarrow>
             getPstate s3 Ctrl = redAfterMinimalRed \<and>
             getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED) \<Longrightarrow>
       toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> MINIMAL_RED_TIME_LIMIT \<longrightarrow> getVarBool s2 minimalRed = NOT_PRESSED"
 apply(rule impI)
  apply(rule disjE[of "substate s2 x" "substate x s2 \<and> x \<noteq> s2"])
using substate_total substate_refl
  apply metis   
  apply(rule cut_rl[of "(\<forall> s2. toEnvP s2 \<and> substate s2 x \<and> toEnvNum s2 x < ltimeEnv x Ctrl \<longrightarrow>
getVarBool s2 trafficLight = RED)"])
  apply(drule allE[of _ s2 "getVarBool s2 minimalRed = NOT_PRESSED"])
  apply(rule cut_rl[of "toEnvNum x s1 > 0"])
    apply (metis dual_order.strict_trans1 less_add_same_cancel1 toEnvNum3)
   apply (metis bot_nat_0.not_eq_extremum numeral_eq_iff shiftEnv.simps(1) shift_toEnvNum verit_eq_simplify(14))
  apply assumption
  apply(rule minimalRed_red_at_least_T1[of _ s])
  using substate_trans
   apply (smt (verit))
  by (metis (mono_tags, lifting) add_left_imp_eq numeral_Bit0 numeral_eq_one_iff numeral_plus_numeral one_plus_BitM one_plus_numeral_commute semiring_norm(28) semiring_norm(86) substate_trans)

  
lemma redAfterMinimalRed_red_at_least_T1: "toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> 
(\<forall>s1 s2.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
    getPstate s1 Ctrl = minimalRed) \<and>
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
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
      (\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = Ctrl \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) 
 \<Longrightarrow> (\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> MINIMAL_RED_TIME_LIMIT \<longrightarrow>
getVarBool s2 trafficLight = RED)"
  using minimalRed_red_at_least_T1
  apply(cases "getVarBool s1 requestButtonPressed")
  apply(rule exE [of "(\<lambda>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = Ctrl \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))"])
    apply fast
   apply(rule allI)
  apply((rule redAfterMinimalRed_pressed_red_at_least_T1);assumption)
  apply(rule exE[of "\<lambda> s2. toEnvP s2 \<and>
                substate s2 s1 \<and>
                getPstate s2 Ctrl = minimalRed \<and>
                ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                getVarBool s2 redAfterMinimalRed = NOT_PRESSED \<and>
                (\<forall>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s1 \<and> s2 \<noteq> s3 \<longrightarrow>
                      getPstate s3 Ctrl = redAfterMinimalRed \<and>
                      getVarBool s3 redAfterMinimalRed = NOT_PRESSED \<and> getVarBool s3 Ctrl = NOT_PRESSED)"])
   apply blast
  apply(rule allI)
  by ((rule redAfterMinimalRed_notPressed_red_at_least_T1);assumption)

lemma redToGreen_red_at_least_T1_aux1: 
"       toEnvP s1 \<and>
       substate s1 s \<and>
       getPstate s1 Ctrl = redToGreen \<and>
       (\<forall>s1 s2.
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
           getPstate s1 Ctrl = minimalRed) \<and>
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
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
             (\<exists>s2. toEnvP s2 \<and>
                   substate s2 s1 \<and>
                   toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
                   getPstate s2 Ctrl = redAfterMinimalRed \<and>
                   (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
       (\<forall>s1 s2.
           toEnvP s1 \<and>
           toEnvP s2 \<and>
           substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
           getPstate s1 Ctrl = redToGreen) \<and>
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
             (\<exists>s2. toEnvP s2 \<and>
                   substate s2 s1 \<and>
                   toEnvNum s2 s1 = Ctrl \<and>
                   getPstate s2 Ctrl = minimalRed \<and>
                   ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
                   (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED) \<and>
       (\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) \<Longrightarrow>
       toEnvP x \<and>
       substate x s1 \<and>
       toEnvNum x s1 = ltimeEnv s1 Ctrl \<and>
       getPstate x Ctrl = redAfterMinimalRed \<and>
       (getVarBool x redAfterMinimalRed = PRESSED \<or> getVarBool x Ctrl = PRESSED) \<Longrightarrow>
       toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> MINIMAL_RED_TIME_LIMIT + ltimeEnv s1 Ctrl \<longrightarrow>
       getVarBool s2 minimalRed = NOT_PRESSED"
  apply(rule impI)
 apply(rule disjE[of "substate s2 x" "substate x s2 \<and> x \<noteq> s2"])
using substate_total substate_refl
  apply metis
  apply(rule cut_rl[of "(\<forall> s2. toEnvP s2 \<and> substate s2 x \<and> toEnvNum s2 x \<le> MINIMAL_RED_TIME_LIMIT \<longrightarrow>
getVarBool s2 trafficLight = RED)"])
  apply(drule allE[of _ s2])
   prefer 2
   apply assumption
  apply (metis add_le_imp_le_right toEnvNum3)
  apply(rule redAfterMinimalRed_red_at_least_T1[of _ s])
  apply (meson substate_trans)
  by (smt (verit) linorder_le_less_linear numeral_eq_iff semiring_norm(88) shift_toEnvNum substate_asym substate_shift substate_trans)
  
  
  

lemma redToGreen_red_at_least_T1: "toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<and> 
(\<forall>s1 s2.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    substate s1 s2 \<and> substate s2 s \<and> getPstate s2 Ctrl = minimalRed \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<longrightarrow>
    getPstate s1 Ctrl = minimalRed) \<and>
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
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redToGreen \<longrightarrow>
      (\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
            getPstate s2 Ctrl = redAfterMinimalRed \<and>
            (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))) \<and>
(\<forall>s1 s2.
    toEnvP s1 \<and>
    toEnvP s2 \<and>
    substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < ltimeEnv s2 Ctrl \<and> getPstate s2 Ctrl = redToGreen \<longrightarrow>
    getPstate s1 Ctrl = redToGreen) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = redAfterMinimalRed \<and> getVarBool s1 redAfterMinimalRed \<longrightarrow>
      (\<exists>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = Ctrl \<and>
            getPstate s2 Ctrl = minimalRed \<and>
            ltimeEnv s2 Ctrl = MINIMAL_RED_TIME_LIMIT \<and>
            (getVarBool s2 redAfterMinimalRed \<or> getVarBool s1 Ctrl = PRESSED))) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl = green \<longrightarrow> getVarBool s1 minimalRed = PRESSED) \<and>
(\<forall>s1. toEnvP s1 \<and> substate s1 s \<and> getPstate s1 Ctrl \<noteq> green \<longrightarrow> getVarBool s1 minimalRed = NOT_PRESSED) 
 \<Longrightarrow> (\<forall> s2. toEnvP s2 \<and> substate s2 s1 \<and> toEnvNum s2 s1 \<le> MINIMAL_RED_TIME_LIMIT + ltimeEnv s1 Ctrl \<longrightarrow>
getVarBool s2 trafficLight = RED)"
  apply(rule exE[of "(\<lambda>s2. toEnvP s2 \<and>
            substate s2 s1 \<and>
            toEnvNum s2 s1 = ltimeEnv s1 Ctrl \<and>
            getPstate s2 Ctrl = redAfterMinimalRed \<and>
            (getVarBool s2 redAfterMinimalRed = PRESSED \<or> getVarBool s2 Ctrl = PRESSED))"])
   apply blast
  apply(rule allI)
  by ((rule redToGreen_red_at_least_T1_aux1);assumption)

theorem proof_5_1: "VC1 inv5 s0"
  apply(simp only: VC1_def inv5_def R5_def extraInv_def)
  by auto
end