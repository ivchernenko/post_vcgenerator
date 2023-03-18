theory Proofs_no_setVarAny
  imports HandDryer_no_setVarAny VCTheoryLemmas_no_setVarAny Extra_no_setVarAny
begin


theorem proof_1_1: 
"VC1 inv1 s0"
  apply(simp only: VC1_def inv1_def R1_def
 extraInv_def waiting_def drying_def)
  by auto

theorem proof_2_1: 
"VC1 inv2 s0"
  apply(simp only: VC1_def inv2_def R2_def
 extraInv_def waiting_def drying_def)
  by auto

theorem proof_3_1: 
"VC1 inv3 s0"
  apply(simp only: VC1_def inv3_def R3_def
 extraInv_def waiting_def drying_def)
  by auto

theorem proof_4_1: 
"VC1 inv4 s0"
  apply(simp only: VC1_def inv4_def R4_def
 extraInv_def waiting_def drying_def)
  by auto


theorem proof_2_2:
"VC2 inv2 s0 hands_value"
  apply(simp only: VC2_def inv2_def R2_def 
dryer_def)
  apply(rule impI; rule conjI)
  apply(auto)
  using extra2 by (auto simp add: VC2_def dryer_def)

theorem proof_2_3:
"VC3 inv2 s0 hands_value"
 apply(simp only: VC3_def inv2_def R2_def 
dryer_def)
  apply(rule impI; rule conjI)
   apply(auto)
  using extra3 by (auto simp add: VC3_def dryer_def)

theorem proof_2_4: 
"VC4 inv2 s0 hands_value"
 apply(simp only: VC4_def R2_def
dryer_def)
  by auto

theorem proof_2_5: 
"VC5 inv2 s0 hands_value"
 apply(simp only: VC5_def inv2_def R2_def 
dryer_def)
  apply(rule impI; rule conjI)
  apply(auto)
  using extra5 by (auto simp add: VC5_def)

theorem proof_2_6:
"VC6 inv2 s0 hands_value"
 apply(simp only: VC6_def inv2_def R2_def
dryer_def)
  apply(rule impI; rule conjI)
   apply(rule conjI)
    apply simp
   apply((rule allI)+)
   apply(rule impI)
   apply(simp split: if_splits)
  using substate_toEnvNum_id apply blast
   apply auto[1]
  using extra6 by (auto simp add: VC6_def)

theorem proof_2_7:
"VC7 inv2 s0 hands_value"
 apply(simp only: VC7_def inv2_def R2_def 
dryer_def)
  apply(rule impI; rule conjI)
  apply(auto)
  apply force
  using substate_toEnvNum_id apply blast
  using extra7 by (auto simp add: VC7_def)

theorem proof_4_2:
"VC2 inv4 s0 hands_value"
apply(simp only: VC2_def inv4_def R4_def 
dryer_def)
  apply(rule impI; rule conjI)
   apply(auto)
  using extra2 by (auto simp add: VC2_def dryer_def)

theorem proof_4_3:
"VC3 inv4 s0 hands_value"
apply(simp only: VC3_def inv4_def R4_def
dryer_def)
  apply(rule impI; rule conjI)
   apply(auto)
  using extra3 by (auto simp add: VC3_def dryer_def)

theorem proof_4_4:
"VC4 inv4 s0 hands_value"
apply(simp only: VC4_def R4_def
dryer_def)
  by auto

theorem proof_4_5:
"VC5 inv4 s0 hands_value"
apply(simp only: VC5_def inv4_def R4_def  
dryer_def)
  apply(rule impI; rule conjI)
  apply(auto)
   apply(force)
  using substate_toEnvNum_id apply(blast)
  using extra5 by (auto simp add: VC5_def)

theorem proof_4_6:
"VC6 inv4 s0 hands_value"
apply(simp only: VC6_def inv4_def R4_def
dryer_def)
  apply(rule impI; rule conjI)
   apply(auto)
  using extra6 by (auto simp add: VC6_def)

theorem proof_4_7:
"VC7 inv4 s0 hands_value"
apply(simp only: VC7_def inv4_def R4_def
dryer_def)
  apply(rule impI; rule conjI)
   apply(auto)
  using extra7 by (auto simp add: VC7_def)

theorem proof_1_4:
"VC4 inv1 s0 hands_value"
apply(simp only: VC4_def R1_def
dryer_def)
  by auto

theorem proof_3_4:
"VC4 inv3 s0 hands_value"
apply(simp only: VC4_def R3_def
dryer_def)
  by auto


end               

