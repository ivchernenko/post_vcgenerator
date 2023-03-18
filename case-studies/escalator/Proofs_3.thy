theory Proofs_3
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"

theorem proof_3_1: "VC1 inv3 s0"
  apply(simp only: VC1_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_2: "VC2 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC2_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_3: "VC3 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC3_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_4: "VC4 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC4_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_5: "VC5 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC5_def inv3_def R3_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI)+)
 apply(rule impI)
  apply (simp split: if_splits)
  using substate_toEnvNum_id apply blast
  by auto

theorem proof_3_6: "VC6 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC6_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_7: "VC7 inv3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC7_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_8: "VC8 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC8_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_9: "VC9 inv3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC9_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_10: "VC10  R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC10_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_11: "VC11 inv3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC11_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_12: "VC12 R3 env s0 userAtTop_value userAtBottom_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC12_def inv3_def R3_def extraInv_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI)+)
  apply(rule impI)
  apply(simp split: if_splits)
  using substate_toEnvNum_id apply blast
  by auto

end