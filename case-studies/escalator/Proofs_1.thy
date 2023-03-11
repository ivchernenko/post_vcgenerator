theory Proofs_1
  imports Requirements ExtraInv VCTheoryLemmas
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"

theorem proof_1_1: "VC1 inv1 s0"
  apply(simp only: VC1_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_2: "VC2 R1 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC2_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_3: "VC3 R1 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC3_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_4: "VC4 R1 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC4_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_5: "VC5 R1 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC5_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_6: "VC6 R1 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC6_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_7: "VC7 inv11 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC7_def)
  by auto

theorem proof_1_8: "VC8 R1 env s0 userAtTop_value userAtBotton_value directionSwitch_value alarmButton_value stuck_value"
  apply(simp only: VC8_def inv1_def R1_def extraInv_def)
  by auto

end