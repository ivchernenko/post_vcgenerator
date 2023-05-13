theory Proofs4
  imports ExtraInv
begin

definition inv4 where "inv4 s \<equiv> R4 s \<and> extraInv s"

theorem proof_4_1: "VC1 inv4 s0"
  apply(unfold VC1_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_2: "VC2 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC2_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_12: "VC12 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC12_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_22: "VC22 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC22_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_32: "VC32 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC32_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_42: "VC42 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC42_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_52: "VC52 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC52_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_62: "VC62 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC62_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_72: "VC72 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC72_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_82: "VC82 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC82_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_92: "VC92 R4 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC92_def inv4_def R4_def extraInv_def)
  by auto

