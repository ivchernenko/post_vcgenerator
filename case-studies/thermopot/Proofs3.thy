theory Proofs3
  imports ExtraInv
begin

definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"

theorem proof_3_1: "VC1 inv3 s0"
  apply(unfold VC1_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_2: "VC2 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC2_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_62: "VC62 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC62_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_64: "VC64 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC64_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_65: "VC65 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC65_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_66: "VC66 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC66_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_67: "VC67 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC67_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_68: "VC68 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC68_def inv3_def R3_def extraInv_def)
  by auto

theorem proof_3_62: "VC69 R3 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC69_def inv3_def R3_def extraInv_def)
  by auto

end