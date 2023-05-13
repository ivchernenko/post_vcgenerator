theory Proofs2
  imports ExtraInv
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"

theorem proof_2_1: "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def extraInv_def)
  by simp

theorem proof_2_62: "VC62 R2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC62_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_64: "VC64 R2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC64_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_66: "VC66 R2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC66_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_67: "VC67 R2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC67_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_68: "VC68 R2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC68_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_2_69: "VC69 R2 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC69_def inv2_def R2_def extraInv_def)
  by auto

end