theory Proofs5
  imports ExtraInv
begin

definition inv5 where "inv5 s \<equiv> R5 s \<and> extraInv s"

theorem proof_5_1: "VC1 inv5 s0"
  apply(unfold VC1_def inv5_def R5_def extraInv_def)
  by auto

theorem proof_5_64: "VC64 R5 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC64_def inv5_def R5_def extraInv_def)
  by auto

theorem proof_5_67: "VC67 R5 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC67_def inv5_def R5_def extraInv_def)
  by auto

end