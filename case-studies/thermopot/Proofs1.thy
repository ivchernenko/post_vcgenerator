theory Proofs1
  imports ExtraInv
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"

theorem proof_1_1: "VC1 inv1 s0"
  apply(unfold VC1_def inv1_def R1_def extraInv_def)
  by simp

theorem proof_1_64: "VC64 R1 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC64_def  R1_def extraInv_def)
  by auto

theorem proof_1_65: "VC65 R1 env s0 temperature_value button1_value button2_value button3_value boilingButton_value "
  apply(unfold VC65_def  R1_def extraInv_def)
  by auto

end