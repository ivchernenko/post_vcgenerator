theory Proofs1
  imports ExtraInv3 VCTheoryLemmas
begin

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"

theorem proof_1_1: "VC1 inv1 s0"
  apply(unfold VC1_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_252: "VC252 R1 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC252_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_277: "VC277 R1 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC277_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_2327: "VC327 R1 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC327_def inv1_def R1_def extraInv_def)
  by auto

theorem proof_1_402: "VC402 R1 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC402_def inv1_def R1_def extraInv_def)
  by auto

end