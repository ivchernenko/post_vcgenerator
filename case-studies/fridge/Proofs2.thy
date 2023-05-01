theory Proofs2
  imports ExtraInv3 VCTheoryLemmas
begin

definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"

theorem proof_2_1: "VC1 inv2 s0"
  apply(unfold VC1_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_1_252: "VC252 R2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC252_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_1_327: "VC327 R2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC327_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_1_352: "VC352 R2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC352_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_1_377: "VC377 R2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC377_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_1_402: "VC402 R2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC402_def inv2_def R2_def extraInv_def)
  by auto

theorem proof_1_427: "VC427 R2 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC427_def inv2_def R2_def extraInv_def)
  by auto

end
