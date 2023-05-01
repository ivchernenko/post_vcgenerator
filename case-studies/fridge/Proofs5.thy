theory Proofs5
imports ExtraInv3 VCTheoryLemmas
begin

definition inv5 where "inv5 s \<equiv> R5 s \<and> extraInv s"

theorem proof_5_1: "VC1 inv5 s0"
  apply(unfold VC1_def inv5_def R5_def extraInv_def)
  by auto

theorem proof_5_2: "VC2 R5 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC2_def inv5_def R5_def)
  by auto

theorem proof_5_252: "VC252 R5 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC252_def inv5_def R5_def)
  by auto

theorem proof_5_257: "VC257 R5 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC257_def inv5_def R5_def)
  by auto

theorem proof_5_262: "VC262 R5 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC262_def inv5_def R5_def)
  by auto

end
