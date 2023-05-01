theory Proofs4
  imports ExtraInv3 VCTheoryLemmas
begin

definition inv4 where "inv4 s \<equiv> R4 s \<and> extraInv s"

theorem proof_4_1: "VC1 inv4 s0"
  apply(unfold VC1_def inv4_def R4_def extraInv_def)
  by auto

theorem proof_4_277: "VC277 R4 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC277_def R4_def)
  apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI)+)
  apply(rule impI)
  apply(simp split: if_splits)
   apply fastforce
  by auto

theorem proof_4_327: "VC327 R4 env s0 fridgeTempGreaterMin_value fridgeTempGreaterMax_value freezerTempGreaterMin_value
 freezerTempGreaterMax_value fridgeDoor_value"
  apply(unfold VC327_def R4_def)
    apply(rule impI)
  apply(rule conjI)
   apply simp
  apply((rule allI)+)
  apply(rule impI)
  apply(simp split: if_splits)
   apply fastforce
  by auto

end
