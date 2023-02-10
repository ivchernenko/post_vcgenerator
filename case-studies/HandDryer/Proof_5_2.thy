theory Proof_5_2
  imports HandDryer VCTheoryLemmas Extra
begin






theorem proof_5_2: "\<exists> k. VC2 R5 s0 hands_value k"
  apply(simp only: VC2_def inv5_def R5_def extraInv_def dryer_def waiting_def drying_def)
  nitpick[card state =23]