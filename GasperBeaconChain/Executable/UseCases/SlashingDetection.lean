import GasperBeaconChain.Executable.UseCases.Model


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

def stSlashing : State V H :=
  { { validator := 0, source := 0, target := 1, sourceHeight := 0, targetHeight := 5 },
    { validator := 0, source := 0, target := 4, sourceHeight := 0, targetHeight := 5 },
    { validator := 1, source := 0, target := 3, sourceHeight := 0, targetHeight := 10 },
    { validator := 1, source := 1, target := 2, sourceHeight := 2, targetHeight := 5 },
    { validator := 2, source := 0, target := 1, sourceHeight := 0, targetHeight := 1 },
    { validator := 3, source := 0, target := 1, sourceHeight := 0, targetHeight := 1 } }



#eval slashedB stSlashing 0
#eval slashedB stSlashing 1
#eval slashedB stSlashing 2
#eval slashedB stSlashing 3

#eval (List.finRange 99).filter (fun v => slashedB stSlashing v)



theorem v0_double_vote : slashed_double_vote stSlashing 0 :=
  ⟨1, 4,
   by decide,
   0, 0, 0, 0, 5,
   by decide,
   by decide⟩

theorem v1_surround_vote : slashed_surround_vote stSlashing 1 :=
  ⟨0, 3, 0, 10,
   1, 2, 2, 5,
   by decide,
   by decide,
   by decide,
   by decide⟩

theorem v0_slashed : slashed stSlashing 0 := Or.inl v0_double_vote
theorem v1_slashed : slashed stSlashing 1 := Or.inr v1_surround_vote



theorem v2_not_slashed : ¬ slashed stSlashing 2 :=
  fun h => absurd ((slashedB_iff stSlashing 2).mpr h) (by decide)

theorem v3_not_slashed : ¬ slashed stSlashing 3 :=
  fun h => absurd ((slashedB_iff stSlashing 3).mpr h) (by decide)



example : slashed stSlashing 0 := (slashedB_iff stSlashing 0).mp (by decide)

theorem slashed_set_characterization :
    ∀ v : V, slashed stSlashing v ↔ (v = 0 ∨ v = 1) := by decide

end GasperBeaconChain.Executable.UseCases
