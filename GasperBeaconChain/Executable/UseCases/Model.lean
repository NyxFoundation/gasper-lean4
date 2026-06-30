import GasperBeaconChain.Executable.Slashing
import GasperBeaconChain.Executable.Quorums
import GasperBeaconChain.Executable.Justification
import GasperBeaconChain.Executable.AccountableSafety
import GasperBeaconChain.Executable.PlausibleLiveness


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

abbrev V := Fin 99

abbrev H := Fin 6


instance (priority := 10000) instFintypeV : Fintype V :=
  ⟨⟨(List.finRange 99 : List (Fin 99)), by decide⟩, List.mem_finRange⟩

instance (priority := 10000) instFintypeH : Fintype H :=
  ⟨⟨(List.finRange 6 : List (Fin 6)), by decide⟩, List.mem_finRange⟩

def stake : V → Nat := fun _ => 1

def vset : H → Finset V := fun _ => Finset.univ

def genesis : H := 0

def parent : H → H → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨
  (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 5)

instance : DecidableRel parent := fun a b => by unfold parent; infer_instance

abbrev τ : Threshold := canonicalThreshold



theorem hash_ancestor_right_closed {a b : H}
    (h : hash_ancestor parent a b) : (a = 4 ∨ a = 5) → (b = 4 ∨ b = 5) := by
  induction h with
  | refl => exact id
  | step _ hp ih =>
      intro ha
      rcases ih ha with rfl | rfl
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, rfl⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr rfl
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)

theorem hash_ancestor_left_closed {a b : H}
    (h : hash_ancestor parent a b) :
    (a = 1 ∨ a = 2 ∨ a = 3) → (b = 1 ∨ b = 2 ∨ b = 3) := by
  induction h with
  | refl => exact id
  | step _ hp ih =>
      intro ha
      rcases ih ha with rfl | rfl | rfl
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨_, rfl⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inl rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, rfl⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inr rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)

theorem not_hash_ancestor_4_1 : ¬ hash_ancestor parent 4 1 := fun h => by
  rcases hash_ancestor_right_closed h (Or.inl rfl) with h1 | h1 <;> exact absurd h1 (by decide)

theorem not_hash_ancestor_1_4 : ¬ hash_ancestor parent 1 4 := fun h => by
  rcases hash_ancestor_left_closed h (Or.inl rfl) with h1 | h1 | h1 <;> exact absurd h1 (by decide)

end GasperBeaconChain.Executable.UseCases
