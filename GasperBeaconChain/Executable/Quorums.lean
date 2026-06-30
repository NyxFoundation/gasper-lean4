import GasperBeaconChain.Core.AtomicDef.Quorums
import GasperBeaconChain.Executable.Slashing

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core


variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash]

def IsQIntersectionWitness
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (bL bR : Hash) (qL qR : Finset Validator) : Prop :=
  qL ⊆ vset bL ∧ qR ⊆ vset bR ∧
  quorum_2 τ stake vset qL bL ∧ quorum_2 τ stake vset qR bR ∧
  ∀ v ∈ qL ∩ qR, slashed st v

instance instDecidableIsQIntersectionWitness
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (bL bR : Hash) (qL qR : Finset Validator) :
    Decidable (IsQIntersectionWitness τ stake vset st bL bR qL qR) := by
  unfold IsQIntersectionWitness
  infer_instance

def qIntersectionWitnessB
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (bL bR : Hash) (qL qR : Finset Validator) : Bool :=
  decide (IsQIntersectionWitness τ stake vset st bL bR qL qR)

theorem qIntersectionWitnessB_iff
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (bL bR : Hash) (qL qR : Finset Validator) :
    qIntersectionWitnessB τ stake vset st bL bR qL qR = true ↔
    IsQIntersectionWitness τ stake vset st bL bR qL qR :=
  iff_of_eq decide_eq_true_eq

theorem q_intersection_slashed_iff_exists_witness
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash) :
    q_intersection_slashed τ stake vset st ↔
    ∃ bL bR : Hash, ∃ qL qR : Finset Validator,
      IsQIntersectionWitness τ stake vset st bL bR qL qR := by
  unfold q_intersection_slashed IsQIntersectionWitness
  constructor
  · rintro ⟨bL, bR, qL, qR, hsubL, hsubR, hqL, hqR, hsl⟩
    exact ⟨bL, bR, qL, qR, hsubL, hsubR, hqL, hqR,
      fun v hv => hsl v (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2⟩
  · rintro ⟨bL, bR, qL, qR, hsubL, hsubR, hqL, hqR, hsl⟩
    exact ⟨bL, bR, qL, qR, hsubL, hsubR, hqL, hqR,
      fun v hvL hvR => hsl v (Finset.mem_inter.mpr ⟨hvL, hvR⟩)⟩

end GasperBeaconChain.Executable
