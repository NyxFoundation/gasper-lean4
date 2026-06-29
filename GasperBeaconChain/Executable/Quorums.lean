import GasperBeaconChain.Core.AtomicDef.Quorums
import GasperBeaconChain.Executable.Slashing

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core

/-!
# Executable layer: checking `q_intersection_slashed` witnesses

Core's `q_intersection_slashed` is an existential over two blocks
`bL bR : Hash` and two quorums `qL qR : Finset Validator`. *Deciding* that
existential would require `[Fintype Hash]` and is exponential (it enumerates
all quorums) — and it is the wrong executable primitive: the accountable-safety
theorem does not search, it **constructs** the witness directly.

The genuinely infinite part of the predicate is the slashing clause
`∀ v ∈ qL ∩ qR, slashed st v` (because `slashed` quantifies over heights in
`ℕ`). That is already made decidable in `Executable.Slashing`.

So the right executable content here is a **witness checker**: given a concrete
`(bL, bR, qL, qR)`, decide the slashable-intersection clause. This needs no
`[Fintype Hash]`, no enumeration, and no `Classical.choice` / `native_decide`.
We then record that `q_intersection_slashed` is exactly "a checkable witness
exists", so `accountable_safety`'s constructed witness can be *verified by
computation*.
-/

variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash]

/-- The slashable-intersection clause for a *concrete* witness `(bL,bR,qL,qR)`.
Every conjunct is decidable from finite data: the subset checks, the Core
`quorum_2` decision, and `slashed` over the finite state. -/
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

/-- Boolean (executable) witness checker. -/
def qIntersectionWitnessB
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (bL bR : Hash) (qL qR : Finset Validator) : Bool :=
  decide (IsQIntersectionWitness τ stake vset st bL bR qL qR)

/-- Reflect bridge for the witness checker (explicit `decide`-correctness). -/
theorem qIntersectionWitnessB_iff
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (bL bR : Hash) (qL qR : Finset Validator) :
    qIntersectionWitnessB τ stake vset st bL bR qL qR = true ↔
    IsQIntersectionWitness τ stake vset st bL bR qL qR :=
  iff_of_eq decide_eq_true_eq

/-- `q_intersection_slashed` is exactly the existence of a checkable witness.
The infinite `slashed` clause is reduced to the decidable `IsQIntersectionWitness`;
only the block/quorum existential stays symbolic. Combined with
`accountable_safety`, this lets one verify the slashing verdict by computation on
the constructed witness. -/
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
