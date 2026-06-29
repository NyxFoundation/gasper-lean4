import GasperBeaconChain.Core.Theories.AccountableSafety
import GasperBeaconChain.Executable.Quorums

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core

/-!
# Executable layer: accountable safety, verified by computation

`Core.accountable_safety` proves, abstractly, that any finalization fork forces
`q_intersection_slashed`. Here we connect that Core theorem to the executable
witness checker `qIntersectionWitnessB` (from `Executable.Quorums`):

> a fork yields a concrete witness `(bL, bR, qL, qR)` on which the Boolean
> checker returns `true`.

In other words the slashing verdict produced by the safety theorem is
*certifiable by computation* — no `[Fintype Hash]`, no enumeration, and the
axiom footprint stays `propext` / `Quot.sound` only.
-/

variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator]

/-- Executable corollary of `k_accountable_safety`: a `k`-finalization fork
yields a witness on which `qIntersectionWitnessB` returns `true`. -/
theorem k_accountable_safety_witnessB
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (parent : HashParent Hash) (genesis : Hash)
    (st : State Validator Hash) {k1 k2 : Nat}
    (hfork : k_finalization_fork τ stake vset parent genesis st k1 k2) :
    ∃ bL bR : Hash, ∃ qL qR : Finset Validator,
      qIntersectionWitnessB τ stake vset st bL bR qL qR = true := by
  obtain ⟨bL, bR, qL, qR, hw⟩ :=
    (q_intersection_slashed_iff_exists_witness τ stake vset st).mp
      (k_accountable_safety τ stake vset parent genesis st hfork)
  exact ⟨bL, bR, qL, qR, (qIntersectionWitnessB_iff τ stake vset st bL bR qL qR).mpr hw⟩

/-- Executable corollary of `accountable_safety`: a finalization fork yields a
witness on which `qIntersectionWitnessB` returns `true`. -/
theorem accountable_safety_witnessB
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (parent : HashParent Hash) (genesis : Hash)
    (st : State Validator Hash)
    (hfork : finalization_fork τ stake vset parent genesis st) :
    ∃ bL bR : Hash, ∃ qL qR : Finset Validator,
      qIntersectionWitnessB τ stake vset st bL bR qL qR = true := by
  obtain ⟨bL, bR, qL, qR, hw⟩ :=
    (q_intersection_slashed_iff_exists_witness τ stake vset st).mp
      (accountable_safety τ stake vset parent genesis st hfork)
  exact ⟨bL, bR, qL, qR, (qIntersectionWitnessB_iff τ stake vset st bL bR qL qR).mpr hw⟩

end GasperBeaconChain.Executable
