import GasperBeaconChain.Core.Theories.AccountableSafety
import GasperBeaconChain.Executable.Quorums

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core


variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator]

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
