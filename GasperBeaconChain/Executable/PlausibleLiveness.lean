import GasperBeaconChain.Core.AtomicDef.PlausibleLiveness
import GasperBeaconChain.Executable.Slashing

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core


variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash]

def notSlashedB (st : State Validator Hash) (v : Validator) : Bool :=
  decide (¬ slashed st v)

theorem notSlashedB_iff (st : State Validator Hash) (v : Validator) :
    notSlashedB st v = true ↔ ¬ slashed st v :=
  iff_of_eq decide_eq_true_eq

def IsGoodQuorumAt
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (b : Hash) (q2 : Finset Validator) : Prop :=
  quorum_2 τ stake vset q2 b ∧ ∀ v ∈ q2, ¬ slashed st v

instance instDecidableIsGoodQuorumAt
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (b : Hash) (q2 : Finset Validator) :
    Decidable (IsGoodQuorumAt τ stake vset st b q2) := by
  unfold IsGoodQuorumAt
  infer_instance

def goodQuorumAtB
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (b : Hash) (q2 : Finset Validator) : Bool :=
  decide (IsGoodQuorumAt τ stake vset st b q2)

theorem goodQuorumAtB_iff
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (b : Hash) (q2 : Finset Validator) :
    goodQuorumAtB τ stake vset st b q2 = true ↔ IsGoodQuorumAt τ stake vset st b q2 :=
  iff_of_eq decide_eq_true_eq

theorem two_thirds_good_iff_forall_exists_goodQuorum
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash) :
    two_thirds_good τ stake vset st ↔
    ∀ b : Hash, ∃ q2 : Finset Validator, IsGoodQuorumAt τ stake vset st b q2 :=
  Iff.rfl

end GasperBeaconChain.Executable
