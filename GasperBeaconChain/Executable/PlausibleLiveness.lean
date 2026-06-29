import GasperBeaconChain.Core.AtomicDef.PlausibleLiveness
import GasperBeaconChain.Executable.Slashing

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core

/-!
# Executable layer: liveness-side predicates

The plausible-liveness hypotheses are built from `¬ slashed` and `quorum_2`.
Both are now computable:

* `¬ slashed st v` is decidable because `slashed` is (`Executable.Slashing`).
* `two_thirds_good st` is `∀ b, ∃ q2, quorum_2 q2 b ∧ ∀ v ∈ q2, ¬ slashed st v`.
  Its genuinely infinite part (the `slashed` negation) is now decidable, so the
  per-block "good quorum" clause `IsGoodQuorumAt` is a decidable witness checker
  (no `[Fintype Hash]`, no quorum enumeration). Only the per-block existential
  over quorums stays symbolic.

No `Classical.choice` / `native_decide` is introduced.
-/

variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash]

/-- Boolean form of "validator `v` is not slashed in `st`". -/
def notSlashedB (st : State Validator Hash) (v : Validator) : Bool :=
  decide (¬ slashed st v)

/-- Reflect bridge for `notSlashedB` (explicit `decide`-correctness). -/
theorem notSlashedB_iff (st : State Validator Hash) (v : Validator) :
    notSlashedB st v = true ↔ ¬ slashed st v :=
  iff_of_eq decide_eq_true_eq

/-- A concrete quorum `q2` is "good" at block `b`: a supermajority all of whose
members are unslashed. Decidable from finite data — no `[Fintype Hash]`. -/
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

/-- Boolean (executable) good-quorum checker. -/
def goodQuorumAtB
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (b : Hash) (q2 : Finset Validator) : Bool :=
  decide (IsGoodQuorumAt τ stake vset st b q2)

/-- Reflect bridge for the good-quorum checker (explicit `decide`-correctness). -/
theorem goodQuorumAtB_iff
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash)
    (b : Hash) (q2 : Finset Validator) :
    goodQuorumAtB τ stake vset st b q2 = true ↔ IsGoodQuorumAt τ stake vset st b q2 :=
  iff_of_eq decide_eq_true_eq

/-- `two_thirds_good` is exactly: at every block, a checkable good quorum exists.
The `slashed`-negation clause is reduced to the decidable `IsGoodQuorumAt`. -/
theorem two_thirds_good_iff_forall_exists_goodQuorum
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator) (st : State Validator Hash) :
    two_thirds_good τ stake vset st ↔
    ∀ b : Hash, ∃ q2 : Finset Validator, IsGoodQuorumAt τ stake vset st b q2 :=
  Iff.rfl

end GasperBeaconChain.Executable
