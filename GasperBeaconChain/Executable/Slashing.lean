import GasperBeaconChain.Core.AtomicDef.Slashing

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core

/-!
# Executable layer: deciding slashing

This is the computable mirror of Core's slashing predicates.

Core defines {name}`slashed_double_vote` / {name}`slashed_surround_vote`
with existentials ranging over {lit}`Hash` and {lit}`Nat` (both
potentially infinite types). They are *not* given a {name}`Decidable`
instance in Core (intentionally — Core is the logical layer).

Here we observe that every witness is constrained to be a vote that
already lives in the finite state $`\sigma`. Rewriting the
existentials as bounded quantifiers over $`\sigma` makes the
predicates decidable **using only the finite state** — no
{lit}`[Fintype Hash]` is required, and no {lit}`Classical.choice` /
{lit}`native_decide` is introduced.

The {lit}`iff` lemmas are the bridges connecting the Core
{name}`Prop` to the computable bounded form.
-/

variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash]

/--
{name}`slashed_double_vote` is equivalent to a bounded existential
over the finite state: the two witnessing votes and their
projections recover the Core existential variables.
-/
theorem slashed_double_vote_iff_bex
    (st : State Validator Hash) (v : Validator) :
    slashed_double_vote st v ↔
    ∃ w1 ∈ st, ∃ w2 ∈ st,
      w1.validator = v ∧ w2.validator = v ∧
      w1.target ≠ w2.target ∧ w1.targetHeight = w2.targetHeight := by
  unfold slashed_double_vote
  constructor
  · rintro ⟨t1, t2, hne, s1, s1h, s2, s2h, th, hv1, hv2⟩
    exact ⟨⟨v, s1, t1, s1h, th⟩, hv1, ⟨v, s2, t2, s2h, th⟩, hv2, rfl, rfl, hne, rfl⟩
  · rintro ⟨w1, hw1, w2, hw2, h1, h2, hne, hth⟩
    refine ⟨w1.target, w2.target, hne, w1.source, w1.sourceHeight,
            w2.source, w2.sourceHeight, w1.targetHeight, ?_, ?_⟩
    · rw [← h1]; exact vote_msg_of_mem hw1
    · rw [hth, ← h2]; exact vote_msg_of_mem hw2

/--
{name}`slashed_surround_vote` is equivalent to a bounded existential
over the finite state: the two witnessing votes recover the Core
existential variables.
-/
theorem slashed_surround_vote_iff_bex
    (st : State Validator Hash) (v : Validator) :
    slashed_surround_vote st v ↔
    ∃ w1 ∈ st, ∃ w2 ∈ st,
      w1.validator = v ∧ w2.validator = v ∧
      w1.sourceHeight < w2.sourceHeight ∧ w2.targetHeight < w1.targetHeight := by
  unfold slashed_surround_vote
  constructor
  · rintro ⟨s1, t1, s1h, t1h, s2, t2, s2h, t2h, hv1, hv2, hlts, hltt⟩
    exact ⟨⟨v, s1, t1, s1h, t1h⟩, hv1, ⟨v, s2, t2, s2h, t2h⟩, hv2, rfl, rfl, hlts, hltt⟩
  · rintro ⟨w1, hw1, w2, hw2, h1, h2, hlts, hltt⟩
    refine ⟨w1.source, w1.target, w1.sourceHeight, w1.targetHeight,
            w2.source, w2.target, w2.sourceHeight, w2.targetHeight, ?_, ?_, hlts, hltt⟩
    · rw [← h1]; exact vote_msg_of_mem hw1
    · rw [← h2]; exact vote_msg_of_mem hw2

/-- {name}`slashed_double_vote` is decidable (state-bounded, no
{lit}`[Fintype Hash]`). -/
instance instDecidableSlashedDoubleVote
    (st : State Validator Hash) (v : Validator) :
    Decidable (slashed_double_vote st v) :=
  decidable_of_iff _ (slashed_double_vote_iff_bex st v).symm

/-- {name}`slashed_surround_vote` is decidable (state-bounded, no
{lit}`[Fintype Hash]`). -/
instance instDecidableSlashedSurroundVote
    (st : State Validator Hash) (v : Validator) :
    Decidable (slashed_surround_vote st v) :=
  decidable_of_iff _ (slashed_surround_vote_iff_bex st v).symm

/-- {name}`slashed` is decidable: the disjunction of two decidable
conditions. -/
instance instDecidableSlashed
    (st : State Validator Hash) (v : Validator) :
    Decidable (slashed st v) := by
  unfold slashed
  infer_instance

/-- Boolean (executable) form of {name}`slashed`. -/
def slashedB (st : State Validator Hash) (v : Validator) : Bool :=
  decide (slashed st v)

/--
The executable {name}`slashedB` agrees with the Core
{name}`slashed`: since {lit}`slashedB st v` is
{lit}`decide (slashed st v)` by definition, the bridge is the
standard equation {lit}`decide p = true ↔ p`.
-/
theorem slashedB_iff (st : State Validator Hash) (v : Validator) :
    slashedB st v = true ↔ slashed st v :=
  iff_of_eq decide_eq_true_eq

end GasperBeaconChain.Executable
