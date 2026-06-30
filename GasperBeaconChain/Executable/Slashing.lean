import GasperBeaconChain.Core.AtomicDef.Slashing

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core


variable {Validator : Type u} {Hash : Type v}
variable [DecidableEq Validator] [DecidableEq Hash]

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

instance instDecidableSlashedDoubleVote
    (st : State Validator Hash) (v : Validator) :
    Decidable (slashed_double_vote st v) :=
  decidable_of_iff _ (slashed_double_vote_iff_bex st v).symm

instance instDecidableSlashedSurroundVote
    (st : State Validator Hash) (v : Validator) :
    Decidable (slashed_surround_vote st v) :=
  decidable_of_iff _ (slashed_surround_vote_iff_bex st v).symm

instance instDecidableSlashed
    (st : State Validator Hash) (v : Validator) :
    Decidable (slashed st v) := by
  unfold slashed
  infer_instance

def slashedB (st : State Validator Hash) (v : Validator) : Bool :=
  decide (slashed st v)

theorem slashedB_iff (st : State Validator Hash) (v : Validator) :
    slashedB st v = true ↔ slashed st v :=
  iff_of_eq decide_eq_true_eq

end GasperBeaconChain.Executable
