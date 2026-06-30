import GasperBeaconChain.Core.Lemmas.Justification

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core




theorem nth_ancestor_zero_iff {Hash : Type v} (parent : HashParent Hash) (s t : Hash) :
    nth_ancestor parent 0 s t ↔ s = t := by
  constructor
  · exact nth_ancestor_0_refl
  · rintro rfl
    exact nth_ancestor.nth_ancestor_0 s

theorem nth_ancestor_succ_iff {Hash : Type v} (parent : HashParent Hash)
    (n : Nat) (s t : Hash) :
    nth_ancestor parent (n + 1) s t ↔ ∃ m : Hash, nth_ancestor parent n s m ∧ parent m t := by
  constructor
  · exact nth_ancestor_succ_inv
  · rintro ⟨m, hsm, hmt⟩
    exact nth_ancestor.nth_ancestor_nth hsm hmt

def decNthAncestor {Hash : Type v} (parent : HashParent Hash)
    [DecidableEq Hash] [Fintype Hash] [DecidableRel parent] :
    (n : Nat) → (s t : Hash) → Decidable (nth_ancestor parent n s t)
  | 0, s, t => decidable_of_iff (s = t) (nth_ancestor_zero_iff parent s t).symm
  | n + 1, s, t =>
    letI : ∀ m, Decidable (nth_ancestor parent n s m) := fun m => decNthAncestor parent n s m
    decidable_of_iff (∃ m : Hash, nth_ancestor parent n s m ∧ parent m t)
      (nth_ancestor_succ_iff parent n s t).symm



def decJustificationLink {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (st : State Validator Hash) (s t : Hash) (s_h t_h : Nat) :
    Decidable (justification_link τ stake vset parent st s t s_h t_h) := by
  letI : Decidable (nth_ancestor parent (t_h - s_h) s t) :=
    decNthAncestor parent (t_h - s_h) s t
  unfold justification_link
  infer_instance



theorem justified_iff_bounded {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) (genesis : Hash)
    (st : State Validator Hash) (b : Hash) (h : Nat) :
    justified τ stake vset parent genesis st b h ↔
    (b = genesis ∧ h = 0) ∨
    ∃ s : Hash, ∃ s_h : Fin h,
      justified τ stake vset parent genesis st s s_h.val ∧
      justification_link τ stake vset parent st s b s_h.val h := by
  constructor
  · intro hj
    rcases justified_cases τ stake vset parent genesis st hj with
      ⟨hbg, hh0⟩ | ⟨s, s_h, hsj, hlink⟩
    · exact Or.inl ⟨hbg, hh0⟩
    · exact Or.inr ⟨s, ⟨s_h, hlink.1⟩, hsj, hlink⟩
  · rintro (⟨rfl, rfl⟩ | ⟨s, s_h, hsj, hlink⟩)
    · exact justified.justified_genesis
    · exact justified.justified_link hsj hlink

def decAllBelow {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash)
    (H : Nat) (b : Hash) (h : Nat) (hlt : h < H) :
    Decidable (justified τ stake vset parent genesis st b h) :=
  match H, hlt with
  | 0, hlt => absurd hlt (Nat.not_lt_zero h)
  | H' + 1, hlt =>
    letI : ∀ (s : Hash) (s_h : Fin h),
        Decidable (justified τ stake vset parent genesis st s s_h.val) :=
      fun s s_h => decAllBelow τ stake vset parent genesis st H' s s_h.val
        (Nat.lt_of_lt_of_le s_h.isLt (Nat.lt_succ_iff.mp hlt))
    letI : ∀ (s : Hash) (s_h : Fin h),
        Decidable (justification_link τ stake vset parent st s b s_h.val h) :=
      fun s s_h => decJustificationLink τ stake vset parent st s b s_h.val h
    decidable_of_iff _ (justified_iff_bounded τ stake vset parent genesis st b h).symm
termination_by structural H

def decJustified {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash) (h : Nat) (b : Hash) :
    Decidable (justified τ stake vset parent genesis st b h) :=
  decAllBelow τ stake vset parent genesis st (h + 1) b h (Nat.lt_succ_self h)

instance instDecidableJustified {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash) (b : Hash) (h : Nat) :
    Decidable (justified τ stake vset parent genesis st b h) :=
  decJustified τ stake vset parent genesis st h b

def justifiedB {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash) (b : Hash) (h : Nat) : Bool :=
  decide (justified τ stake vset parent genesis st b h)

theorem justifiedB_iff {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash) (b : Hash) (h : Nat) :
    justifiedB τ stake vset parent genesis st b h = true ↔
    justified τ stake vset parent genesis st b h :=
  iff_of_eq decide_eq_true_eq

end GasperBeaconChain.Executable
