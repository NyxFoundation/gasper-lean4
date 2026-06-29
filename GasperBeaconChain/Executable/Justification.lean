import GasperBeaconChain.Core.Lemmas.Justification

universe u v

namespace GasperBeaconChain.Executable

open GasperBeaconChain.Core

/-!
# Executable layer: deciding `justified` by height recursion (the fixpoint core)

`Core.justified` is an inductive predicate. Its `justified_link` constructor
requires `s_h < t_h`, so any justification chain has strictly increasing
heights. Hence `justified st b h` is decided by **well-founded recursion on the
height `h`**: the source of a link to `(b, h)` has height `s_h < h`, already
decided by the recursion.

Computational assumptions: `[Fintype Hash]` (to enumerate the source block) and
`[DecidableRel parent]` (to decide `nth_ancestor`). `supermajority_link` is
already decidable in Core.

All proofs are explicit/constructive (no `simp`); decision procedures are built
from named combinators (`decidable_of_iff`, `And.decidable`,
`Fintype.decidableExistsFintype`) and the reflect bridge is the explicit
`decide`-correctness equation.
-/


-- § A. Decidable `nth_ancestor` (structural recursion on the step count)

/-- Zero-step ancestry is just equality. -/
theorem nth_ancestor_zero_iff {Hash : Type v} (parent : HashParent Hash) (s t : Hash) :
    nth_ancestor parent 0 s t ↔ s = t := by
  constructor
  · exact nth_ancestor_0_refl
  · rintro rfl
    exact nth_ancestor.nth_ancestor_0 s

/-- A `(n+1)`-step ancestry factors through an intermediate parent step. -/
theorem nth_ancestor_succ_iff {Hash : Type v} (parent : HashParent Hash)
    (n : Nat) (s t : Hash) :
    nth_ancestor parent (n + 1) s t ↔ ∃ m : Hash, nth_ancestor parent n s m ∧ parent m t := by
  constructor
  · exact nth_ancestor_succ_inv
  · rintro ⟨m, hsm, hmt⟩
    exact nth_ancestor.nth_ancestor_nth hsm hmt

/-- `nth_ancestor` is decidable given an enumerable, decidable block graph.
Structural recursion on the step count `n`; the intermediate block is enumerated
over `Fintype Hash`. -/
def decNthAncestor {Hash : Type v} (parent : HashParent Hash)
    [DecidableEq Hash] [Fintype Hash] [DecidableRel parent] :
    (n : Nat) → (s t : Hash) → Decidable (nth_ancestor parent n s t)
  | 0, s, t => decidable_of_iff (s = t) (nth_ancestor_zero_iff parent s t).symm
  | n + 1, s, t =>
    letI : ∀ m, Decidable (nth_ancestor parent n s m) := fun m => decNthAncestor parent n s m
    decidable_of_iff (∃ m : Hash, nth_ancestor parent n s m ∧ parent m t)
      (nth_ancestor_succ_iff parent n s t).symm


-- § B. Decidable `justification_link`

/-- `justification_link` is decidable: a conjunction of a height comparison, a
decidable `nth_ancestor`, and the Core-decidable `supermajority_link`. -/
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


-- § C. Decidable `justified` by recursion on height

/-- One-step unfolding of `justified`, with the source height witnessed by a
`Fin h` (forced by `s_h < h` inside `justification_link`). This is the recursion
equation used to decide `justified` by strong recursion on `h`. -/
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

/-- Course-of-values helper: decides `justified b h` for every height `h < H`,
by **structural recursion on the bound `H`**, forced via `termination_by
structural H`. This compiles through `Nat.rec`/`brecOn` rather than
`WellFounded.fix`, so it depends on **no `Classical.choice`** (the `Acc` /
`WellFounded` machinery of well-founded recursion is avoided entirely) and stays
computable. At bound `H' + 1`, the source of a link into height `h ≤ H'` has
height `s_h.val < h ≤ H'`, i.e. it falls under the structurally smaller bound
`H'`. This is the explicit height-indexed fixpoint iteration. -/
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

/-- `justified` is decidable: run the height-bounded fixpoint iteration at bound
`h + 1`. Computable and `Classical.choice`-free (structural recursion only). -/
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

/-- Boolean (executable) form of `justified`. -/
def justifiedB {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash) (b : Hash) (h : Nat) : Bool :=
  decide (justified τ stake vset parent genesis st b h)

/-- Reflect bridge: the executable `justifiedB` agrees with the Core `justified`
(explicit `decide`-correctness). -/
theorem justifiedB_iff {Validator : Type u} {Hash : Type v}
    [DecidableEq Validator] [DecidableEq Hash] [Fintype Validator] [Fintype Hash]
    (τ : Threshold) (stake : Validator → Nat) (vset : Hash → Finset Validator)
    (parent : HashParent Hash) [DecidableRel parent]
    (genesis : Hash) (st : State Validator Hash) (b : Hash) (h : Nat) :
    justifiedB τ stake vset parent genesis st b h = true ↔
    justified τ stake vset parent genesis st b h :=
  iff_of_eq decide_eq_true_eq

end GasperBeaconChain.Executable
