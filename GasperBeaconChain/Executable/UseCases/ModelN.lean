import GasperBeaconChain.Executable.UseCases.Committee
import GasperBeaconChain.Core.Theories.AccountableSafety
import GasperBeaconChain.Core.Lemmas.PlausibleLiveness
import GasperBeaconChain.Executable.Slashing
import GasperBeaconChain.Executable.Quorums
import GasperBeaconChain.Executable.Justification
import GasperBeaconChain.Executable.AccountableSafety
import GasperBeaconChain.Executable.PlausibleLiveness

/-!
# A size-parametric committee on the §8 deep checkpoint tree

Shared scaffold for the *new* parametric use cases (S2 surround fork, k=2
finalization, Lemma 4.11, surround liveness).  Unlike the legacy `Model.lean`
(fixed `V = Fin 99`), here the committee size is a **parameter** `N`, instantiated
by the choice-free `Committee.finFintypeCF`.  Quorum weights are computed *exactly*
(no `decide` over `N`) via the image-based `Committee.lowerQuorum`.

The block tree is fixed (it encodes the *scenario*, not the committee size) and is
made deep enough on both branches to host genuine **skip links** (so a finalized
interval can be *surrounded* — the S2 condition) and `k = 2` finalization:

```text
            0   (genesis, height 0)
          /   \
    h1   1     4   h1
         |     |
    h2   2     5   h2
         |     |
    h3   3     6   h3
               |
    h4         7   h4
```

Left chain `0⋖1⋖2⋖3`, right chain `0⋖4⋖5⋖6⋖7`.  Blocks `1` (height 1, left) and
`6` (height 3, right) conflict at different heights; the skip link `0 ⇒ 6`
(`nth_ancestor 3`) over the right chain can surround the finalized interval `[1,2]`
of the left chain — exactly Casper's S2 picture (Buterin–Griffith Thm 1, Fig. 3).
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable.UseCases


/-! ## 1. The fixed checkpoint tree (committee-size independent) -/

/-- Eight checkpoint blocks (`0` = genesis). -/
abbrev H := Fin 8

/-- Genesis. -/
def genesis : H := 0

/-- Parent relation: left chain `0⋖1⋖2⋖3`, right chain `0⋖4⋖5⋖6⋖7`. -/
def parent : H → H → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨
  (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 7)

instance : DecidableRel parent := fun a b => by unfold parent; infer_instance

/-- The canonical 2/3 threshold (`two_third n = n - n/3`). -/
abbrev τ : Threshold := canonicalThreshold

/-- If `n ≤ 2` then `n ∈ {0,1,2}` (the `k = 2` analogue of Core's
`leq_one_means_zero_or_one`; the impossible cases `n ≥ 3` are eliminated by the
dependent match on `h : n ≤ 2`). -/
theorem leq_two_means {n : Nat} (h : n ≤ 2) : n = 0 ∨ n = 1 ∨ n = 2 :=
  match n, h with
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr (Or.inl rfl)
  | 2, _ => Or.inr (Or.inr rfl)


/-! ### Explicit constructive threshold arithmetic (no `omega`)

The canonical threshold is `two_third n = n - n/3`, so `one_third n = n - two_third n = n/3`.
Every quantitative fact the parametric use cases need is proved here, **once**, from named
`Nat` lemmas in term mode — never `omega` (which hides the derivation). -/

/-- `one_third N = N/3` for the canonical threshold (`N - (N - N/3) = N/3`). -/
theorem one_third_eq (N : Nat) : τ.one_third N = N / 3 :=
  Nat.sub_sub_self (Nat.div_le_self N 3)

/-- `2·(N/3) ≤ N` for **every** `N` (`(N/3)·2 ≤ (N/3)·3 ≤ N`). -/
theorem two_div_three_le (N : Nat) : N / 3 + N / 3 ≤ N :=
  le_of_eq_of_le (Nat.mul_two (N / 3)).symm
    (Nat.le_trans (Nat.mul_le_mul (Nat.le_refl (N / 3)) (by decide : (2 : Nat) ≤ 3))
      (Nat.div_mul_le_self N 3))

/-- `2·(N/3) < N` for `N ≥ 3`, proved explicitly: `N/3·2 < N/3·3 ≤ N`. -/
theorem two_div_three_lt {N : Nat} (hN : 3 ≤ N) : N / 3 + N / 3 < N :=
  have hq : 0 < N / 3 := Nat.div_pos hN (by decide)
  have h32 : N / 3 * 3 = N / 3 * 2 + N / 3 := Nat.mul_succ (N / 3) 2
  have hlt23 : N / 3 * 2 < N / 3 * 3 :=
    Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right hq) h32.symm
  lt_of_eq_of_lt (Nat.mul_two (N / 3)).symm
    (Nat.lt_of_lt_of_le hlt23 (Nat.div_mul_le_self N 3))

/-- `two_third N > 0` for `N ≥ 3` (since `N/3 < N`). -/
theorem two_third_pos {N : Nat} (hN : 3 ≤ N) : 0 < τ.two_third N :=
  Nat.sub_pos_of_lt (Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide) hN) (by decide))

/-- The 2/3-overlap weight bound is strictly positive for `N ≥ 3`:
`N - one_third N - one_third N = N - N/3 - N/3 > 0`. -/
theorem overlap_pos {N : Nat} (hN : 3 ≤ N) :
    0 < N - τ.one_third N - τ.one_third N :=
  have hpos : 0 < N - N / 3 - N / 3 :=
    Nat.lt_of_lt_of_eq
      (Nat.sub_pos_of_lt (two_div_three_lt hN))
      (Nat.sub_sub N (N / 3) (N / 3)).symm
  Nat.lt_of_lt_of_eq hpos
    (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) rfl (one_third_eq N).symm) (one_third_eq N).symm)

/-- `N - one_third N = two_third N` (the subtractive form of the decomposition). -/
theorem two_third_eq_sub (N : Nat) : N - τ.one_third N = τ.two_third N :=
  (congrArg (N - ·) (τ.thirds_def N).symm).trans (Nat.sub_sub_self (τ.leq_two_thirds N))

/-- One-third never exceeds two-thirds (`N/3 ≤ N - N/3`, since `2·(N/3) ≤ N`). -/
theorem one_third_le_two_third (N : Nat) : τ.one_third N ≤ τ.two_third N :=
  Eq.subst (motive := fun x => x ≤ τ.two_third N) (one_third_eq N).symm
    (Nat.le_sub_of_add_le (two_div_three_le N))

/-- The exact intersection cardinality equals the Core lower bound:
`two_third N - one_third N = N - one_third N - one_third N`. -/
theorem overlap_card_eq_bound (N : Nat) :
    τ.two_third N - τ.one_third N = N - τ.one_third N - τ.one_third N :=
  congrArg (· - τ.one_third N) (two_third_eq_sub N).symm


/-! ### Parent edges and ancestry paths (concrete, `decide`-checked) -/

theorem pe_01 : parent 0 1 := by decide
theorem pe_12 : parent 1 2 := by decide
theorem pe_23 : parent 2 3 := by decide
theorem pe_04 : parent 0 4 := by decide
theorem pe_45 : parent 4 5 := by decide
theorem pe_56 : parent 5 6 := by decide
theorem pe_67 : parent 6 7 := by decide

/-- `nth_ancestor`s used as the forward-link witnesses of the checkpoint edges. -/
theorem anc_0_1 : nth_ancestor parent 1 0 1 :=
  nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) pe_01
theorem anc_0_4 : nth_ancestor parent 1 0 4 :=
  nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) pe_04
theorem anc_2_3 : nth_ancestor parent 1 2 3 :=
  nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 2) pe_23
theorem anc_1_2 : nth_ancestor parent 1 1 2 :=
  nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 1) pe_12
theorem anc_6_7 : nth_ancestor parent 1 6 7 :=
  nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 6) pe_67
/-- The **skip link** path `0 ⇒ 6` of length 3 (`0⋖4⋖5⋖6`) — the surround engine. -/
theorem anc_0_6 : nth_ancestor parent 3 0 6 :=
  nth_ancestor.nth_ancestor_nth
    (nth_ancestor.nth_ancestor_nth
      (nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) pe_04) pe_45) pe_56
/-- The **skip link** path `1 ⇒ 3` of length 2 (`1⋖2⋖3`) — for `k = 2` finalization. -/
theorem anc_1_3 : nth_ancestor parent 2 1 3 :=
  nth_ancestor.nth_ancestor_nth
    (nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 1) pe_12) pe_23


/-! ### Branch-closure: the two non-genesis branches are descent-closed

Needed to discharge the `¬ hash_ancestor` conflict clauses of a `finalization_fork`. -/

/-- Descendants of `{1,2,3}` stay in `{1,2,3}` (the upper-left chain). -/
theorem left_closed {a b : H} (h : hash_ancestor parent a b) :
    (a = 1 ∨ a = 2 ∨ a = 3) → (b = 1 ∨ b = 2 ∨ b = 3) := by
  induction h with
  | refl => exact id
  | step _ hp ih =>
      intro ha
      rcases ih ha with rfl | rfl | rfl
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨_,rfl⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inl rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨h0,_⟩|⟨_,rfl⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inr rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)

/-- Descendants of `{4,5,6,7}` stay in `{4,5,6,7}` (the right chain). -/
theorem right_closed {a b : H} (h : hash_ancestor parent a b) :
    (a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7) → (b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7) := by
  induction h with
  | refl => exact id
  | step _ hp ih =>
      intro ha
      rcases ih ha with rfl | rfl | rfl | rfl
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨_,rfl⟩|⟨h0,_⟩|⟨h0,_⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inl rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨_,rfl⟩|⟨h0,_⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨_,rfl⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inr (Or.inr rfl))
      · unfold parent at hp
        rcases hp with ⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩|⟨h0,_⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)

/-- Block `1` (left) is not an ancestor of block `6` (right). -/
theorem not_anc_1_6 : ¬ hash_ancestor parent 1 6 := fun h => by
  rcases left_closed h (Or.inl rfl) with h1 | h1 | h1 <;> exact absurd h1 (by decide)
/-- Block `6` (right) is not an ancestor of block `1` (left). -/
theorem not_anc_6_1 : ¬ hash_ancestor parent 6 1 := fun h => by
  rcases right_closed h (Or.inr (Or.inr (Or.inl rfl))) with h1|h1|h1|h1 <;> exact absurd h1 (by decide)
/-- Block `1` (left) is not an ancestor of block `4` (right). -/
theorem not_anc_1_4 : ¬ hash_ancestor parent 1 4 := fun h => by
  rcases left_closed h (Or.inl rfl) with h1 | h1 | h1 <;> exact absurd h1 (by decide)
/-- Block `4` (right) is not an ancestor of block `1` (left). -/
theorem not_anc_4_1 : ¬ hash_ancestor parent 4 1 := fun h => by
  rcases right_closed h (Or.inl rfl) with h1|h1|h1|h1 <;> exact absurd h1 (by decide)


/-! ## 2. The size-parametric committee -/

section Committee
variable (N : Nat)

/-- Uniform unit stake on an `N`-validator committee. -/
def stake : Fin N → Nat := fun _ => 1

/-- Static validator set: all `N` validators eligible at every block. -/
def vset : H → Finset (Fin N) := fun _ => Finset.univ

/-- The whole committee has weight `N` (choice-free, no `decide`). -/
theorem wt_vset (b : H) : wt (stake N) (vset N b) = N :=
  wt_one_univ N

/-- A canonical 2/3 quorum: the first `two_third N` validators, weight *exactly*
`two_third N` (computed by `Finset.card_map`, independent of `N`). -/
def qTT : Finset (Fin N) :=
  lowerQuorum N (τ.two_third N) (τ.leq_two_thirds N)

theorem wt_qTT : wt (stake N) (qTT N) = τ.two_third N :=
  wt_lowerQuorum N (τ.two_third N) (τ.leq_two_thirds N)

/-- `qTT` is a genuine 2/3 quorum at every block — the reusable supermajority. -/
theorem quorum2_qTT (b : H) : quorum_2 τ (stake N) (vset N) (qTT N) b :=
  ⟨Finset.subset_univ _,
   le_of_eq ((congrArg τ.two_third (wt_vset N b)).trans (wt_qTT N).symm)⟩

/-- Well-formedness: all supporters lie in the (universal) target set. -/
theorem wf_vset (st : State (Fin N) H) :
    votes_from_target_vset_property (vset N) st :=
  fun {x} _ _ _ _ _ => Finset.mem_univ x

end Committee

end GasperBeaconChain.Executable.UseCases.Parametric
