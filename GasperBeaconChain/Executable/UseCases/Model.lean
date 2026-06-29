import GasperBeaconChain.Executable.Slashing
import GasperBeaconChain.Executable.Quorums
import GasperBeaconChain.Executable.Justification
import GasperBeaconChain.Executable.AccountableSafety
import GasperBeaconChain.Executable.PlausibleLiveness

/-!
# A faithful medium-scale Casper FFG instance for the executable use cases

This is the shared testbed for everything under `Executable/UseCases/`. It is
designed *against the actual Core structure* — `State = Finset Vote`,
`HashParent = Hash → Hash → Prop`, `quorum_2`, `supermajority_link`, `justified`,
`finalized`, `finalization_fork`, `q_intersection_slashed` — so that the use
cases exercise the real **theorems** (`accountable_safety`, `slashable_bound`,
plausible liveness), not merely the Boolean oracles.

## The instance

* **Validators** `V = Fin 99` — a committee-scale set (cf. the Gasper paper's
  simulations with ~100 validators), each of unit stake. Total weight `99`, so
  `two_third 99 = 99 - 99/3 = 66` and `one_third 99 = 33`. A 2/3 supermajority
  link therefore needs supporters of weight `≥ 66`; any two such quorums of a
  99-validator set intersect in weight `≥ 66 + 66 - 99 = 33 = one_third 99` —
  exactly the N/3 accountable-safety bound, realised concretely. At this scale
  states are built with Core's `votes_for_link` / `fUnion`, not hand-listed.
* **Blocks** `H = Fin 6` — a checkpoint tree with a genuine fork:

  ```text
        0  (genesis)
       / \
      1   4
      |   |
      2   5
      |
      3
  ```

  Left chain `0 ⋖ 1 ⋖ 2 ⋖ 3`; right branch `0 ⋖ 4 ⋖ 5`. Blocks `1` and `4` are
  the two conflicting children of genesis — the fork witnessed by accountable
  safety. Neither is an ancestor of the other (proved below as
  `not_hash_ancestor_4_1` / `not_hash_ancestor_1_4`).
* **Static validator sets** `vset b = univ`. This is the Casper FFG /
  static-set setting (faithful to the paper's §2.3 normalisation to average
  stake `1`); the *dynamic* validator sets of Gasper §8.6 are exercised
  separately in the slashable-bound use case, where `vset bL ≠ vset bR`.

The branch-closure lemmas at the end are the constructive content needed to
prove the `¬ hash_ancestor` conflict clauses of `finalization_fork` — they
cannot come from `decide` (Core gives `hash_ancestor` no `Decidable` instance),
so we establish them by induction on the ancestry derivation.
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

/-- A committee-scale set of 99 validators, each of unit stake. -/
abbrev V := Fin 99

/-- Six checkpoint blocks (`0` = genesis). -/
abbrev H := Fin 6

/-!
### Choice-free finite universes

Mathlib's `Fin.fintype` is **`Classical.choice`-tainted**: its `elems` field
carries the `Nodup` witness `List.nodup_finRange`, which depends on
`Classical.choice` (as does `Finset.range`). Consequently *every*
`Finset.univ : Finset (Fin n)` — and thus `vset`, the quorums, and `link_supporters`
inside the Core — would inherit `Classical.choice` the moment the abstractly
choice-free Core is instantiated at a concrete `Fin n`.

We repair this by supplying our own `Fintype` instances whose `Nodup` obligation
is discharged by **`decide`** (the membership field `List.mem_finRange` is already
choice-free). Higher priority ensures every `Finset.univ : Finset V` / `Finset H`
in the use cases resolves here, so the concrete demonstrations stay
`Classical.choice`-zero — the project's defining invariant — exactly like the
abstract Core that `make audit` certifies.
-/

/-- A `Classical.choice`-free `Fintype (Fin 99)` for the validators. -/
instance (priority := 10000) instFintypeV : Fintype V :=
  ⟨⟨(List.finRange 99 : List (Fin 99)), by decide⟩, List.mem_finRange⟩

/-- A `Classical.choice`-free `Fintype (Fin 6)` for the checkpoint blocks
(used by `justifiedB`'s source enumeration). -/
instance (priority := 10000) instFintypeH : Fintype H :=
  ⟨⟨(List.finRange 6 : List (Fin 6)), by decide⟩, List.mem_finRange⟩

/-- Uniform unit stake. Total weight `9`; `two_third 9 = 6`, `one_third 9 = 3`. -/
def stake : V → Nat := fun _ => 1

/-- Static validator set: all nine validators are eligible at every block. -/
def vset : H → Finset V := fun _ => Finset.univ

/-- The genesis checkpoint. -/
def genesis : H := 0

/-- Parent relation of the checkpoint tree: left chain `0 ⋖ 1 ⋖ 2 ⋖ 3` and
right branch `0 ⋖ 4 ⋖ 5`. -/
def parent : H → H → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨
  (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 5)

/-- The parent relation is decidable (a disjunction of decidable `Fin`
equalities), enabling `nth_ancestor` / `justified` to compute. -/
instance : DecidableRel parent := fun a b => by unfold parent; infer_instance

/-- The canonical 2/3 threshold (`two_third n = n - n/3`). -/
abbrev τ : Threshold := canonicalThreshold


/-! ## Branch-closure lemmas

`hash_ancestor` is the reflexive-transitive closure of `parent` and is *not*
given a `Decidable` instance in Core, so the `¬ hash_ancestor` conflict clauses
of a `finalization_fork` must be proved structurally. We show each branch of the
tree is closed under taking descendants: the right branch `{4,5}` and the upper
left chain `{1,2,3}` map into themselves under `parent`. The conflict facts
follow immediately. -/

/-- The right branch `{4,5}` is closed under descent: any descendant of `4` or
`5` is again in `{4,5}` (from `4` the only edge is `4 ⋖ 5`; `5` is a leaf). -/
theorem hash_ancestor_right_closed {a b : H}
    (h : hash_ancestor parent a b) : (a = 4 ∨ a = 5) → (b = 4 ∨ b = 5) := by
  induction h with
  | refl => exact id
  | step _ hp ih =>
      intro ha
      rcases ih ha with rfl | rfl
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, rfl⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr rfl
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)

/-- The upper-left chain `{1,2,3}` is closed under descent (`1 ⋖ 2 ⋖ 3`, and `3`
is a leaf), so no descendant of `1` leaves `{1,2,3}`. -/
theorem hash_ancestor_left_closed {a b : H}
    (h : hash_ancestor parent a b) :
    (a = 1 ∨ a = 2 ∨ a = 3) → (b = 1 ∨ b = 2 ∨ b = 3) := by
  induction h with
  | refl => exact id
  | step _ hp ih =>
      intro ha
      rcases ih ha with rfl | rfl | rfl
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨_, rfl⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inl rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, rfl⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact Or.inr (Or.inr rfl)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · unfold parent at hp
        rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)

/-- Block `4` (right branch) is not an ancestor of block `1` (left branch). -/
theorem not_hash_ancestor_4_1 : ¬ hash_ancestor parent 4 1 := fun h => by
  rcases hash_ancestor_right_closed h (Or.inl rfl) with h1 | h1 <;> exact absurd h1 (by decide)

/-- Block `1` (left branch) is not an ancestor of block `4` (right branch). -/
theorem not_hash_ancestor_1_4 : ¬ hash_ancestor parent 1 4 := fun h => by
  rcases hash_ancestor_left_closed h (Or.inl rfl) with h1 | h1 | h1 <;> exact absurd h1 (by decide)

end GasperBeaconChain.Executable.UseCases
