import GasperBeaconChain.Executable.UseCases.Finality
import GasperBeaconChain.Core.Refinement.CheckpointTree


/-!
# Use case: justification across an empty epoch

An executable counterexample to the reading "the model cannot express a
justification whose source and target are the same block in consecutive
epochs". Following Gasper § 4, checkpoints are *pairs* $`(B, j)`; when an
epoch contains no block of the chain, the same block is the checkpoint of
two consecutive epochs, and the two pairs are distinct nodes of the
checkpoint tree joined by one parent edge.

## The chain

Three blocks with $`C = 2` slots per epoch:

```
%%mermaid
graph LR
  g["0 = genesis (slot 0)"] --> b1["1 = B (slot 1)"] --> b2["2 = B' (slot 5)"]
```

Epoch $`2` covers slots $`3, 4` and contains no block, so
$`\operatorname{EBB}(B', 2) = \operatorname{EBB}(B', 1) = B`.

## The checkpoint tree

```
%%mermaid
graph LR
  c0["(0, 0)"] --> c1["(1, 1)"] --> c2["(1, 2)  ← same block 1, distinct node"] --> c3["(2, 3)"]
```

## What is checked

* {lit}`ebb` computes the epoch boundary blocks above ({lit}`#eval`).
* $`(1, 1) \to (1, 2)` is a parent edge, by {lit}`cp_empty_epoch`.
* With a $`\frac{2}{3}`-quorum voting $`(0,0) \to (1,1)`, $`(1,1) \to (1,2)`
  and $`(1,2) \to (2,3)`, the checkpoint $`(1, 2)` is {lit}`justified` at
  height $`2` — proved as a term over the concrete checkpoint tree
  {lit}`cp_parent`, and decided by {lit}`decide` / {lit}`#eval` on a finite
  encoding of the same tree.
* The invalid pair $`(2, 2)` (slot $`5 > 2 \cdot 2`) is not justified.
-/

namespace GasperBeaconChain.Executable.UseCases.EmptyEpoch

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

/-! ## The slotted chain -/

abbrev B := Fin 3

def bslot : B → Nat := fun b => if b = 0 then 0 else if b = 1 then 1 else 5

def bparent : B → Option B := fun b => if b = 0 then none else if b = 1 then some 0 else some 1

theorem bslot_lt : ∀ b p : B, bparent b = some p → bslot p < bslot b := by decide

theorem broot_unique : ∀ b : B, bparent b = none → b = 0 := by decide

def ctx : SlottedChainContext B where
  bparent := bparent
  slot := bslot
  bgenesis := 0
  C := 2
  slot_genesis := rfl
  slot_lt := fun {b p} h => bslot_lt b p h
  root_unique := fun {b} h => broot_unique b h

/-! ## Epoch boundary blocks -/

#eval ebb ctx 2 1
#eval ebb ctx 2 2
#eval ebb ctx 2 3
#eval ebb ctx 1 0

theorem ebb_2_1 : ebb ctx 2 1 = 1 := by decide
theorem ebb_2_2 : ebb ctx 2 2 = 1 := by decide
theorem ebb_2_3 : ebb ctx 2 3 = 2 := by decide

/-! ## The checkpoint tree: the same block as two distinct nodes -/

theorem cp_11_valid : cp_valid ctx ⟨1, 1⟩ := by decide
theorem cp_12_valid : cp_valid ctx ⟨1, 2⟩ := by decide
theorem cp_22_invalid : ¬ cp_valid ctx ⟨2, 2⟩ := by decide

theorem parent_00_11 : cp_parent ctx ⟨0, 0⟩ ⟨1, 1⟩ := by decide

/-- The empty-epoch edge $`(1,1) \to (1,2)`, obtained from the general theorem. -/
theorem parent_11_12 : cp_parent ctx ⟨1, 1⟩ ⟨1, 2⟩ :=
  cp_empty_epoch ctx cp_11_valid

theorem parent_12_23 : cp_parent ctx ⟨1, 2⟩ ⟨2, 3⟩ := by decide

theorem cp_11_ne_12 : (⟨1, 1⟩ : Checkpoint B) ≠ ⟨1, 2⟩ := by decide

/-- Depth of $`(1, 2)` is $`2`, from {lit}`cp_depth`. -/
theorem depth_12 : nth_ancestor (cp_parent ctx) 2 (cp_genesis ctx) ⟨1, 2⟩ :=
  cp_depth ctx 2 1 cp_12_valid

/-! ## Votes and justification over the concrete checkpoint tree -/

def vsetCP : Checkpoint B → Finset V := fun _ => Finset.univ

def stEmpty : State V (Checkpoint B) :=
  fUnion (fUnion
    (votes_for_link qF ⟨0, 0⟩ ⟨1, 1⟩ 0 1)
    (votes_for_link qF ⟨1, 1⟩ ⟨1, 2⟩ 1 2))
    (votes_for_link qF ⟨1, 2⟩ ⟨2, 3⟩ 2 3)

theorem wf_stEmpty : votes_from_target_vset_property vsetCP stEmpty := by
  intro x s t s_h t_h _; exact Finset.mem_univ x

theorem q2_qF_CP (t : Checkpoint B) : quorum_2 τ stake vsetCP qF t :=
  ⟨Finset.subset_univ qF, (q2_qF 0).2⟩

theorem sub_00_11 : votes_for_link qF ⟨0, 0⟩ ⟨1, 1⟩ 0 1 ⊆ stEmpty :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left hv)
theorem sub_11_12 : votes_for_link qF ⟨1, 1⟩ ⟨1, 2⟩ 1 2 ⊆ stEmpty :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem sub_12_23 : votes_for_link qF ⟨1, 2⟩ ⟨2, 3⟩ 2 3 ⊆ stEmpty :=
  fun _ hv => mem_fUnion_right hv

theorem sm_00_11 : supermajority_link τ stake vsetCP stEmpty ⟨0, 0⟩ ⟨1, 1⟩ 0 1 :=
  supermajority_link_of_quorum_votes τ stake vsetCP (q2_qF_CP _) sub_00_11 wf_stEmpty
theorem sm_11_12 : supermajority_link τ stake vsetCP stEmpty ⟨1, 1⟩ ⟨1, 2⟩ 1 2 :=
  supermajority_link_of_quorum_votes τ stake vsetCP (q2_qF_CP _) sub_11_12 wf_stEmpty
theorem sm_12_23 : supermajority_link τ stake vsetCP stEmpty ⟨1, 2⟩ ⟨2, 3⟩ 2 3 :=
  supermajority_link_of_quorum_votes τ stake vsetCP (q2_qF_CP _) sub_12_23 wf_stEmpty

theorem cp_11_justified :
    justified τ stake vsetCP (cp_parent ctx) (cp_genesis ctx) stEmpty ⟨1, 1⟩ 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide,
     nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 _) parent_00_11,
     sm_00_11⟩

/--
**The same block, one epoch later, is justified through an empty epoch.**
$`(1, 2)` is justified at height $`2` via the link from $`(1, 1)`.
-/
theorem cp_12_justified :
    justified τ stake vsetCP (cp_parent ctx) (cp_genesis ctx) stEmpty ⟨1, 2⟩ 2 :=
  justified.justified_link cp_11_justified
    ⟨by decide,
     nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 _) parent_11_12,
     sm_11_12⟩

theorem cp_23_justified :
    justified τ stake vsetCP (cp_parent ctx) (cp_genesis ctx) stEmpty ⟨2, 3⟩ 3 :=
  justified.justified_link cp_12_justified
    ⟨by decide,
     nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 _) parent_12_23,
     sm_12_23⟩

/-- The link $`(1,1) \to (1,2)` in the form of {lit}`cp_justification_link_iff`. -/
theorem link_11_12_chain :
    (1 : Nat) < 2 ∧ (1 : B) = ebb ctx 1 1 ∧
      supermajority_link τ stake vsetCP stEmpty ⟨1, 1⟩ ⟨1, 2⟩ 1 2 :=
  (cp_justification_link_iff ctx cp_11_valid cp_12_valid).mp
    ⟨by decide,
     nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 _) parent_11_12,
     sm_11_12⟩

/-- Heights certified by justification are epochs ({lit}`cp_justified_height_eq`). -/
theorem height_12 : (2 : Nat) = (⟨1, 2⟩ : Checkpoint B).epoch :=
  cp_justified_height_eq ctx cp_12_justified

/-! ## Executable check on a finite encoding of the same tree -/

/-- Checkpoints with epoch $`< 4`, as a finite type. -/
abbrev CP := Fin 3 × Fin 4

def toCP : CP → Checkpoint B := fun c => ⟨c.1, c.2.val⟩

def parentCP : CP → CP → Prop := fun a b => cp_parent ctx (toCP a) (toCP b)

instance : DecidableRel parentCP := fun _ _ => inferInstanceAs (Decidable (cp_parent ctx _ _))

def genesisCP : CP := (0, 0)

def vsetF : CP → Finset V := fun _ => Finset.univ

instance (priority := 10000) instFintypeCP : Fintype CP :=
  ⟨⟨(List.finRange 3).flatMap (fun b => (List.finRange 4).map (fun e => (b, e))), by decide⟩,
   fun ⟨b, e⟩ =>
     List.mem_flatMap.mpr ⟨b, List.mem_finRange b, List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩⟩⟩

def stEmptyF : State V CP :=
  fUnion (fUnion
    (votes_for_link qF (0, 0) (1, 1) 0 1)
    (votes_for_link qF (1, 1) (1, 2) 1 2))
    (votes_for_link qF (1, 2) (2, 3) 2 3)

abbrev JE : CP → Nat → Bool :=
  justifiedB τ stake vsetF parentCP genesisCP stEmptyF

#eval JE (0, 0) 0
#eval JE (1, 1) 1
#eval JE (1, 2) 2
#eval JE (2, 3) 3
#eval JE (2, 2) 2
#eval JE (1, 3) 3

theorem cp_12_justified_decide :
    justified τ stake vsetF parentCP genesisCP stEmptyF (1, 2) 2 :=
  (justifiedB_iff τ stake vsetF parentCP genesisCP stEmptyF (1, 2) 2).mp (by decide +kernel)

theorem cp_22_not_justified :
    ¬ justified τ stake vsetF parentCP genesisCP stEmptyF (2, 2) 2 :=
  fun h =>
    absurd ((justifiedB_iff τ stake vsetF parentCP genesisCP stEmptyF (2, 2) 2).mpr h)
      (by decide +kernel)

end GasperBeaconChain.Executable.UseCases.EmptyEpoch
