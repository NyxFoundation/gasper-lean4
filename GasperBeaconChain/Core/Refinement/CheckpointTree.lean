import GasperBeaconChain.Core.Refinement.SlottedChain
import GasperBeaconChain.Core.AtomicDef.HashTree
import GasperBeaconChain.Core.AtomicDef.Grading
import GasperBeaconChain.Core.AtomicDef.Justification
import GasperBeaconChain.Core.Lemmas.HashTree
import GasperBeaconChain.Core.Lemmas.Grading

universe u v

namespace GasperBeaconChain.Core

/-!
# The checkpoint tree of a slotted chain

This file is the second half of the concrete refinement layer. It
builds Gasper's **checkpoint tree** — the tree whose nodes are epoch
boundary pairs $`(B, j)` — from a slotted block chain
({lit}`SlottedChain.lean`), and shows that it is an instance of the
abstract tree of {lit}`HashTree.lean` on which the whole development
is stated, with the epoch as its height grading.

## Construction

* A {lit}`Checkpoint` is a pair $`(\mathsf{block}, \mathsf{epoch})`.
  The same block may appear in many checkpoints (one per epoch in
  which it is the boundary block), which is how Gasper represents
  empty epochs.
* A checkpoint is {lit}`cp_valid` when its block can be the epoch
  boundary block of its epoch, i.e. $`\operatorname{slot}(B) \le jC`.
* The parent of $`(B, j+1)` is $`(\operatorname{EBB}(B, j), j)`
  ({lit}`cp_parent`); the genesis checkpoint is
  $`(\operatorname{genesis}, 0)` ({lit}`cp_genesis`).
* {lit}`on_checkpoint_chain` is Gasper's "$`c_1` lies on the
  checkpoint chain of $`c_2`": $`c_1` is the epoch boundary pair of
  $`c_2`'s block at $`c_1`'s epoch.

## Results

* (R1) {lit}`cp_context` — the checkpoint tree is a
  {name}`HashTreeContext`: irreflexive (epochs differ by one) and
  with at most one parent (the parent is a function of the child).
* (R2) {lit}`cp_graded` — the epoch is a {name}`height_graded`
  height function, so every lemma of {lit}`Lemmas/Grading.lean`
  applies to the checkpoint tree.
* (R3) {lit}`cp_empty_epoch` — **empty epochs are representable**:
  every valid checkpoint $`(B, j)` is the parent of $`(B, j+1)`, the
  same block one epoch later.
* (R4) {lit}`cp_depth` — a valid checkpoint $`(B, j)` is reached
  from the genesis checkpoint by exactly $`j` parent edges.
* (R5) {lit}`cp_ancestor_iff_on_chain` / {lit}`cp_link_correspondence`
  — abstract ancestry in the checkpoint tree coincides with "lies on
  the checkpoint chain".
* {lit}`cp_justification_link_iff` — combining R5 with the abstract
  equivalence {lit}`justification_link_iff_ancestor`: **on the
  checkpoint tree, a justification link is a supermajority link whose
  source lies on the target's checkpoint chain**, with strictly
  increasing epoch. This is Gasper's justification condition.

## Non-assumptions

No finiteness is required, and invalid pairs are allowed to exist as
nodes: the tree laws hold regardless, and validity is a hypothesis
only where the correspondence with epoch boundary blocks is at stake.
-/

variable {Block : Type u}

/--
A **checkpoint**: an epoch boundary pair $`(B, j)` in the sense of
Gasper § 4. The pair, not the block, is the node of the checkpoint
tree; the same block occurs in several checkpoints across empty
epochs. This is the concrete counterpart of the abstract identifier
type $`H` of {lit}`HashTree.lean`, and of the eth2
$`\mathsf{Checkpoint} = (\mathsf{epoch}, \mathsf{root})`.
-/
structure Checkpoint (Block : Type u) where
  block : Block
  epoch : Nat
deriving DecidableEq, Repr

/--
A checkpoint $`(B, j)` is **valid** when its block is within the slot
bound of its epoch:

$$`\operatorname{cp\_valid}(B, j) \;\;\coloneqq\;\; \operatorname{slot}(B) \le jC`

Equivalently ({lit}`ebb_self_iff`), $`B` is its own epoch boundary
block at epoch $`j`. Validity is a predicate rather than a subtype so
that the tree laws and decidability need no coercions; it is assumed
only where the pair must genuinely be an epoch boundary pair.
-/
def cp_valid (ctx : SlottedChainContext Block) (c : Checkpoint Block) : Prop :=
  ctx.slot c.block ≤ c.epoch * ctx.C

/--
The **parent relation of the checkpoint tree**: $`c_1 \to c_2` when
$`c_2` is one epoch later and $`c_1` is the epoch boundary pair of
$`c_2`'s block at $`c_1`'s epoch:

$$`c_1 \to c_2 \;\;\coloneqq\;\; \operatorname{epoch}(c_2) = \operatorname{epoch}(c_1) + 1 \;\wedge\; \operatorname{block}(c_1) = \operatorname{EBB}(\operatorname{block}(c_2),\, \operatorname{epoch}(c_1))`

The parent is determined by the child, so the relation is functional
in the reverse direction; it spans exactly one attestation epoch and
is *not* the slot-level block parent.
-/
def cp_parent (ctx : SlottedChainContext Block) : HashParent (Checkpoint Block) :=
  fun c₁ c₂ =>
    c₂.epoch = c₁.epoch + 1 ∧ c₁.block = ebb ctx c₂.block c₁.epoch

/--
The **genesis checkpoint** $`(\operatorname{genesis}, 0)`.
-/
def cp_genesis (ctx : SlottedChainContext Block) : Checkpoint Block :=
  ⟨ctx.bgenesis, 0⟩

/--
**Gasper's checkpoint chain membership.** $`c_1` lies on the
checkpoint chain of $`c_2` when its epoch is not later and its block
is the epoch boundary block of $`c_2`'s block at that epoch:

$$`\operatorname{epoch}(c_1) \le \operatorname{epoch}(c_2) \;\wedge\; \operatorname{block}(c_1) = \operatorname{EBB}(\operatorname{block}(c_2),\, \operatorname{epoch}(c_1))`

This is the condition in Gasper's justification rule ("the source
checkpoint is on the chain of the target"); {lit}`cp_ancestor_iff_on_chain`
identifies it with abstract ancestry in the checkpoint tree.
-/
def on_checkpoint_chain (ctx : SlottedChainContext Block) (c₁ c₂ : Checkpoint Block) : Prop :=
  c₁.epoch ≤ c₂.epoch ∧ c₁.block = ebb ctx c₂.block c₁.epoch

instance cp_parent_decidable
    [DecidableEq Block]
    (ctx : SlottedChainContext Block) :
    DecidableRel (cp_parent ctx) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance cp_valid_decidable
    (ctx : SlottedChainContext Block)
    (c : Checkpoint Block) :
    Decidable (cp_valid ctx c) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-!
## § 1 Tree laws (R1) and grading (R2)
-/

/--
# The checkpoint parent relation is irreflexive

$`c \to c` is impossible: it would require
$`\operatorname{epoch}(c) = \operatorname{epoch}(c) + 1`.
-/
theorem cp_parent_irreflexive
    (ctx : SlottedChainContext Block) :
    hash_parent_irreflexive (cp_parent ctx) :=
  fun {c₁ _} h heq =>
    Nat.succ_ne_self c₁.epoch
      ((congrArg Checkpoint.epoch heq).trans h.1).symm

/--
# A checkpoint has at most one parent

Two parents of the same child have the same epoch (one less than the
child's) and hence the same block
($`\operatorname{EBB}(\operatorname{block}(c_1), \cdot)` at that
epoch).
-/
theorem cp_at_most_one_parent
    (ctx : SlottedChainContext Block) :
    hash_at_most_one_parent (cp_parent ctx) :=
  fun {c₁ c₂ c₃} h₂ h₃ =>
    have he : c₂.epoch = c₃.epoch := Nat.succ.inj (h₂.1.symm.trans h₃.1)
    have hb : c₂.block = c₃.block :=
      h₂.2.trans
        (Eq.subst (motive := fun e => ebb ctx c₁.block e = c₃.block) he.symm h₃.2.symm)
    match c₂, c₃, hb, he with
    | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/--
# (R1) The checkpoint tree is a hash-tree context

The concrete checkpoint tree packaged as the abstract
{name}`HashTreeContext` on which ancestry, justification and the
safety/liveness theorems are stated. Every theorem of the development
therefore applies to it verbatim.
-/
def cp_context (ctx : SlottedChainContext Block) : HashTreeContext (Checkpoint Block) where
  parent := cp_parent ctx
  genesis := cp_genesis ctx
  parent_irreflexive := cp_parent_irreflexive ctx
  at_most_one_parent := cp_at_most_one_parent ctx

/--
# (R2) The epoch is a height grading of the checkpoint tree

$$`\operatorname{epoch}(\operatorname{genesis}, 0) = 0 \qquad\wedge\qquad c_1 \to c_2 \implies \operatorname{epoch}(c_2) = \operatorname{epoch}(c_1) + 1`

Both are immediate from the definitions. Through this instance all of
{lit}`Lemmas/Grading.lean` — in particular
{lit}`justification_link_iff_ancestor` and {lit}`justified_height_eq`
— applies to the concrete checkpoint tree with heights read as
attestation epochs.
-/
theorem cp_graded
    (ctx : SlottedChainContext Block) :
    height_graded (cp_parent ctx) (cp_genesis ctx) Checkpoint.epoch :=
  ⟨rfl, fun h => h.1⟩

/-!
## § 2 Empty epochs (R3) and depth (R4)
-/

/--
# A parent checkpoint is valid

The parent's block is an epoch boundary block, so it is within the
bound by {lit}`ebb_slot_le`. No validity of the child is needed.
-/
theorem cp_valid_of_parent
    (ctx : SlottedChainContext Block)
    {c₁ c₂ : Checkpoint Block}
    (h : cp_parent ctx c₁ c₂) :
    cp_valid ctx c₁ :=
  Eq.subst (motive := fun x => ctx.slot x ≤ c₁.epoch * ctx.C) h.2.symm
    (ebb_slot_le ctx c₁.epoch c₂.block)

/--
# (R3) Empty epochs are representable

**The same block, one epoch later, is a child checkpoint.** For every
valid checkpoint $`(B, j)`,

$$`(B, j) \;\to\; (B, j+1) .`

# Interpretation

This is the situation of an empty epoch: no block of
$`\operatorname{chain}(B)` has a slot in $`(jC, (j+1)C]`, so
$`\operatorname{EBB}(B, j+1) = B = \operatorname{EBB}(B, j)`, and the
checkpoint chain repeats the block (Gasper § 4: "a block may appear
more than once as a checkpoint on the same chain"). In the abstract
tree the two checkpoints are *distinct nodes* joined by a parent
edge, so irreflexivity of the parent relation is not in tension with
repeated blocks. The executable example
{lit}`Executable/UseCases/EmptyEpoch.lean` justifies such a pair with
a supermajority link.

# Proof

Immediate from {lit}`ebb_of_le`: validity says
$`\operatorname{slot}(B) \le jC`, hence $`\operatorname{EBB}(B, j) = B`.
-/
theorem cp_empty_epoch
    (ctx : SlottedChainContext Block)
    {c : Checkpoint Block}
    (h : cp_valid ctx c) :
    cp_parent ctx c ⟨c.block, c.epoch + 1⟩ :=
  ⟨rfl, (ebb_of_le ctx h).symm⟩

/--
# A valid checkpoint at epoch $`0` is the genesis checkpoint

Validity at epoch $`0` means $`\operatorname{slot}(B) \le 0`, so
$`B` is genesis ({lit}`eq_genesis_of_slot_le_zero`).
-/
theorem cp_valid_zero_eq_genesis
    (ctx : SlottedChainContext Block)
    {B : Block}
    (h : cp_valid ctx ⟨B, 0⟩) :
    (⟨B, 0⟩ : Checkpoint Block) = cp_genesis ctx :=
  congrArg (fun x => (⟨x, 0⟩ : Checkpoint Block))
    (eq_genesis_of_slot_le_zero ctx
      (Eq.subst (motive := fun n => ctx.slot B ≤ n) (Nat.zero_mul ctx.C) h))

/--
# (R4) Depth equals epoch

A valid checkpoint $`(B, j)` is reached from the genesis checkpoint
by exactly $`j` parent edges:

$$`\operatorname{cp\_valid}(B, j) \;\implies\; (\operatorname{genesis}, 0) \xrightarrow{j} (B, j)`

Induction on $`j`. At $`0` the pair is the genesis checkpoint
({lit}`cp_valid_zero_eq_genesis`). At $`j + 1` the parent
$`(\operatorname{EBB}(B, j), j)` is valid by {lit}`ebb_slot_le`, and
the induction hypothesis supplies the path to it.
-/
theorem cp_depth
    (ctx : SlottedChainContext Block) :
    ∀ (j : Nat) (B : Block), cp_valid ctx ⟨B, j⟩ →
      nth_ancestor (cp_parent ctx) j (cp_genesis ctx) ⟨B, j⟩
  | 0, _, h =>
      Eq.subst (motive := fun c => nth_ancestor (cp_parent ctx) 0 (cp_genesis ctx) c)
        (cp_valid_zero_eq_genesis ctx h).symm
        (nth_ancestor.nth_ancestor_0 (cp_genesis ctx))
  | j + 1, B, _ =>
      nth_ancestor.nth_ancestor_nth
        (cp_depth ctx j (ebb ctx B j) (ebb_slot_le ctx j B))
        ⟨rfl, rfl⟩

/-!
## § 3 Ancestry is checkpoint-chain membership (R5)
-/

/--
# Ancestry implies checkpoint-chain membership

If $`c_1` is valid and an ancestor of $`c_2` in the checkpoint tree,
then $`c_1` lies on the checkpoint chain of $`c_2`. Induction on the
ancestry path: the epoch bound is {lit}`height_le_of_ancestor` under
{lit}`cp_graded`; the block equation composes one parent edge
($`\operatorname{block}(x) = \operatorname{EBB}(\operatorname{block}(c_2), \operatorname{epoch}(x))`)
with the induction hypothesis via the tower property
{lit}`ebb_tower`.
-/
theorem on_checkpoint_chain_of_ancestor
    (ctx : SlottedChainContext Block)
    {c₁ c₂ : Checkpoint Block}
    (h₁ : cp_valid ctx c₁)
    (ha : hash_ancestor (cp_parent ctx) c₁ c₂) :
    on_checkpoint_chain ctx c₁ c₂ :=
  match ha with
  | .refl _ => ⟨Nat.le_refl _, (ebb_of_le ctx h₁).symm⟩
  | .step ha' hp =>
      have ih := on_checkpoint_chain_of_ancestor ctx h₁ ha'
      ⟨Nat.le_trans ih.1
         (Eq.subst (motive := fun n => _ ≤ n) hp.1.symm (Nat.le_succ _)),
       ih.2.trans
         ((congrArg (fun x => ebb ctx x c₁.epoch) hp.2).trans
           (ebb_tower ctx ih.1 c₂.block))⟩

/--
# Checkpoint-chain membership implies ancestry (auxiliary)

Auxiliary form of the reverse direction, with the epoch difference
$`k` made explicit: if $`c_2` is valid,
$`\operatorname{epoch}(c_2) = \operatorname{epoch}(c_1) + k`, and
$`\operatorname{block}(c_1) = \operatorname{EBB}(\operatorname{block}(c_2), \operatorname{epoch}(c_1))`,
then $`c_1 \xrightarrow{*} c_2`. Induction on $`k`, generalizing
$`c_2`: at $`k = 0` validity of $`c_2` forces $`c_1 = c_2`; at
$`k + 1` the parent $`(\operatorname{EBB}(\operatorname{block}(c_2), \operatorname{epoch}(c_1) + k),\, \operatorname{epoch}(c_1) + k)`
is valid, and $`c_1` is on its chain by {lit}`ebb_tower`.
-/
theorem ancestor_of_on_checkpoint_chain_aux
    (ctx : SlottedChainContext Block)
    (c₁ : Checkpoint Block) :
    ∀ (k : Nat) (c₂ : Checkpoint Block),
      cp_valid ctx c₂ →
      c₂.epoch = c₁.epoch + k →
      c₁.block = ebb ctx c₂.block c₁.epoch →
      hash_ancestor (cp_parent ctx) c₁ c₂
  | 0, c₂, h₂, he, hb =>
      have he' : c₁.epoch = c₂.epoch := he.symm
      have hb' : c₁.block = c₂.block :=
        hb.trans
          (Eq.subst (motive := fun e => ebb ctx c₂.block e = c₂.block) he'.symm
            (ebb_of_le ctx h₂))
      match c₁, c₂, hb', he' with
      | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => hash_ancestor.refl _
  | k + 1, c₂, _, he, hb =>
      let x : Checkpoint Block := ⟨ebb ctx c₂.block (c₁.epoch + k), c₁.epoch + k⟩
      have hx : cp_parent ctx x c₂ := ⟨he, rfl⟩
      have hxv : cp_valid ctx x := ebb_slot_le ctx (c₁.epoch + k) c₂.block
      have hxb : c₁.block = ebb ctx x.block c₁.epoch :=
        hb.trans (ebb_tower ctx (Nat.le_add_right c₁.epoch k) c₂.block).symm
      hash_ancestor.step
        (ancestor_of_on_checkpoint_chain_aux ctx c₁ k x hxv rfl hxb)
        hx

/--
# Checkpoint-chain membership implies ancestry

If $`c_2` is valid and $`c_1` lies on its checkpoint chain, then
$`c_1` is an ancestor of $`c_2` in the checkpoint tree. The epoch
difference is $`\operatorname{epoch}(c_2) - \operatorname{epoch}(c_1)`
({name}`Nat.add_sub_of_le`), and
{lit}`ancestor_of_on_checkpoint_chain_aux` builds the path.
-/
theorem ancestor_of_on_checkpoint_chain
    (ctx : SlottedChainContext Block)
    {c₁ c₂ : Checkpoint Block}
    (h₂ : cp_valid ctx c₂)
    (hc : on_checkpoint_chain ctx c₁ c₂) :
    hash_ancestor (cp_parent ctx) c₁ c₂ :=
  ancestor_of_on_checkpoint_chain_aux ctx c₁ (c₂.epoch - c₁.epoch) c₂ h₂
    (Nat.add_sub_of_le hc.1).symm hc.2

/--
# (R5) Ancestry in the checkpoint tree is checkpoint-chain membership

**Correspondence theorem.** For valid checkpoints $`c_1, c_2`,

$$`c_1 \xrightarrow{*} c_2 \;\iff\; \operatorname{epoch}(c_1) \le \operatorname{epoch}(c_2) \;\wedge\; \operatorname{block}(c_1) = \operatorname{EBB}(\operatorname{block}(c_2),\, \operatorname{epoch}(c_1))`

The left-hand side is the abstract ancestry relation of
{lit}`HashTree.lean` instantiated at the checkpoint tree; the
right-hand side is Gasper's "$`c_1` is on the checkpoint chain of
$`c_2`". Forward: {lit}`on_checkpoint_chain_of_ancestor` (uses only
validity of $`c_1`). Backward: {lit}`ancestor_of_on_checkpoint_chain`
(uses only validity of $`c_2`).
-/
theorem cp_ancestor_iff_on_chain
    (ctx : SlottedChainContext Block)
    {c₁ c₂ : Checkpoint Block}
    (h₁ : cp_valid ctx c₁)
    (h₂ : cp_valid ctx c₂) :
    hash_ancestor (cp_parent ctx) c₁ c₂ ↔ on_checkpoint_chain ctx c₁ c₂ :=
  ⟨on_checkpoint_chain_of_ancestor ctx h₁,
   ancestor_of_on_checkpoint_chain ctx h₂⟩

/--
# (R5, epoch-bounded form) Ancestry is the epoch boundary block equation

For valid checkpoints with $`\operatorname{epoch}(c_1) \le \operatorname{epoch}(c_2)`,

$$`c_1 \xrightarrow{*} c_2 \;\iff\; \operatorname{block}(c_1) = \operatorname{EBB}(\operatorname{block}(c_2),\, \operatorname{epoch}(c_1)) .`

The form of {lit}`cp_ancestor_iff_on_chain` with the epoch bound
taken as a hypothesis.
-/
theorem cp_link_correspondence
    (ctx : SlottedChainContext Block)
    {c₁ c₂ : Checkpoint Block}
    (h₁ : cp_valid ctx c₁)
    (h₂ : cp_valid ctx c₂)
    (hle : c₁.epoch ≤ c₂.epoch) :
    hash_ancestor (cp_parent ctx) c₁ c₂ ↔ c₁.block = ebb ctx c₂.block c₁.epoch :=
  ⟨fun ha => ((cp_ancestor_iff_on_chain ctx h₁ h₂).mp ha).2,
   fun hb => (cp_ancestor_iff_on_chain ctx h₁ h₂).mpr ⟨hle, hb⟩⟩

/-!
## § 4 Justification links on the checkpoint tree
-/

variable {Validator : Type v}

/--
# A justification link on the checkpoint tree is Gasper's justification condition

**Main refinement theorem.** On the concrete checkpoint tree, with
heights read as epochs, a {name}`justification_link` from a valid
checkpoint $`c_1` to a valid checkpoint $`c_2` is exactly: strictly
increasing epoch, $`c_1` on the checkpoint chain of $`c_2`, and a
supermajority link:

$$`\operatorname{justification\_link}(\sigma, c_1, c_2, \operatorname{epoch}(c_1), \operatorname{epoch}(c_2)) \;\iff\; \operatorname{epoch}(c_1) < \operatorname{epoch}(c_2) \;\wedge\; \operatorname{block}(c_1) = \operatorname{EBB}(\operatorname{block}(c_2), \operatorname{epoch}(c_1)) \;\wedge\; \operatorname{supermajority\_link}(\sigma, c_1, c_2, \operatorname{epoch}(c_1), \operatorname{epoch}(c_2))`

# Proof

{lit}`justification_link_iff_ancestor` under {lit}`cp_graded`
replaces the graded condition
$`c_1 \xrightarrow{\operatorname{epoch}(c_2) - \operatorname{epoch}(c_1)} c_2`
by plain ancestry, and {lit}`cp_link_correspondence` replaces
ancestry by the epoch boundary block equation.

# Interpretation

This closes the gap between the code and the paper: the
"exactly $`h_t - h_s` parent edges" condition of
{name}`justification_link`, which is *not* a statement about
slot-level blocks, is precisely Gasper's "source checkpoint on the
target's checkpoint chain" once the tree is the checkpoint tree. The
only divergence from the paper's raw Definition 4.6 is intentional
and documented: the paper's $`J(G)` does not require chain membership
at all, whereas justification computed per chain (as validators do
when producing valid votes) does.
-/
theorem cp_justification_link_iff
    [DecidableEq Validator]
    [DecidableEq Block]
    [Fintype Validator]
    (ctx : SlottedChainContext Block)
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Checkpoint Block → Finset Validator}
    {st : State Validator (Checkpoint Block)}
    {c₁ c₂ : Checkpoint Block}
    (h₁ : cp_valid ctx c₁)
    (h₂ : cp_valid ctx c₂) :
    justification_link τ stake vset (cp_parent ctx) st c₁ c₂ c₁.epoch c₂.epoch
      ↔
    (c₁.epoch < c₂.epoch ∧
     c₁.block = ebb ctx c₂.block c₁.epoch ∧
     supermajority_link τ stake vset st c₁ c₂ c₁.epoch c₂.epoch) :=
  (justification_link_iff_ancestor (cp_graded ctx)).trans
    ⟨fun ⟨hlt, ha, hsm⟩ =>
        ⟨hlt, (cp_link_correspondence ctx h₁ h₂ (Nat.le_of_lt hlt)).mp ha, hsm⟩,
     fun ⟨hlt, hb, hsm⟩ =>
        ⟨hlt, (cp_link_correspondence ctx h₁ h₂ (Nat.le_of_lt hlt)).mpr hb, hsm⟩⟩

/--
# Justified checkpoints carry their epoch as height

On the checkpoint tree, whatever heights the votes carry, a
{name}`justified` pair $`(c, h)` has $`h = \operatorname{epoch}(c)`:
the instance of {lit}`justified_height_eq` at {lit}`cp_graded`.
-/
theorem cp_justified_height_eq
    [DecidableEq Validator]
    [DecidableEq Block]
    [Fintype Validator]
    (ctx : SlottedChainContext Block)
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Checkpoint Block → Finset Validator}
    {st : State Validator (Checkpoint Block)}
    {c : Checkpoint Block} {h : Nat}
    (hj : justified τ stake vset (cp_parent ctx) (cp_genesis ctx) st c h) :
    h = c.epoch :=
  justified_height_eq (cp_graded ctx) hj

end GasperBeaconChain.Core
