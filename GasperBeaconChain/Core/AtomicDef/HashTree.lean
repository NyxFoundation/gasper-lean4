universe u

namespace GasperBeaconChain.Core

/-!
# Checkpoint tree

This file defines the **checkpoint tree** structure on which Casper
FFG justification and finalization are stated. A type $`H` of
checkpoint identifiers is equipped with a binary relation on $`H`
(the parent relation), written $`h_1 \to h_2` when $`h_1` is the
parent of $`h_2`. Two structural conditions are required:

* **Irreflexivity** — no checkpoint is its own parent ($`h \to h` is
  excluded).
* **At-most-one-parent** — each checkpoint has at most one
  predecessor.

A distinguished element $`g \in H` (genesis) is included in the
context (its role as the base case of justification is established
in {lit}`Justification.lean`).

## Nodes are checkpoints, not blocks

The Coq development this file is ported from fixes the intended
reading at the outset: *"We consider the checkpoint tree of blocks,
and so a 'block' refers to a 'checkpoint block' throughout"*
({lit}`HashTree.v`). The same convention holds throughout this
development — wherever the prose says "block", a node of the
checkpoint tree is meant — and it is spelled out here in Gasper's
terms:

* A node $`h \in H` is an **epoch boundary pair** $`(B, j)` in the
  sense of Gasper § 4: a block *together with* an attestation epoch.
  The eth2 counterpart is {lit}`Checkpoint = (epoch, root)`.
* The **same block root may occur as several distinct nodes**. When
  an epoch contains no block of a chain, the pairs $`(B, j)` and
  $`(B, j+1)` are both checkpoints of that chain (Gasper § 4: "a block
  may appear more than once as a checkpoint on the same chain"). They
  are different elements of $`H`.
* A **parent edge spans one attestation epoch**: the parent of
  $`(B, j+1)` is $`(\operatorname{EBB}(B, j),\, j)`, where
  $`\operatorname{EBB}` is the epoch boundary block. It is *not* the
  slot-level parent relation between blocks — several blocks, or
  none, may lie between two consecutive checkpoints.
* Consequently the tree is **graded by the epoch**: $`(B, 0)` is the
  genesis pair for every $`B`, so the depth of $`(B, j)` is exactly
  $`j`. The height fields $`h_s, h_t` of votes ({lit}`State.lean`) are
  attestation epochs, i.e. depths in this tree. This is what makes
  the graded ancestry condition $`s \xrightarrow{h_t - h_s} t` of
  {lit}`justification_link` the right one: under the grading it is
  *equivalent* to "$`s` lies on the checkpoint chain of $`t`" — proved
  as {lit}`justification_link_iff_ancestor` in
  {lit}`Lemmas/Grading.lean`, with the grading hypothesis
  {lit}`height_graded` of {lit}`Grading.lean`.

Irreflexivity is a property of checkpoint *nodes*: the edge
$`(B, j) \to (B, j+1)` joins two distinct nodes that share a block, so
the law does not exclude empty epochs.

The concrete construction of this tree from slotted blocks — nodes as
pairs, parents via $`\operatorname{EBB}`, and the proofs that it
satisfies the laws below and is graded by the epoch — is carried out
in {lit}`Refinement/SlottedChain.lean` and
{lit}`Refinement/CheckpointTree.lean` ({lit}`cp_context`,
{lit}`cp_graded`, {lit}`cp_empty_epoch`, {lit}`cp_link_correspondence`).

## Ancestry relations

On top of the parent relation the file defines two inductive
closures:

* {lit}`hash_ancestor` — the reflexive-transitive closure
  $`(\xrightarrow{*})`, capturing ancestry
* {lit}`nth_ancestor` — the graded (distance-indexed) version
  $`(\xrightarrow{n})`, capturing exact-length ancestry

Both are Prop-valued inductive types; {name}`Decidable` bridges live
in the {lit}`Executable` layer.

Coq source: {lit}`HashTree.v`. The Coq development uses a boolean
relation {lit}`hash_parent : rel Hash` and computes reachability via
{lit}`connect`; in Lean these are replaced by Prop-valued inductive
closures, preserving the mathematical content.

## Checkpoint-tree shape

The parent relation grows downward from genesis $`g`: an edge $`x \to y`
means $`x` is the parent of $`y`, one epoch later. Every non-genesis
checkpoint has **at most one** incoming edge (at-most-one-parent) and no
checkpoint points to itself (irreflexivity). Ancestry $`\xrightarrow{*}`
is reachability along these edges (e.g. $`g \xrightarrow{*} d`); the
graded $`\xrightarrow{n}` counts the steps (here $`g \xrightarrow{3} d`).
In the example, $`a` and $`c` carry the same block root $`B_1` — epoch
$`2` is empty on that chain — yet they are distinct checkpoints.

```
%%mermaid
graph TD
  g["g = (B₀, 0) : genesis"]
  g --> a["a = (B₁, 1)"]
  a --> c["c = (B₁, 2) — same block as a"]
  c --> d["d = (B₂, 3)"]
  g --> b["b = (B₃, 1)"]
```

Over a parent relation ({lit}`HashParent`) the file layers exactly three
declarations: the two inductive closures of the edge relation and the bundling
context. The nodes below are those real declarations — hover any one for its
signature and click to jump to it.

```
%%mermaid
graph LR
  HashTreeContext -->|"bundles parent, genesis, laws"| HashParent
  HashParent -->|"reflexive-transitive closure"| hash_ancestor
  HashParent -->|"graded by step count n"| nth_ancestor
```
-/

/--
The type of a **parent relation** on checkpoint identifiers: a binary
relation on $`H`. We write $`h_1 \to h_2` for the assertion that
$`h_1` is the parent of $`h_2` — under the checkpoint-tree reading,
that $`h_2` is the checkpoint one epoch after $`h_1` on the same
chain.
-/
abbrev HashParent (Hash : Type u) : Type u :=
  Hash → Hash → Prop

/--
**Irreflexivity** of the parent relation: no checkpoint is its own
parent.

$$`\forall\, h_1\, h_2,\quad h_1 \to h_2 \;\implies\; h_1 \ne h_2`

In particular, no checkpoint satisfies $`h \to h` (self-loops are
excluded). See also {lit}`hash_at_most_one_parent`, which
independently ensures uniqueness of the predecessor.

The law concerns checkpoint *nodes*, not block roots: two consecutive
checkpoints $`(B, j) \to (B, j+1)` of an empty epoch share a block
root but are distinct nodes, and are not excluded.

This is a property of a given parent relation, not a global axiom.
-/
def hash_parent_irreflexive {Hash : Type u} (parent : HashParent Hash) : Prop :=
  ∀ {h₁ h₂ : Hash}, parent h₁ h₂ → h₁ ≠ h₂

/--
**At-most-one-parent** (functional inverse): if two checkpoints are
both parents of the same child, they are equal.

$$`\forall\, h_1\, h_2\, h_3,\quad (h_2 \to h_1) \;\wedge\; (h_3 \to h_1) \;\implies\; h_2 = h_3`

Equivalently, the map $`h_1 \mapsto h_2` where $`h_2 \to h_1` is a
partial function — each checkpoint has at most one parent (on the
concrete checkpoint tree the parent of $`(B, j+1)` is the function
$`(\operatorname{EBB}(B, j), j)` of the child).

This is a property of a given parent relation, not a global axiom.
-/
def hash_at_most_one_parent {Hash : Type u} (parent : HashParent Hash) : Prop :=
  ∀ {h₁ h₂ h₃ : Hash}, parent h₂ h₁ → parent h₃ h₁ → h₂ = h₃

/--
A **bundled checkpoint-tree context** $`(H,\, \to,\, g)`: it packages
the ambient checkpoint-tree structure on which Casper FFG ancestry
and justification links are stated.

# Data

* {lit}`parent` — a parent relation $`(\to)` on $`H`
  ({name}`HashParent`),
* {lit}`genesis` — the genesis checkpoint $`g \in H`.

# Laws

* {lit}`parent_irreflexive` — no checkpoint is its own parent
  ({name}`hash_parent_irreflexive`),
* {lit}`at_most_one_parent` — parenthood is functional in the
  reverse direction: a checkpoint has at most one immediate parent
  ({name}`hash_at_most_one_parent`).

# Intended semantics

An inhabitant models the minimal rooted-tree-like fragment needed
to speak about ancestry ($`\xrightarrow{*}`, $`\xrightarrow{n}`)
and justification links in the Gasper core. The nodes are Gasper's
epoch boundary pairs $`(B, j)` and each edge spans one attestation
epoch (see the module introduction). Bundling the relation, the base
point, and the two laws lets downstream definitions quantify over a
single context object rather than repeat the hypotheses. The
concrete checkpoint tree of {lit}`Refinement/CheckpointTree.lean` is
an inhabitant ({lit}`cp_context`).

# Non-assumptions

The structure does *not* assume:

* reachability of every checkpoint from $`g` (no connectivity is
  imposed);
* acyclicity beyond immediate irreflexivity — a two-cycle
  $`a \to b`, $`b \to a` is *not* excluded, since each of $`a, b`
  still has a unique immediate parent;
* existence of children for any checkpoint;
* finiteness of the checkpoint universe $`H`;
* uniqueness of ancestry paths (where needed, this is established
  separately, not baked in as a field);
* that distinct nodes carry distinct block roots — $`H` is a type of
  *checkpoints*, and several nodes may share a block (empty epochs);
* that heights are depths — the grading of the tree by the epoch is
  a separate hypothesis ({lit}`height_graded`, {lit}`Grading.lean`),
  not needed by the safety and liveness theorems and therefore not
  bundled here.

Those properties, when required, belong to separate lemmas or
stronger contexts.

# Provenance

This replaces the global parameters and axioms of the Coq
development with a single first-class value.
-/
structure HashTreeContext (Hash : Type u) where
  parent : HashParent Hash
  genesis : Hash
  parent_irreflexive : hash_parent_irreflexive parent
  at_most_one_parent : hash_at_most_one_parent parent

/--
The **reflexive-transitive closure** of the parent relation, written
$`h_1 \xrightarrow{*} h_2` (informally, "$`h_1` is an ancestor of
$`h_2`, or $`h_1 = h_2`"). Defined by two constructors:

$$`\dfrac{\vphantom{X}}{h \xrightarrow{*} h}\;\textsf{refl} \qquad\qquad \dfrac{h_1 \xrightarrow{*} h_2 \qquad h_2 \to h_3}{h_1 \xrightarrow{*} h_3}\;\textsf{step}`

{lit}`refl` provides the zero-length path (reflexivity), and
{lit}`step` extends an existing path by one parent edge on the
right. By induction on a proof of $`h_1 \xrightarrow{*} h_2` one
obtains a finite (possibly empty) sequence of parent edges from
$`h_1` to $`h_2`. Under the checkpoint-tree reading,
$`h_1 \xrightarrow{*} h_2` says that $`h_1` lies on the checkpoint
chain of $`h_2` (Gasper § 4); on the concrete checkpoint tree this is
{lit}`cp_link_correspondence`.

This is the Prop-valued replacement for Coq's boolean reachability
function {lit}`connect hash_parent`.
-/
inductive hash_ancestor {Hash : Type u} (parent : HashParent Hash) :
    Hash → Hash → Prop
| refl (h : Hash) :
    hash_ancestor parent h h
| step {h₁ h₂ h₃ : Hash} :
    hash_ancestor parent h₁ h₂ →
    parent h₂ h₃ →
    hash_ancestor parent h₁ h₃

/--
**Distance-indexed (graded) ancestry**. The proposition
$`h_1 \xrightarrow{n} h_2` asserts that $`h_2` is reachable from
$`h_1` by **exactly** $`n` parent steps. Defined by two
constructors:

$$`\dfrac{\vphantom{X}}{h \xrightarrow{0} h}\;\textsf{base} \qquad\qquad \dfrac{h_1 \xrightarrow{n} h_2 \qquad h_2 \to h_3}{h_1 \xrightarrow{n+1} h_3}\;\textsf{step}`

The step constructor increments the distance index by one
({lit}`Nat.succ n`).

Mathematically, the ungraded closure {name}`hash_ancestor` corresponds
to $`h_1 \xrightarrow{*} h_2 \iff \exists\, n,\; h_1 \xrightarrow{n} h_2`.
The graded version is needed in {lit}`justification_link`, where the
number of parent steps from source to target must equal the height
difference $`h_t - h_s`. Since one parent edge of the checkpoint tree
spans one attestation epoch and heights are epochs, the two relations
coincide there: under the grading {lit}`height_graded`,
$`s \xrightarrow{*} t` already implies
$`s \xrightarrow{\mathrm{ht}(t) - \mathrm{ht}(s)} t`
({lit}`nth_ancestor_of_ancestor`, {lit}`Lemmas/Grading.lean`).
-/
inductive nth_ancestor {Hash : Type u} (parent : HashParent Hash) :
    Nat → Hash → Hash → Prop
| nth_ancestor_0 (h : Hash) :
    nth_ancestor parent 0 h h
| nth_ancestor_nth {n : Nat} {h₁ h₂ h₃ : Hash} :
    nth_ancestor parent n h₁ h₂ →
    parent h₂ h₃ →
    nth_ancestor parent (Nat.succ n) h₁ h₃

end GasperBeaconChain.Core
