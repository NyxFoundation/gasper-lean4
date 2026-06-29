universe u

namespace GasperBeaconChain.Core

/-!
# Block tree

This file defines the **block tree** structure that underlies
Casper FFG checkpoints. A type $`H` of block identifiers is equipped
with a binary relation on $`H` (the parent relation), written
$`h_1 \to h_2` when $`h_1` is the parent of $`h_2`. Two structural
conditions are required:

* **Irreflexivity** — no block is its own parent ($`h \to h` is
  excluded).
* **At-most-one-parent** — each block has at most one predecessor.

A distinguished element $`g \in H` (genesis) is included in the
context (its role as the base case of justification is established
in {lit}`Justification.lean`).

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

## Block-tree shape

The parent relation grows downward from genesis $`g`: an edge $`x \to y`
means $`x` is the parent of $`y`. Every non-genesis block has **at most one**
incoming edge (at-most-one-parent) and no block points to itself
(irreflexivity). Ancestry $`\xrightarrow{*}` is reachability along these edges
(e.g. $`g \xrightarrow{*} d`); the graded $`\xrightarrow{n}` counts the steps
(here $`g \xrightarrow{3} d`).

```
%%mermaid
graph TD
  g["g : genesis"]
  g --> a
  a --> c
  c --> d
  g --> b
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
The type of a **parent relation** on block identifiers: a binary
relation on $`H`. We write $`h_1 \to h_2` for the assertion that
$`h_1` is the parent of $`h_2`.
-/
abbrev HashParent (Hash : Type u) : Type u :=
  Hash → Hash → Prop

/--
**Irreflexivity** of the parent relation: no block is its own parent.

$$`\forall\, h_1\, h_2,\quad h_1 \to h_2 \;\implies\; h_1 \ne h_2`

In particular, no block satisfies $`h \to h` (self-loops are
excluded). See also {lit}`hash_at_most_one_parent`, which
independently ensures uniqueness of the predecessor.

This is a property of a given parent relation, not a global axiom.
-/
def hash_parent_irreflexive {Hash : Type u} (parent : HashParent Hash) : Prop :=
  ∀ {h₁ h₂ : Hash}, parent h₁ h₂ → h₁ ≠ h₂

/--
**At-most-one-parent** (functional inverse): if two blocks are both
parents of the same child, they are equal.

$$`\forall\, h_1\, h_2\, h_3,\quad (h_2 \to h_1) \;\wedge\; (h_3 \to h_1) \;\implies\; h_2 = h_3`

Equivalently, the map $`h_1 \mapsto h_2` where $`h_2 \to h_1` is a
partial function — each block has at most one parent.

This is a property of a given parent relation, not a global axiom.
-/
def hash_at_most_one_parent {Hash : Type u} (parent : HashParent Hash) : Prop :=
  ∀ {h₁ h₂ h₃ : Hash}, parent h₂ h₁ → parent h₃ h₁ → h₂ = h₃

/--
A **bundled block-tree context** $`(H,\, \to,\, g)`: it packages the
ambient block-tree structure on which Casper FFG ancestry and
justification links are stated.

# Data

* {lit}`parent` — a parent relation $`(\to)` on $`H`
  ({name}`HashParent`),
* {lit}`genesis` — a distinguished block $`g \in H`.

# Laws

* {lit}`parent_irreflexive` — no block is its own parent
  ({name}`hash_parent_irreflexive`),
* {lit}`at_most_one_parent` — parenthood is functional in the
  reverse direction: a block has at most one immediate parent
  ({name}`hash_at_most_one_parent`).

# Intended semantics

An inhabitant models the minimal rooted-tree-like fragment needed
to speak about ancestry ($`\xrightarrow{*}`, $`\xrightarrow{n}`)
and justification links in the Gasper core. Bundling the relation,
the base point, and the two laws lets downstream definitions
quantify over a single context object rather than repeat the
hypotheses.

# Non-assumptions

The structure does *not* assume:

* reachability of every block from $`g` (no connectivity is
  imposed);
* acyclicity beyond immediate irreflexivity — a two-cycle
  $`a \to b`, $`b \to a` is *not* excluded, since each of $`a, b`
  still has a unique immediate parent;
* existence of children for any block;
* finiteness of the block universe $`H`;
* uniqueness of ancestry paths (where needed, this is established
  separately, not baked in as a field).

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
$`h_1` to $`h_2`.

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
difference $`h_t - h_s`.
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
