import GasperBeaconChain.Core.AtomicDef.HashTree

universe u

namespace GasperBeaconChain.Core

/-!
# Height grading of the checkpoint tree

This file isolates the single structural property that makes the
graded ancestry condition of {lit}`justification_link` (see
{lit}`Justification.lean`) faithful to Gasper: **the height of a
checkpoint is its depth in the checkpoint tree**.

## Motivation

In Gasper, a checkpoint is an *epoch boundary pair* $`(B, j)` and the
checkpoint tree is graded by the epoch $`j`: the parent of $`(B, j+1)`
is $`(\operatorname{EBB}(B, j), j)`, and $`(B, 0)` is always the
genesis pair. Consequently the epoch of a pair equals its distance
from genesis along parent edges, and "the source checkpoint lies on
the target's checkpoint chain" is the same as "the target is reached
from the source by *exactly* $`h_t - h_s` parent edges" — which is the
condition $`s \xrightarrow{h_t - h_s} t` used by
{lit}`justification_link`.

The abstract model in {lit}`HashTree.lean` does not bake this grading
into {name}`HashTreeContext` (it is not needed by the safety and
liveness theorems). This file states the grading as an explicit
hypothesis, {lit}`height_graded`, so that the equivalence above can be
*proved* ({lit}`justification_link_iff_ancestor` in
{lit}`Lemmas/Grading.lean`) rather than asserted in prose, and so that
the concrete checkpoint tree of {lit}`Refinement/CheckpointTree.lean`
can be shown to satisfy it ({lit}`cp_graded`).

## What is *not* assumed

The grading is a property of a *given* height function $`\mathrm{ht}`
with respect to a parent relation and a genesis; it is a hypothesis of
individual theorems, never a global axiom, and none of the existing
definitions or theorems depend on it.
-/

/--
A height function $`\mathrm{ht} : H \to \mathbb{N}` is a **grading**
of the checkpoint tree $`(H, \to, g)` when genesis has height $`0`
and every parent edge raises the height by exactly one:

$$`\mathrm{ht}(g) = 0 \qquad\wedge\qquad \forall\, h_1\, h_2,\;\; h_1 \to h_2 \;\implies\; \mathrm{ht}(h_2) = \mathrm{ht}(h_1) + 1`

# Intended semantics

In Gasper's checkpoint tree the nodes are epoch boundary pairs
$`(B, j)` and $`\mathrm{ht}(B, j) = j` is the attestation epoch. The
parent of $`(B, j+1)` is $`(\operatorname{EBB}(B, j), j)`, one epoch
below, and $`(B, 0)` is the genesis pair for every $`B`; so the epoch
is a grading in exactly this sense. The concrete construction
{lit}`cp_parent` in {lit}`Refinement/CheckpointTree.lean` satisfies
this property ({lit}`cp_graded`).

# Consequences

Under this hypothesis (see {lit}`Lemmas/Grading.lean`):

* along any ancestry path the height is monotone
  ({lit}`height_le_of_ancestor`);
* the step count of a graded path is forced to be the height
  difference ({lit}`height_eq_of_nth_ancestor`), so
  $`s \xrightarrow{*} t` and $`s \xrightarrow{\mathrm{ht}(t) - \mathrm{ht}(s)} t`
  coincide ({lit}`nth_ancestor_of_ancestor`);
* the graded condition of {lit}`justification_link` is equivalent to
  plain checkpoint ancestry ({lit}`justification_link_iff_ancestor`);
* heights along any {lit}`justified` chain are forced to equal the
  true depth ({lit}`justified_height_eq`).

# Non-assumptions

Nothing is assumed about blocks with no relation to genesis, about
finiteness, or about acyclicity beyond what {name}`HashTreeContext`
already provides. The property is stated for an arbitrary
{name}`HashParent`, not only for a bundled context.
-/
def height_graded
    {Hash : Type u}
    (parent : HashParent Hash)
    (genesis : Hash)
    (ht : Hash → Nat) : Prop :=
  ht genesis = 0 ∧
  ∀ {h₁ h₂ : Hash}, parent h₁ h₂ → ht h₂ = ht h₁ + 1

end GasperBeaconChain.Core
