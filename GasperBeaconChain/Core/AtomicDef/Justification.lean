import Mathlib.Data.Fintype.Basic
import GasperBeaconChain.Core.AtomicDef.HashTree
import GasperBeaconChain.Core.AtomicDef.State
import GasperBeaconChain.Core.AtomicDef.Quorums

universe u v

namespace GasperBeaconChain.Core

/-!
# Justification and finalization

This file defines the core protocol predicates of Casper FFG:
the chain from individual votes to justified and finalized blocks.

## Notation

As in {lit}`Quorums.lean`, $`V(b)` denotes {lit}`vset b` and
$`\sigma` denotes the protocol state. We write
$`h_1 \to h_2` for the parent relation (see {lit}`HashTree.lean`).
Parameters $`\tau`, $`\mathsf{stake}`, $`\mathsf{vset}`, and
$`\mathsf{parent}` are suppressed in formulas;
$`\mathsf{genesis}` is written explicitly where it appears.

## From votes to supermajority links

{lit}`link_supporters` collects the validators who voted for a
given source-target link. When this set forms a
$`\frac{2}{3}`-quorum (see {lit}`Quorums.lean`), the link is a
**supermajority link** ({lit}`supermajority_link`).

## Justification link

A {lit}`justification_link` adds two structural conditions to a
supermajority link: **forward direction** ($`h_s < h_t`) and
**checkpoint-tree ancestry** ($`s \xrightarrow{h_t - h_s} t`). The
tree is Gasper's checkpoint tree ({lit}`HashTree.lean`), whose nodes
are epoch boundary pairs and whose edges span one attestation epoch;
the graded condition is therefore "the source checkpoint lies on the
target's checkpoint chain" (see the docstring of
{lit}`justification_link` and {lit}`Lemmas/Grading.lean`).

## Justification (inductive)

{lit}`justified` is defined inductively: genesis is justified at
height $`0`, and a target is justified if its source is justified
and there is a justification link from source to target.

## Finalization and $`k`-finalization

{lit}`finalized` adds a direct-child supermajority link to
justification. {lit}`k_finalized` generalises this to a depth-$`k`
chain, closed by a single height-$`k` supermajority link.

## Well-formedness

{lit}`votes_from_target_vset_property` is the property that every
vote supporter belongs to the target's validator set. Coq
postulates this as a global axiom; Lean defines it as an explicit
property of states.

Coq source: {lit}`Justification.v`.
-/

variable {Validator : Type u}
variable {Hash : Type v}

/--
The set of validators who voted for a given source-target link:

$$`\operatorname{link\_supporters}(\sigma, s, t, h_s, h_t) = \{\, v \mid \sigma \ni (v, s, t, h_s, h_t) \,\}`

It is a finite set of the validators satisfying the vote predicate. And this finiteness is exactly why $`\mathsf{Validator}` is required to be a finite type.
-/
def link_supporters
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (st : State Validator Hash)
    (s t : Hash)
    (s_h t_h : Nat) :
    Finset Validator :=
  Finset.univ.filter (fun v =>
    vote_msg st v s t s_h t_h)

/--
Membership characterization for {name}`link_supporters`:
$`v \in \operatorname{link\_supporters}(\sigma, s, t, h_s, h_t) \iff \sigma \ni (v, s, t, h_s, h_t)`.

Filtering the finite universe of validators by the vote predicate, membership reduces to the predicate itself, since membership in the universe is automatic.
-/
theorem mem_link_supporters
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    {st : State Validator Hash}
    {s t : Hash}
    {s_h t_h : Nat}
    {v : Validator} :
    v ∈ link_supporters st s t s_h t_h
      ↔
    vote_msg st v s t s_h t_h :=
  show v ∈ Finset.univ.filter (fun v => vote_msg st v s t s_h t_h) ↔ _ from
    (Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))

/--
Well-formedness of votes with respect to target validator sets.

Coq postulated this globally as an axiom: every supporter of a link to target
$`t` belongs to the validator set of $`t`,

$$`\forall\, x\, s\, t\, h_s\, h_t,\;\; x \in \operatorname{link\_supporters}(\sigma, s, t, h_s, h_t) \;\implies\; x \in V(t)`

Lean Core does not use a global axiom.
Instead, this is a property of a state relative to {lit}`vset`.
-/
def votes_from_target_vset_property
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (vset : Hash → Finset Validator)
    (st : State Validator Hash) : Prop :=
  ∀ {x : Validator}
    {s t : Hash}
    {s_h t_h : Nat},
    x ∈ link_supporters st s t s_h t_h →
    x ∈ vset t

/--
A **supermajority link** from source $`(s, h_s)` to target
$`(t, h_t)`: the supporters of this link form a
$`\frac{2}{3}`-quorum of the target's validator set $`V(t)` — that
is, they lie in $`V(t)` and their combined stake meets the
two-thirds threshold $`f_{2/3}(\operatorname{wt}(V(t)))`
({name}`quorum_2`).

$$`\operatorname{supermajority\_link}(\sigma, s, t, h_s, h_t) \;\;\coloneqq\;\; \operatorname{quorum\_2}\bigl(\operatorname{link\_supporters}(\sigma, s, t, h_s, h_t),\; t\bigr)`

# Dependence on the state

The state $`\sigma` enters *only* through {name}`link_supporters`,
i.e. through which validators have cast the corresponding vote
message in $`\sigma`. The threshold $`\tau`, the stake function,
and the validator set $`V(t)` are ambient parameters.

# Non-assumptions

This definition does *not* require:

* forward direction $`h_s < h_t`;
* any ancestry relation between $`s` and $`t`;
* justification of the source $`(s, h_s)`;
* uniqueness or maximality of the link.

Those conditions are added separately in {lit}`justification_link`.
-/
def supermajority_link
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (st : State Validator Hash)
    (s t : Hash)
    (s_h t_h : Nat) : Prop :=
  quorum_2 τ stake vset
    (link_supporters st s t s_h t_h)
    t

/--
Definitional unfolding of {name}`supermajority_link`.
-/
theorem supermajority_link_def
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Hash → Finset Validator}
    {st : State Validator Hash}
    {s t : Hash}
    {s_h t_h : Nat} :
    supermajority_link τ stake vset st s t s_h t_h
      ↔
    quorum_2 τ stake vset (link_supporters st s t s_h t_h) t :=
  Iff.rfl

instance supermajority_link_decidable
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (st : State Validator Hash)
    (s t : Hash)
    (s_h t_h : Nat) :
    Decidable (supermajority_link τ stake vset st s t s_h t_h) :=
  inferInstanceAs (Decidable (quorum_2 τ stake vset _ t))

/--
A **justification link** from source $`(s, h_s)` to target
$`(t, h_t)`, defined as a supermajority link that additionally
satisfies forward direction and tree ancestry:

$$`\operatorname{justification\_link}(\sigma, s, t, h_s, h_t) \;\;\coloneqq\;\; h_s < h_t \;\;\wedge\;\; s \xrightarrow{h_t - h_s} t \;\;\wedge\;\; \operatorname{supermajority\_link}(\sigma, s, t, h_s, h_t)`

The three conjuncts ensure: (1) the link points strictly forward
in height ($`h_s < h_t`); (2) $`t` is reachable from $`s` by
*exactly* $`h_t - h_s` parent edges of the checkpoint tree
($`s \xrightarrow{h_t - h_s} t`, the graded ancestry of
{name}`nth_ancestor`), so the checkpoint-height gap coincides with
the tree distance; (3) the link carries $`\frac{2}{3}`-quorum
support ({name}`supermajority_link`). The grading in (2) is
essential: an ungraded "$`t` is some descendant of $`s`" would
leave the path length unconstrained, whereas pinning it to
$`h_t - h_s` is what lets justification heights track tree depth
({lit}`justified_depth`). Since (1) gives $`h_s < h_t`, the
difference $`h_t - h_s` is a genuine positive step count, never
collapsed by truncated subtraction.

# Reading the ancestry condition

The parent relation is that of Gasper's **checkpoint tree**
({lit}`HashTree.lean`): a node is an epoch boundary pair $`(B, j)`,
one parent edge spans one attestation epoch, and heights are epochs,
i.e. depths in the tree. Read against a *slot-level block tree* the
condition "exactly $`h_t - h_s` block parents" would be wrong —
consecutive checkpoints are separated by arbitrarily many blocks, or
by none in an empty epoch, where the same block is both checkpoints.
Read on the checkpoint tree it is exactly Gasper's condition: under
the grading of the tree by the epoch ({lit}`height_graded`) the
graded condition is *equivalent* to plain ancestry "$`s` lies on the
checkpoint chain of $`t`" — this is
{lit}`justification_link_iff_ancestor` in {lit}`Lemmas/Grading.lean`
— and on the concrete checkpoint tree built from slotted blocks it is
literally
$`\operatorname{block}(s) = \operatorname{EBB}(\operatorname{block}(t),\, \operatorname{epoch}(s))`
({lit}`cp_justification_link_iff` in
{lit}`Refinement/CheckpointTree.lean`). Empty epochs are represented
by distinct nodes with the same block ({lit}`cp_empty_epoch`;
executable example {lit}`Executable/UseCases/EmptyEpoch.lean`).

# Relation to Gasper Definition 4.6

Gasper's raw set $`J(G)` of justified pairs is generated from
supermajority links alone; it does not require the source to lie on
the target's checkpoint chain. The ancestry conjunct here is a
deliberate strengthening, inherited from the Coq model: it is
justification as computed along a chain from the attestations valid
for that chain (an attestation's source is a checkpoint on the chain
of its target), which is the notion the safety argument is about.
Every justification link of this model is a supermajority link, so
the justified pairs of this model form a subset of $`J(G)`.

# Non-assumptions

This relation does *not* assert that the source $`(s, h_s)` is
already justified; that global closure condition is supplied
separately by the {lit}`justified` link rule. A justification link
is a *local* edge, not a statement about reachability from genesis.
-/
def justification_link
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (st : State Validator Hash)
    (s t : Hash)
    (s_h t_h : Nat) : Prop :=
  s_h < t_h ∧
  nth_ancestor parent (t_h - s_h) s t ∧
  supermajority_link τ stake vset st s t s_h t_h

/--
**Inductive justification.** A checkpoint $`b` at height $`h` is
justified in state $`\sigma` if it is reachable from genesis via a
finite chain of justification links. Two constructors:

$$`\dfrac{\vphantom{X}}{\mathsf{genesis} \;\text{justified at}\; 0}\;\textsf{genesis} \qquad\qquad \dfrac{s \;\text{justified at}\; h_s \qquad \operatorname{justification\_link}(\sigma, s, t, h_s, h_t)}{t \;\text{justified at}\; h_t}\;\textsf{link}`

The heights along any justification chain are strictly increasing
(since each link satisfies $`h_s < h_t`), so every chain is finite.
Moreover the height certified for $`b` is its depth in the
checkpoint tree: $`g \xrightarrow{h} b` ({lit}`justified_depth`,
{lit}`Lemmas/Grading.lean`).
-/
inductive justified
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash) :
    Hash → Nat → Prop
| justified_genesis :
    justified τ stake vset parent genesis st genesis 0
| justified_link
    {s t : Hash}
    {s_h t_h : Nat} :
    justified τ stake vset parent genesis st s s_h →
    justification_link τ stake vset parent st s t s_h t_h →
    justified τ stake vset parent genesis st t t_h

/--
**Finalization.** A checkpoint $`b` at height $`h` is finalized when
it is justified and there exists a direct child $`c` (i.e.
$`b \to c`, a single parent edge) for which there is a
supermajority link from $`(b, h)` to $`(c, h + 1)`:

$$`\operatorname{finalized}(\sigma, b, h) \;\;\coloneqq\;\; \operatorname{justified}(\sigma, b, h) \;\;\wedge\;\; \exists\, c,\; (b \to c) \;\wedge\; \operatorname{supermajority\_link}(\sigma, b, c, h, h{+}1)`

Unlike a general justification link (which may span multiple
heights), the finalization condition requires a link of distance
exactly $`1`.

# Non-assumptions

No uniqueness of the finalizing child $`c` is asserted, and no
safety or irreversibility theorem is built into the definition;
those belong to later theory files. The condition is intentionally
*local* — a single justified checkpoint plus one direct
supermajority link.
-/
def finalized
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (b : Hash)
    (b_h : Nat) : Prop :=
  justified τ stake vset parent genesis st b b_h ∧
  ∃ c : Hash,
    parent b c ∧
    supermajority_link τ stake vset st b c b_h (b_h + 1)

/--
**$`k`-finalization**, the depth-$`k` generalization of
{name}`finalized` (Gasper's $`k`-finalization). A checkpoint $`b` at
height $`b_h` is $`k`-finalized when some chain of $`k + 1` checkpoints
$`ls = (ls_0, \dots, ls_k)` starts at $`ls_0 = b`, has each $`ls_n`
justified at height $`b_h + n` and reached from $`b` in exactly
$`n` parent steps, and carries a supermajority link from $`b` to
its last checkpoint $`ls_k` spanning the full height gap $`k`:

$$`\operatorname{k\_finalized}(\sigma, b, b_h, k) \;\;\coloneqq\;\; \begin{gathered} 1 \le k \;\;\wedge\;\; \exists\, ls,\;\; |ls| = k + 1 \;\wedge\; ls_0 = b \\ \wedge\;\; \bigl(\forall n \le k,\;\; \operatorname{justified}(\sigma, ls_n, b_h + n) \;\wedge\; b \xrightarrow{n} ls_n\bigr) \\ \wedge\;\; \operatorname{supermajority\_link}(\sigma, b, ls_k, b_h, b_h + k) \end{gathered}`

At $`k = 1` this is exactly {name}`finalized` — one child $`ls_1`
of $`b` carrying a height-$`1` supermajority link (the equivalence
is {lit}`finalized_means_one_finalized`).

**Range of the justification clause.** The quantifier
$`\forall n \le k` asserts justification of *every* $`ls_n`, the
last one included. That last instance,
$`\operatorname{justified}(\sigma, ls_k, b_h + k)`, is redundant:
from $`ls_0 = b` justified (case $`n = 0`), the ancestry
$`b \xrightarrow{k} ls_k` (case $`n = k`, noting
$`(b_h + k) - b_h = k`), and $`b_h < b_h + k` (since $`1 \le k`),
the supermajority link
$`\operatorname{supermajority\_link}(\sigma, b, ls_k, b_h, b_h + k)`
is a {name}`justification_link`, so the {name}`justified` link
rule already derives $`\operatorname{justified}(\sigma, ls_k, b_h + k)`.
The definition is therefore equivalent to the form that justifies
only $`ls_0, \dots, ls_{k-1}`. The ancestry conjunct at $`n = k`
is, by contrast, *not* redundant — it supplies the witness
$`b \xrightarrow{k} ls_k` consumed downstream (e.g. by
{lit}`k_finalized_last_justified`).

Implementation: $`ls` is a {lit}`List Hash` (as in the Coq
development) rather than a length-indexed vector. The index $`ls_0`
is {lit}`ls.headD b`, a general $`ls_n` is {lit}`ls.getD n b`, and
$`ls_k` is {lit}`ls.getLastD b`; these agree with the intended
indexing because $`|ls| = k + 1`.
-/
def k_finalized
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (b : Hash)
    (b_h k : Nat) : Prop :=
  1 ≤ k ∧
  ∃ ls : List Hash,
    ls.length = k + 1 ∧
    ls.headD b = b ∧
    (∀ n : Nat,
      n ≤ k →
        justified τ stake vset parent genesis st
          (ls.getD n b)
          (b_h + n)
        ∧
        nth_ancestor parent n b (ls.getD n b)) ∧
    supermajority_link τ stake vset st
      b
      (ls.getLastD b)
      b_h
      (b_h + k)

end GasperBeaconChain.Core
