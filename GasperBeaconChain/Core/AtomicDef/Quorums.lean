import GasperBeaconChain.Core.AtomicDef.NatExt
import GasperBeaconChain.Core.AtomicDef.Weight
import GasperBeaconChain.Core.AtomicDef.Slashing

universe u v

namespace GasperBeaconChain.Core

/-!
# Quorums

This file defines the **quorum predicates** that formalise the
supermajority requirements of Casper FFG, together with the
**accountable-safety conclusion** {lit}`q_intersection_slashed`.

## Validator sets

Each block $`b` is associated with a validator set
$`V(b) \subseteq \mathsf{Validator}`, represented by a total function
{lit}`vset : Hash → Finset Validator`. Coq uses a partial finite map
$`\mathsf{vset} : \mathsf{Hash} \rightharpoonup \mathcal{P}(\mathsf{Validator})`
with a totality witness; Lean uses a total function directly.

## Notation

Throughout this file, $`V(b)` denotes {lit}`vset b`,
$`\operatorname{wt}(\cdot)` abbreviates
{lit}`wt stake (·)` (with $`\mathsf{stake}` fixed by context),
$`\sigma` denotes the protocol state {lit}`st`, and the threshold
$`\tau` is fixed by context, hence suppressed in the quorum
operators $`\operatorname{quorum\_1}(vs, b)`,
$`\operatorname{quorum\_2}(vs, b)`.

## Quorum predicates

A subset $`q \subseteq V(b)` is a **$`\frac{1}{3}`-quorum** (resp.
**$`\frac{2}{3}`-quorum**) relative to block $`b` when its weight
meets the corresponding threshold:

$$`\operatorname{quorum}_k(q, b) \;\;\coloneqq\;\; q \subseteq V(b) \;\;\wedge\;\; f_k\bigl(\operatorname{wt}(V(b))\bigr) \le \operatorname{wt}(q)`

where $`f_{1/3} = \tau.\mathsf{one\_third}` and
$`f_{2/3} = \tau.\mathsf{two\_third}` are the threshold functions
from {lit}`NatExt.lean`.

## Accountable-safety conclusion

{lit}`q_intersection_slashed` asserts the existence of two
$`\frac{2}{3}`-quorums whose intersection consists entirely of
slashed validators. This is the **conclusion** of the Accountable
Safety theorem (proved in {lit}`Theories/AccountableSafety.lean`).

## Quorum context

{lit}`QuorumContext` bundles the nonemptiness property of
$`\frac{2}{3}`-quorums, replacing a Coq global axiom with a
first-class value.

Coq source: {lit}`Quorums.v`.
-/

variable {Validator : Type u}
variable {Hash : Type v}

/--
A **$`\frac{1}{3}`-quorum** relative to block $`b`: a subset of the
validator set $`V(b)` whose total stake reaches the one-third
threshold $`f_{1/3}(\operatorname{wt}(V(b)))` for that set.

$$`\operatorname{quorum\_1}(vs, b) \;\;\coloneqq\;\; vs \subseteq V(b) \;\;\wedge\;\; f_{1/3}\bigl(\operatorname{wt}(V(b))\bigr) \le \operatorname{wt}(vs)`

Here $`f_{1/3} = \tau.\mathsf{one\_third}` is the threshold function
from the {name}`Threshold` structure.
-/
def quorum_1
    [DecidableEq Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (vs : Finset Validator)
    (b : Hash) : Prop :=
  vs ⊆ vset b ∧
  τ.one_third (wt stake (vset b)) ≤ wt stake vs

/--
A **$`\frac{2}{3}`-quorum** relative to block $`b`: a subset of the
validator set $`V(b)` whose total stake reaches the two-thirds
threshold $`f_{2/3}(\operatorname{wt}(V(b)))` for that set.

$$`\operatorname{quorum\_2}(vs, b) \;\;\coloneqq\;\; vs \subseteq V(b) \;\;\wedge\;\; f_{2/3}\bigl(\operatorname{wt}(V(b))\bigr) \le \operatorname{wt}(vs)`

Here $`f_{2/3} = \tau.\mathsf{two\_third}`. This is the central
quorum predicate of the formalization: {lit}`supermajority_link`,
{lit}`justification_link`, and {lit}`finalized` all require
$`\frac{2}{3}`-quorums.
-/
def quorum_2
    [DecidableEq Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (vs : Finset Validator)
    (b : Hash) : Prop :=
  vs ⊆ vset b ∧
  τ.two_third (wt stake (vset b)) ≤ wt stake vs

instance quorum_1_decidable
    [DecidableEq Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (vs : Finset Validator)
    (b : Hash) :
    Decidable (quorum_1 τ stake vset vs b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance quorum_2_decidable
    [DecidableEq Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (vs : Finset Validator)
    (b : Hash) :
    Decidable (quorum_2 τ stake vset vs b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/--
The **accountable-safety conclusion**. There exist two blocks
$`b_L, b_R` — possibly distinct, and (since $`\mathsf{vset}` is
assigned per block) possibly with different validator sets
$`V(b_L), V(b_R)` — together with two $`\frac{2}{3}`-quorums
$`q_L \subseteq V(b_L)`, $`q_R \subseteq V(b_R)` such that every
validator in their intersection is {name}`slashed`:

$$`\begin{gathered} \exists\, b_L\, b_R\, q_L\, q_R, \\ q_L \subseteq V(b_L) \;\wedge\; q_R \subseteq V(b_R) \;\wedge\; \operatorname{quorum\_2}(q_L, b_L) \;\wedge\; \operatorname{quorum\_2}(q_R, b_R) \\ \wedge\;\; \forall v,\; v \in q_L \;\to\; v \in q_R \;\to\; \operatorname{slashed}(\sigma, v) \end{gathered}`

The explicit subset conditions $`q_L \subseteq V(b_L)`,
$`q_R \subseteq V(b_R)` are already entailed by {name}`quorum_2`
but are kept here to match the Coq definition.

Allowing $`V(b_L) \ne V(b_R)` is what lets one statement serve the
dynamic-validator-set setting, where the two finalized blocks may
be governed by different validator sets; when the validator set is
held fixed across blocks the two coincide.
-/
def q_intersection_slashed
    [DecidableEq Validator]
    [DecidableEq Hash]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (st : State Validator Hash) : Prop :=
  ∃ bL bR : Hash,
  ∃ qL qR : Finset Validator,
    qL ⊆ vset bL ∧
    qR ⊆ vset bR ∧
    quorum_2 τ stake vset qL bL ∧
    quorum_2 τ stake vset qR bR ∧
    ∀ v : Validator, v ∈ qL → v ∈ qR → slashed st v

/--
The **nonemptiness** property of $`\frac{2}{3}`-quorums: every
$`\frac{2}{3}`-quorum contains at least one validator.

$$`\forall\, b\, q,\;\; \operatorname{quorum\_2}(q, b) \;\implies\; \exists\, v,\; v \in q`

This is needed in the Plausible Liveness proof to extract a witness
from a quorum. Coq postulates it as a global axiom; Lean defines it
as an explicit property so it can be assumed via
{lit}`QuorumContext` or derived from positive threshold values (see
{lit}`Lemmas/Quorums.lean`).
-/
def quorum_2_nonempty_property
    [DecidableEq Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator) : Prop :=
  ∀ (b : Hash) (q : Finset Validator),
    quorum_2 τ stake vset q b → q.Nonempty

/--
A **bundled quorum context** carrying the
{name}`quorum_2_nonempty_property`: every $`\frac{2}{3}`-quorum is
inhabited. This replaces the Coq global axiom with a first-class
value that can be assumed, constructed, or derived.
-/
structure QuorumContext
    [DecidableEq Validator]
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator) where
  quorum_2_nonempty :
    quorum_2_nonempty_property (Hash := Hash) τ stake vset

end GasperBeaconChain.Core
