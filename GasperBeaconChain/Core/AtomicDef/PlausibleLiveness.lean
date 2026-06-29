import GasperBeaconChain.Core.AtomicDef.Justification

universe u v

namespace GasperBeaconChain.Core

/-!
# Plausible liveness: definitions

This file defines the **hypotheses and conclusions** of the Plausible
Liveness theorem (proved in {lit}`Theories/PlausibleLiveness.lean`).

## Notation

As in {lit}`Quorums.lean` and {lit}`Justification.lean`,
$`\sigma` and $`\sigma'` denote protocol states ({lit}`st`,
{lit}`st'`), $`\sigma \ni (v, s, t, h_s, h_t)` denotes
{lit}`vote_msg`, and parameters $`\tau`, $`\mathsf{stake}`,
$`\mathsf{vset}`, $`\mathsf{parent}`, $`\mathsf{genesis}` are
suppressed in formulas.

## Block existence

{lit}`blocks_exist_high_over` asserts that blocks exist at
arbitrarily large heights above a given base block. An alternative
Coq-faithful version {lit}`blocks_exist_high_over_coq` is provided
for reference (it is unsatisfiable, owing to the placement of the
height guard inside the existential).

## Honest-majority hypotheses

The following predicates formalise the assumption that a sufficient
fraction of validators behaves honestly:

* {lit}`justified_source_votes` — every vote has a justified source
* {lit}`forward_link_votes` — every vote is a valid forward link
* {lit}`good_votes` — every quorum member satisfies both of the above
* {lit}`two_thirds_good` — every block has an unslashed
  $`\frac{2}{3}`-quorum

## Uniqueness and maximality

* {lit}`highest_justified` — a given block is the unique highest
  justified block
* {lit}`maximal_justification_link` — a justification link with
  maximal target height

## State extension

* {lit}`unslashed_can_extend` — new votes come only from unslashed
  validators
* {lit}`no_new_slashed` — no validator becomes newly slashed

Coq source: {lit}`PlausibleLiveness.v`. Definitions are ordered by
dependency.
-/


-- § Block existence (no type class assumptions beyond Hash)


variable {Hash : Type v}

/--
Coq-faithful version of {lit}`blocks_exist_high_over`, with the height guard
trapped inside the existential:

$$`\forall n,\ \exists\, block,\ \operatorname{nth\_ancestor} n\, base\, block \ \wedge\ 1 < n`

Note: this definition universally quantifies over all $`n`, including $`n = 0`
and $`n = 1`, where the condition $`1 < n` is false. Thus the conjunction
$`\cdots \wedge\ 1 < n` forces the existential to produce, at $`n \le 1`, a
witness whose second component proves $`1 < n` — which is absurd. Hence the
predicate is impossible to satisfy, i.e. it implies $`\bot`.

The improved version {lit}`blocks_exist_high_over` avoids this by moving the
$`1 < n` guard to the left of the existential.
-/
def blocks_exist_high_over_coq
    (parent : HashParent Hash)
    (base : Hash) : Prop :=
  ∀ n : Nat, ∃ block : Hash, nth_ancestor parent n base block ∧ 1 < n

/--
Improved version: blocks exist at all heights $`n > 1` above $`base`,

$$`\forall n,\ 1 < n \ \rightarrow\ \exists\, block,\ \operatorname{nth\_ancestor} n\, base\, block`

This separates the height guard $`1 < n` from the existential,
making the predicate satisfiable for any block with sufficiently
many descendants. It is the Plausible Liveness precondition that
the underlying proposal mechanism keeps producing blocks: Casper
and Gasper establish liveness only "provided new blocks can be
created by the underlying blockchain".
-/
def blocks_exist_high_over
    (parent : HashParent Hash)
    (base : Hash) : Prop :=
  ∀ n : Nat, 1 < n → ∃ block : Hash, nth_ancestor parent n base block


-- § Protocol-level definitions (require full type class assumptions)


variable {Validator : Type u}
variable [DecidableEq Validator]
variable [DecidableEq Hash]
variable [Fintype Validator]

/--
Every vote by validator $`v` in state $`\sigma` has a
**justified source**:

$$`\forall\, s\, t\, h_s\, h_t,\;\; \sigma \ni (v, s, t, h_s, h_t) \;\implies\; \operatorname{justified}(\sigma, s, h_s)`

Coq: {lit}`justified_source_votes`.
-/
def justified_source_votes
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (v : Validator) : Prop :=
  ∀ (s t : Hash) (s_h t_h : Nat),
    vote_msg st v s t s_h t_h →
    justified τ stake vset parent genesis st s s_h

/--
Every vote by validator $`v` constitutes a **valid forward link**
in the block tree:

$$`\forall\, s\, t\, h_s\, h_t,\;\; \sigma \ni (v, s, t, h_s, h_t) \;\implies\; h_s < h_t \;\wedge\; s \xrightarrow{h_t - h_s} t`

Coq: {lit}`forward_link_votes`.
-/
def forward_link_votes
    (parent : HashParent Hash)
    (st : State Validator Hash)
    (v : Validator) : Prop :=
  ∀ (s t : Hash) (s_h t_h : Nat),
    vote_msg st v s t s_h t_h →
    s_h < t_h ∧ nth_ancestor parent (t_h - s_h) s t

/--
The global well-formedness condition asserting that every validator
occurring in any $`\frac{2}{3}`-quorum over $`\sigma` casts only
justified and forward votes: each such validator satisfies both
{lit}`justified_source_votes` and {lit}`forward_link_votes`.

$$`\begin{gathered} \forall\, b\, q,\;\; \operatorname{quorum\_2}(q, b) \;\implies\; \forall\, v \in q, \\ \operatorname{justified\_source\_votes}(v) \;\;\wedge\;\; \operatorname{forward\_link\_votes}(v) \end{gathered}`

# Scope

A property of the entire state $`\sigma`, quantifying over all
blocks $`b` and all $`\frac{2}{3}`-quorums $`q` at $`b`.

# Interpretation

This packages the semantic hygiene needed for plausible-liveness
arguments: every validator that participates in a relevant quorum
behaves in a way compatible with justified, forward progress.

# Role in later theory

A standing hypothesis of the Plausible Liveness development (proved
in {lit}`Theories/PlausibleLiveness.lean`). It is a hypothesis
schema, not a theorem of this file.

# Non-assumptions

This property does *not* say that every validator is unslashed, nor
that every vote in $`\sigma` belongs to some quorum. It constrains
only the validators that appear inside relevant
$`\frac{2}{3}`-quorums.

Coq: {lit}`good_votes`.
-/
def good_votes
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash) : Prop :=
  ∀ (b : Hash) (q2 : Finset Validator),
    quorum_2 τ stake vset q2 b →
    ∀ v : Validator, v ∈ q2 →
      justified_source_votes τ stake vset parent genesis st v ∧
      forward_link_votes parent st v

/--
For every block $`b`, there exists a $`\frac{2}{3}`-quorum of
**unslashed** validators:

$$`\forall\, b,\;\; \exists\, q,\;\; \operatorname{quorum\_2}(q, b) \;\wedge\; \forall\, v \in q,\; \neg\,\operatorname{slashed}(\sigma, v)`

This is the honest-supermajority hypothesis of Plausible Liveness:
every block's validator set contains a two-thirds quorum of
validators unslashed in $`\sigma` — the formal counterpart of "at
least two-thirds of the stake is honest".

Coq: {lit}`two_thirds_good`.
-/
def two_thirds_good
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (st : State Validator Hash) : Prop :=
  ∀ b : Hash,
    ∃ q2 : Finset Validator,
      quorum_2 τ stake vset q2 b ∧
      ∀ v : Validator, v ∈ q2 → ¬ slashed st v

/--
The property that $`b` at height $`h` is the **unique highest
justified block**: any justified block at height $`\ge h` must
equal $`b` at the same height.

$$`\forall\, b'\, h',\;\; h \le h' \;\implies\; \operatorname{justified}(\sigma, b', h') \;\implies\; b' = b \;\wedge\; h' = h`

Coq: {lit}`highest_justified`.
-/
def highest_justified
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (b : Hash) (b_h : Nat) : Prop :=
  ∀ (b' : Hash) (b_h' : Nat),
    b_h ≤ b_h' →
    justified τ stake vset parent genesis st b' b_h' →
    b' = b ∧ b_h' = b_h

/--
There exists at least one justification link with a justified
source:

$$`\exists\, s\, t\, h_s\, h_t,\;\; \operatorname{justified}(\sigma, s, h_s) \;\wedge\; \operatorname{justification\_link}(\sigma, s, t, h_s, h_t)`

Coq: {lit}`has_justification_link`.
-/
def has_justification_link
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash) : Prop :=
  ∃ s t : Hash, ∃ s_h t_h : Nat,
    justified τ stake vset parent genesis st s s_h ∧
    justification_link τ stake vset parent st s t s_h t_h

/--
A justification link whose target height $`h_t` is **maximal**
among all justification links in $`\sigma`:

$$`\operatorname{justification\_link}(\sigma, s, t, h_s, h_t) \;\;\wedge\;\; \forall\, s'\, t'\, h_s'\, h_t',\;\; \operatorname{justification\_link}(\sigma, s', t', h_s', h_t') \;\implies\; h_t' \le h_t`

Coq: {lit}`maximal_justification_link`.
-/
def maximal_justification_link
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (st : State Validator Hash)
    (s t : Hash) (s_h t_h : Nat) : Prop :=
  justification_link τ stake vset parent st s t s_h t_h ∧
  ∀ (s' t' : Hash) (s_h' t_h' : Nat),
    justification_link τ stake vset parent st s' t' s_h' t_h' → t_h' ≤ t_h

/--
The extended state $`\sigma'` only adds votes from **unslashed**
validators:

$$`\forall\, v\, s\, t\, h_s\, h_t,\;\; \sigma' \ni (v, s, t, h_s, h_t) \;\implies\; \sigma \ni (v, s, t, h_s, h_t) \;\lor\; \neg\,\operatorname{slashed}(\sigma, v)`

# Scope

A property of a *pair* of states $`(\sigma, \sigma')`.

# Interpretation

Every vote present in $`\sigma'` either already belonged to
$`\sigma` or was cast by a validator not slashed in $`\sigma`. New
voting activity is thus attributed only to previously-unslashed
validators.

# Role in later theory

A standing hypothesis on the state extension built in the Plausible
Liveness argument, paired with {lit}`no_new_slashed` to keep the
extension free of fresh slashing.

# Non-assumptions

It does *not* require $`\sigma \subseteq \sigma'`; a vote of
$`\sigma'` absent from $`\sigma` is permitted as long as its caster
is unslashed in $`\sigma`. It says nothing about votes of $`\sigma`
that may be missing from $`\sigma'`.

Coq: {lit}`unslashed_can_extend`.
-/
def unslashed_can_extend
    (st st' : State Validator Hash) : Prop :=
  ∀ (v : Validator) (s t : Hash) (s_h t_h : Nat),
    vote_msg st' v s t s_h t_h →
    vote_msg st v s t s_h t_h ∨ ¬ slashed st v

/--
**No new slashing**: any validator slashed in $`\sigma'` was
already slashed in $`\sigma`.

$$`\forall\, v,\;\; \operatorname{slashed}(\sigma', v) \;\implies\; \operatorname{slashed}(\sigma, v)`

# Scope

A property of a *pair* of states $`(\sigma, \sigma')`.

# Interpretation

Slashing status is monotone backwards along the transition from
$`\sigma` to $`\sigma'`: the extended state introduces no new
slashing evidence.

# Role in later theory

Used to control state-extension steps in plausible-liveness
arguments, where one must add votes without creating new slashings.

# Non-assumptions

It does *not* require $`\sigma \subseteq \sigma'`, nor does it
constrain which votes are added or removed except insofar as they
affect slashing.

Coq: {lit}`no_new_slashed`.
-/
def no_new_slashed
    (st st' : State Validator Hash) : Prop :=
  ∀ v : Validator, slashed st' v → slashed st v

end GasperBeaconChain.Core
