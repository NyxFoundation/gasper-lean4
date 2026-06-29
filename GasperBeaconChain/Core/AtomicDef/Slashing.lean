import GasperBeaconChain.Core.AtomicDef.State

universe u v

namespace GasperBeaconChain.Core

/-!
# Slashing conditions

This file defines two predicates — equivocation (double vote,
Casper's (S1)) and surround vote (Casper's (S2)) — each parameterised
by a protocol state $`\sigma` and a validator $`v`. Both assert the
**existence** of a particular configuration of $`v`'s votes within
$`\sigma`. Their disjunction is {lit}`slashed`.

Throughout this file we write
$`\sigma \ni (v, s, t, h_s, h_t)` for the membership predicate
{name}`vote_msg`, i.e. the five-tuple
$`(v,\, s,\, t,\, h_s,\, h_t)` belongs to the finite vote set $`\sigma`.

No global axioms are used; the conditions are direct logical definitions
over protocol states.

## The two conditions, pictured

**(S1) double vote** — validator $`v` casts two links to *distinct* targets
$`t_1 \ne t_2` at the *same* target height $`h_t`; this configuration is exactly
{lit}`slashed_double_vote` (the conclusion node bridges to its definition):

```
%%mermaid
graph LR
  v(("validator v")) -->|"link 1"| t1["t₁ at height hₜ"]
  v -->|"link 2"| t2["t₂ at height hₜ"]
  t1 -.->|"distinct targets, same height"| slashed_double_vote
  t2 -.-> slashed_double_vote
```

**(S2) surround vote** — on the height axis, $`v`'s vote 1 surrounds vote 2:
$`h_{s_1} < h_{s_2} < h_{t_2} < h_{t_1}`. {lit}`slashed_surround_vote` keeps the
two **outer** inequalities $`h_{s_1} < h_{s_2}` and $`h_{t_2} < h_{t_1}` (the
middle one is the inner vote's forward-link well-formedness):

```
%%mermaid
graph LR
  hs1["hₛ₁ : vote 1 source"] --> hs2["hₛ₂ : vote 2 source"]
  hs2 --> ht2["hₜ₂ : vote 2 target"]
  ht2 --> ht1["hₜ₁ : vote 1 target"]
  ht1 -.-> slashed_surround_vote
```

Coq source: {lit}`Slashing.v`.
-/

/--
**Equivocation (double vote)** — Casper's slashing condition (S1).

State $`\sigma` contains an equivocation by validator $`v` when there
exist two votes by $`v` with **distinct target checkpoints**
$`t_1 \ne t_2` but the **same target height** $`h_t`:

$$`\exists\, t_1\, t_2,\; t_1 \ne t_2 \;\wedge\; \exists\, s_1\, h_{s_1}\, s_2\, h_{s_2}\, h_t,\quad \sigma \ni (v, s_1, t_1, h_{s_1}, h_t) \;\wedge\; \sigma \ni (v, s_2, t_2, h_{s_2}, h_t)`

The target height $`h_t` appears in both votes (the shared slot), the
target blocks $`t_1 \ne t_2` differ (the conflict), and the source
checkpoints $`(s_1, h_{s_1})`, $`(s_2, h_{s_2})` are existentially
quantified without further constraints.

Casper's (S1) forbids *any* two distinct attestations of equal
target height; the predicate here is its instance in which the two
targets differ ($`t_1 \ne t_2`), which is precisely the instance the
accountable-safety argument produces. Two distinct checkpoints
justified at one common height force the shared members of their
$`\frac{2}{3}`-quorums to have voted for $`t_1 \ne t_2` at that
height, i.e. to satisfy this predicate.
-/
def slashed_double_vote
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    (st : State Validator Hash)
    (v : Validator) : Prop :=
  ∃ t₁ t₂ : Hash,
    t₁ ≠ t₂ ∧
    ∃ s₁ : Hash,
    ∃ s₁_h : Nat,
    ∃ s₂ : Hash,
    ∃ s₂_h : Nat,
    ∃ t_h : Nat,
      vote_msg st v s₁ t₁ s₁_h t_h ∧
      vote_msg st v s₂ t₂ s₂_h t_h

/--
**Surround vote** — Casper's slashing condition (S2).

While equivocation concerns two votes at the same target height, the
surround condition concerns the **source and target heights** of two
votes. The condition holds for validator $`v` in state $`\sigma` when
$`\sigma` contains two of $`v`'s votes whose height pairs satisfy a
strict ordering on both sides:

$$`\begin{gathered} \exists\, s_1\, t_1\, h_{s_1}\, h_{t_1}\, s_2\, t_2\, h_{s_2}\, h_{t_2}, \\ \sigma \ni (v, s_1, t_1, h_{s_1}, h_{t_1}) \;\wedge\; \sigma \ni (v, s_2, t_2, h_{s_2}, h_{t_2}) \;\wedge\; h_{s_1} < h_{s_2} \;\wedge\; h_{t_2} < h_{t_1} \end{gathered}`

The two strict inequalities constrain the four heights as follows:

$$`h_{s_1} \;<\; h_{s_2} \qquad\text{and}\qquad h_{t_2} \;<\; h_{t_1}`

That is, vote 1 has the strictly lower source height and the strictly
higher target height. When both votes are well-formed forward links
(i.e. $`h_{s_i} < h_{t_i}`), both endpoints of the inner interval
$`[h_{s_2},\, h_{t_2}]` lie strictly inside the outer interval
$`[h_{s_1},\, h_{t_1}]` — this is stronger than mere proper
containment $`\subsetneq`, which requires only one endpoint to
differ.

Casper's (S2) is the full chain
$`h_{s_1} < h_{s_2} < h_{t_2} < h_{t_1}`; this predicate keeps the
two **outer** inequalities and omits the middle one
$`h_{s_2} < h_{t_2}`, which is exactly the forward-link
well-formedness of the inner vote. Hence the definition does not
require well-formedness and operates purely on the four height
values: on forward-link votes the omitted inequality holds
automatically, so the two forms coincide, while as a raw predicate
this is the relaxation of (S2) that drops that assumption.

The definition does not refer to the temporal order in which the votes
were cast; it is purely a property of the pair of votes present in
$`\sigma`.
-/
def slashed_surround_vote
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    (st : State Validator Hash)
    (v : Validator) : Prop :=
  ∃ s₁ : Hash,
  ∃ t₁ : Hash,
  ∃ s₁_h : Nat,
  ∃ t₁_h : Nat,
  ∃ s₂ : Hash,
  ∃ t₂ : Hash,
  ∃ s₂_h : Nat,
  ∃ t₂_h : Nat,
    vote_msg st v s₁ t₁ s₁_h t₁_h ∧
    vote_msg st v s₂ t₂ s₂_h t₂_h ∧
    s₁_h < s₂_h ∧
    t₂_h < t₁_h

/--
The disjunction of the two slashing conditions:

$$`\operatorname{slashed}(\sigma, v) \;\;\coloneqq\;\; \text{equivocation}(\sigma, v) \;\;\lor\;\; \text{surround-vote}(\sigma, v)`

A validator $`v` is **slashed** in state $`\sigma` when $`\sigma`
witnesses an equivocation by $`v`, a surround vote by $`v`, or both.

Both conditions feed this disjunction; the three nodes are the real
declarations (hover for the signature, click to jump):

```
%%mermaid
graph LR
  slashed_double_vote -->|"or"| slashed
  slashed_surround_vote -->|"or"| slashed
```

This is the predicate that appears inside the universal quantifier of
{lit}`q_intersection_slashed`.
-/
def slashed
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    (st : State Validator Hash)
    (v : Validator) : Prop :=
  slashed_double_vote st v ∨ slashed_surround_vote st v

end GasperBeaconChain.Core
