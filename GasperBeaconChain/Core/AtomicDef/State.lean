import Mathlib.Data.Finset.Basic

universe u v

namespace GasperBeaconChain.Core

/-!
# Votes and states

A **vote** (attestation) is a five-tuple
$`(v,\, s,\, t,\, h_s,\, h_t)` recording that validator $`v` supports
a link from source checkpoint $`s` at height $`h_s` to target
checkpoint $`t` at height $`h_t`. A **protocol state** $`\sigma` is a
finite set of such votes.

The central predicate of this file is {lit}`vote_msg`, which asserts
membership of a vote in a state:
$`\sigma \ni (v, s, t, h_s, h_t)`. This predicate is the foundation
for all quorum and slashing definitions in subsequent files.

## Representation choice

A state is represented *extensionally* as a {name}`Finset` of
votes ({lit}`State` unfolds to {lit}`Finset (Vote Validator Hash)`).
Three consequences follow from this choice:

* duplicate identical votes collapse — a vote is either present or
  absent, never present "twice";
* the state records only extensional membership, not the order in
  which votes were inserted;
* no temporal or network metadata (timestamps, rounds, delivery
  order) is stored at this layer.

This file therefore models the *logical content* of a vote state,
not its network history. The representation is a design choice, not
a mathematical necessity.

Coq source: {lit}`State.v`. Coq represents a vote as a nested tuple;
Lean uses a structure with named fields. The two types
{lit}`Validator : Type u` and {lit}`Hash : Type v` live in separate
universes, avoiding an unnecessary restriction.

## A vote as a link

Each vote is a directed **link** from a source checkpoint $`(s, h_s)` to a
target checkpoint $`(t, h_t)`, labelled by the attesting validator $`v` (top
row). Bundled with $`v` and the two heights, that link is a {lit}`Vote`, and the
predicate {lit}`vote_msg` asserts that the {lit}`Vote` belongs to the state
$`\sigma`, a {lit}`State` (bottom row). The identifier nodes {lit}`Vote`,
{lit}`vote_msg`, and {lit}`State` are the real declarations: hover for the
signature and click to jump to the definition.

```
%%mermaid
graph LR
  source["source (s, hₛ)"] -->|"validator v"| target["target (t, hₜ)"]
  target -->|"bundled with v, hₛ, hₜ"| Vote
  Vote -->|"vote_msg"| State
```
-/

/--
A **Casper FFG vote** — the atomic element of a protocol state.
A vote pairs an attesting validator $`v` with a source checkpoint
$`(s, h_s)` and a target checkpoint $`(t, h_t)`, where
$`\mathsf{Validator}` and $`\mathsf{Hash}` are the validator and
checkpoint-identifier types respectively:

$$`(v,\; s,\; t,\; h_s,\; h_t) \;\in\; \mathsf{Validator} \times \mathsf{Hash} \times \mathsf{Hash} \times \mathbb{N} \times \mathbb{N}`

The five fields correspond to:

* {lit}`validator` — $`v`, the attesting validator,
* {lit}`source` — $`s`, the source checkpoint identifier,
* {lit}`target` — $`t`, the target checkpoint identifier,
* {lit}`sourceHeight` — $`h_s`, the source height,
* {lit}`targetHeight` — $`h_t`, the target height.

The presence or absence of a vote in a state $`\sigma` is queried
via {lit}`vote_msg` and forms the basis of quorum and slashing
predicates in subsequent files.

# Checkpoints and heights

The identifiers $`s, t` name nodes of the **checkpoint tree**
({lit}`HashTree.lean`): epoch boundary pairs $`(B, j)`, not bare
block roots. The heights $`h_s, h_t` are the **attestation epochs**
of the two checkpoints, which under the checkpoint-tree reading are
their depths in the tree. The eth2 counterpart of a vote is an
attestation's FFG vote $`(\mathsf{source}, \mathsf{target})` with
$`\mathsf{Checkpoint} = (\mathsf{epoch}, \mathsf{root})`; the
height fields here play the role of the two {lit}`epoch` components.

Since a checkpoint identifier already determines its epoch, the
height fields are *redundant* with the identifiers on a well-formed
chain. They are carried explicitly, as in the Coq model, because
slashing conditions ({lit}`Slashing.lean`) are stated on heights.
The model does **not** require a vote's heights to agree with the
tree: a state may contain votes with inconsistent heights. This is
deliberate — the state space is a superset of the protocol-reachable
one, so the safety theorems, which quantify over all states, are only
strengthened, and an adversary gains nothing: along justification
chains the heights are forced to be the true depths anyway
({lit}`justified_depth`, {lit}`justified_height_eq` in
{lit}`Lemmas/Grading.lean`).
-/
structure Vote (Validator : Type u) (Hash : Type v) where
  validator : Validator
  source : Hash
  target : Hash
  sourceHeight : Nat
  targetHeight : Nat
deriving DecidableEq, Repr

/--
A **protocol state** is a finite set of votes:
$`\sigma \in \mathcal{P}_{\mathrm{fin}}(\mathsf{Vote})`.

This corresponds to Coq's {lit}`{fset Vote}`.
-/
abbrev State
    (Validator : Type u)
    (Hash : Type v)
    [DecidableEq Validator]
    [DecidableEq Hash] :=
  Finset (Vote Validator Hash)

/--
The **membership predicate** for votes in a state. Writing
$`\sigma \ni (v, s, t, h_s, h_t)` for {lit}`vote_msg st v s t s_h t_h`,
this asserts that the vote $`\langle v, s, t, h_s, h_t \rangle`
belongs to the finite set $`\sigma`:

$$`\operatorname{vote\_msg}(\sigma, v, s, t, h_s, h_t) \;\;\coloneqq\;\; \langle v,\, s,\, t,\, h_s,\, h_t \rangle \in \sigma`

This is the foundational predicate from which
{lit}`link_supporters`, {lit}`slashed_double_vote`, and
{lit}`slashed_surround_vote` are built.
-/
def vote_msg
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    (st : State Validator Hash)
    (v : Validator)
    (s t : Hash)
    (s_h t_h : Nat) : Prop :=
  ({ validator := v
     source := s
     target := t
     sourceHeight := s_h
     targetHeight := t_h } : Vote Validator Hash) ∈ st

/--
{name}`vote_msg` is decidable: the underlying {name}`Vote` type
derives {name}`DecidableEq`, so membership in the finite set
$`\sigma` is decided by {name}`Finset.decidableMem`.
-/
instance vote_msg_decidable
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    (st : State Validator Hash)
    (v : Validator)
    (s t : Hash)
    (s_h t_h : Nat) :
    Decidable (vote_msg st v s t s_h t_h) :=
  Finset.decidableMem _ st

/-- Projection of the validator component. -/
def vote_val
    {Validator : Type u}
    {Hash : Type v}
    (vote : Vote Validator Hash) : Validator :=
  vote.validator

/-- Projection of the source checkpoint. -/
def vote_source
    {Validator : Type u}
    {Hash : Type v}
    (vote : Vote Validator Hash) : Hash :=
  vote.source

/-- Projection of the target checkpoint. -/
def vote_target
    {Validator : Type u}
    {Hash : Type v}
    (vote : Vote Validator Hash) : Hash :=
  vote.target

/-- Projection of the source height. -/
def vote_source_height
    {Validator : Type u}
    {Hash : Type v}
    (vote : Vote Validator Hash) : Nat :=
  vote.sourceHeight

/-- Projection of the target height. -/
def vote_target_height
    {Validator : Type u}
    {Hash : Type v}
    (vote : Vote Validator Hash) : Nat :=
  vote.targetHeight

/--
**$`\eta`-expansion for votes**: every vote $`\mathbf{w}` equals the
structure reconstructed from its five projections:

$$`\begin{gathered} \mathbf{w} \;=\; \bigl\langle\, \operatorname{vote\_val}(\mathbf{w}),\;\; \operatorname{vote\_source}(\mathbf{w}),\;\; \operatorname{vote\_target}(\mathbf{w}), \\ \qquad\qquad \operatorname{vote\_source\_height}(\mathbf{w}),\;\; \operatorname{vote\_target\_height}(\mathbf{w}) \,\bigr\rangle \end{gathered}`

The five projections are {name}`vote_val`, {name}`vote_source`,
{name}`vote_target`, {name}`vote_source_height`,
{name}`vote_target_height`. The equality is definitional: by
$`\eta`-expansion for structures, with the projections unfolded,
the two sides are the same term.

Coq: {lit}`vote_unfold`.
-/
theorem vote_unfold
    {Validator : Type u}
    {Hash : Type v}
    (vote : Vote Validator Hash) :
    vote =
      { validator := vote_val vote
        source := vote_source vote
        target := vote_target vote
        sourceHeight := vote_source_height vote
        targetHeight := vote_target_height vote } :=
  match vote with | ⟨_, _, _, _, _⟩ => rfl

/--
Forward direction of the {name}`vote_msg` unfolding: given
$`\mathbf{w} \in \sigma` with
$`\mathbf{w} = \langle v, s, t, h_s, h_t \rangle`,

$$`\operatorname{vote\_msg}(\sigma,\; v,\; s,\; t,\; h_s,\; h_t)`

holds. That is, membership of a {name}`Vote` structure in a state
implies the membership predicate with the vote's field values as
arguments.
-/
theorem vote_msg_of_mem
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    {st : State Validator Hash}
    {vote : Vote Validator Hash}
    (h : vote ∈ st) :
    vote_msg st
      vote.validator
      vote.source
      vote.target
      vote.sourceHeight
      vote.targetHeight :=
  match vote, h with | ⟨_, _, _, _, _⟩, h => h

/--
Reverse direction of the {name}`vote_msg` unfolding:

$$`\operatorname{vote\_msg}(\sigma, v, s, t, h_s, h_t) \;\;\implies\;\; \langle v, s, t, h_s, h_t \rangle \in \sigma`

Together with {name}`vote_msg_of_mem`, this makes explicit that
{name}`vote_msg` is definitionally equal to set membership
$`\langle v, s, t, h_s, h_t \rangle \in \sigma`.
-/
theorem mem_of_vote_msg
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    {st : State Validator Hash}
    {v : Validator}
    {s t : Hash}
    {s_h t_h : Nat}
    (h : vote_msg st v s t s_h t_h) :
    ({ validator := v
       source := s
       target := t
       sourceHeight := s_h
       targetHeight := t_h } : Vote Validator Hash) ∈ st :=
  h

/--
Transfers a uniform upper bound on target heights to a specific vote:

$$`\bigl(\forall\, \mathbf{w} \in \sigma,\; \mathbf{w}.\mathit{targetHeight} \le H\bigr) \;\wedge\; \sigma \ni (v, s, t, h_s, h_t) \;\;\implies\;\; h_t \le H`

The proof constructs the {name}`Vote` structure from the
{name}`vote_msg` arguments and applies the bound hypothesis.
-/
theorem target_height_le_of_vote_msg
    {Validator : Type u}
    {Hash : Type v}
    [DecidableEq Validator]
    [DecidableEq Hash]
    {st : State Validator Hash}
    {v : Validator} {s t : Hash} {s_h t_h : Nat}
    {H : Nat}
    (hbound : ∀ vote : Vote Validator Hash, vote ∈ st → vote.targetHeight ≤ H)
    (hvm : vote_msg st v s t s_h t_h) :
    t_h ≤ H :=
  hbound ⟨v, s, t, s_h, t_h⟩ hvm

end GasperBeaconChain.Core
