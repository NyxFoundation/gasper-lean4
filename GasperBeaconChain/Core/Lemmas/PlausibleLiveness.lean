import GasperBeaconChain.Core.AtomicDef.PlausibleLiveness
import GasperBeaconChain.Core.Lemmas.Quorums
import GasperBeaconChain.Core.AtomicDef.NatExt
import GasperBeaconChain.Core.Lemmas.AccountableSafety
import GasperBeaconChain.Core.Lemmas.HashTree
import GasperBeaconChain.Core.Lemmas.SetTheoryProps

universe u v

namespace GasperBeaconChain.Core

/-!
# Plausible liveness: lemmas

Infrastructure for constructing the state extension that witnesses
plausible liveness. The file is organized in five groups:

## Block existence (§ 1)

{lit}`blocks_exist_high_over_of_coq` and
{lit}`not_blocks_exist_high_over_coq` show that the Coq-faithful
block-existence predicate is unsatisfiable, justifying the corrected
version. {lit}`blocks_exist_extract_new_final_pair_from_bound`
extracts a parent-child pair at a controlled height from the
block-existence hypothesis — the pair that will become the new
finalized block and its child.

## Vote-set construction (§ 2)

{lit}`votes_for_link` maps a quorum $`q` to a {name}`Finset` of
votes, one per validator, all targeting the same link. Its
membership characterization ({lit}`mem_votes_for_link`) is used in
{lit}`vote_msg_extend_classify` and the supermajority-link
construction.

## Highest target and state bounds (§ 3)

{lit}`highest_target` computes the greatest target height occurring
in a state (via {name}`foldMaxNat`). The predicates
{lit}`target_height_bound` and {lit}`target_height_present`,
together with their lemmas, connect the height of justified blocks
to the highest target in the state.

## State extension and vote classification (§ 4)

{lit}`extend_state_with_two_vote_sets` builds
$`\sigma' = \sigma \uplus V_1 \uplus V_2` via nested {name}`fUnion`.
{lit}`vote_msg_extend_classify` performs the three-way case split on
a vote in $`\sigma'`: old / first new set / second new set.
{lit}`unslashed_can_extend_two_vote_sets` verifies the
{lit}`unslashed_can_extend` property.

## Maximal-link and highest-block existence (§ 5)

{lit}`good_votes_mean_source_justified`,
{lit}`maximal_link_exists`, {lit}`maximal_link_highest_block`,
{lit}`highest_exists` — the chain of lemmas establishing that, under
the standing hypotheses (good votes, no slashing, quorum
nonemptiness), a unique highest justified block exists and any
justified block at or above its height must equal it.
-/

variable {Hash : Type v}

/--
# The Coq block-existence predicate implies the corrected one

The Coq-faithful predicate implies the corrected one:

$$`\operatorname{blocks\_exist\_high\_over\_coq}(\to, b) \;\implies\; \operatorname{blocks\_exist\_high\_over}(\to, b)`

The $`1 < n` guard, though trapped inside the existential in the
Coq version, can still be projected out since $`n` is universally
quantified: match on the Coq witness at a given $`n` to extract
the path, discarding the unused $`1 < n` component.
-/
theorem blocks_exist_high_over_of_coq
    {parent : HashParent Hash}
    {base : Hash}
    (h : blocks_exist_high_over_coq parent base) :
    blocks_exist_high_over parent base :=
  fun n _ => match h n with
  | ⟨block, hpath, _⟩ => ⟨block, hpath⟩

/--
# The Coq block-existence predicate is unsatisfiable

The Coq-faithful block-existence predicate is **unsatisfiable**:

$$`\neg\;\operatorname{blocks\_exist\_high\_over\_coq}(\to, b)`

Instantiating the universal quantifier at $`n = 0` forces the
existential to produce a witness of $`1 < 0`, which is absurd
({lit}`Nat.not_lt_zero`). This theorem justifies replacing the
Coq formulation with the corrected
{lit}`blocks_exist_high_over`, where the guard $`1 < n` is
moved outside the existential.
-/
theorem not_blocks_exist_high_over_coq
    {parent : HashParent Hash}
    {base : Hash} :
    ¬ blocks_exist_high_over_coq parent base :=
  fun h => match h 0 with
  | ⟨_, _, hlt⟩ => False.elim ((Nat.not_lt_zero _) hlt)

/--
# Extracting a parent-child pair at a controlled tree height

**Extract a parent-child pair**: given
blocks at arbitrarily large heights above a base block and the
bound $`\mathit{base\_h} \le H`, produces a parent-child pair:

$$`\exists\, \mathit{nf}\, \mathit{nc},\;\; \mathit{base} \xrightarrow{H + 1 - \mathit{base\_h}} \mathit{nf} \;\wedge\; \mathit{nf} \to \mathit{nc}`

# Proof idea

The distance $`d = H + 1 - \mathit{base\_h}` satisfies
$`d \ge 1` (from $`\mathit{base\_h} \le H`), so
$`\mathrm{succ}(d) > 1` and the block-existence hypothesis
{lit}`blocks_exist_high_over` provides a block at distance
$`\mathrm{succ}(d)` from $`\mathit{base}`.
{lit}`nth_ancestor_succ_inv` then decomposes this
$`(\mathrm{succ}(d))$-step chain into a $`d$-step chain to
$`\mathit{nf}` followed by a single parent edge
$`\mathit{nf} \to \mathit{nc}`.

# Role in the development

This is the block-tree witness factory for the plausible-liveness
construction: given the highest justified block at height
$`\mathit{base\_h}` and the state's highest target height $`H`,
it produces the new finalized block $`\mathit{nf}` and its child
$`\mathit{nc}` at the right tree distance. Consumed by
{lit}`blocks_exist_extract_new_final_pair` (which specializes
$`H = \operatorname{highest\_target}(\sigma)`) and ultimately by
{lit}`plausible_liveness_construct_extension`.
-/
theorem blocks_exist_extract_new_final_pair_from_bound
    (parent : HashParent Hash)
    {base : Hash}
    {base_h H : Nat}
    (hblocks : blocks_exist_high_over parent base)
    (hbase_le : base_h ≤ H) :
    ∃ new_finalized new_final_child : Hash,
      nth_ancestor parent (H + 1 - base_h) base new_finalized
      ∧ parent new_finalized new_final_child :=
  have hd_gt : 1 < Nat.succ (H + 1 - base_h) :=
    Nat.succ_lt_succ (Nat.sub_pos_of_lt (Nat.lt_succ_of_le hbase_le))
  match hblocks (Nat.succ (H + 1 - base_h)) hd_gt with
  | ⟨child, hpath⟩ =>
    match nth_ancestor_succ_inv hpath with
    | ⟨fin, hprev, hp⟩ => ⟨fin, child, hprev, hp⟩




/-!
## Vote-set construction

{lit}`votes_for_link` manufactures the batch of votes that a quorum
would cast for a given link. Its membership characterization
{lit}`mem_votes_for_link` is the interface through which
{lit}`vote_msg_extend_classify` identifies new votes in the extended
state.
-/

variable {Validator : Type u}

/--
# Constructing the vote set for a quorum and a link

Constructs the {name}`Finset` of votes that a quorum $`q` would
cast for a given link $`(s, t, h_s, h_t)`:

$$`\operatorname{votes\_for\_link}(q, s, t, h_s, h_t) \;\;\coloneqq\;\; \bigl\{\, \langle v, s, t, h_s, h_t \rangle \;\mid\; v \in q \,\bigr\}`

One vote per validator $`v \in q`, all sharing the same source,
target, and heights. The map $`v \mapsto \langle v, s, t, h_s, h_t \rangle`
is injective (by the {lit}`validator` field of {lit}`Vote.mk`),
so the resulting set has the same cardinality as $`q`.

# Role in the development

These vote sets are the two batches of new votes added to the
state in {lit}`extend_state_with_two_vote_sets`. Their membership
characterization {lit}`mem_votes_for_link` drives the three-way
case split in {lit}`vote_msg_extend_classify`, and their subset
relation to $`\sigma'` is what
{lit}`supermajority_link_of_quorum_votes` needs to construct
the new supermajority links.
-/
def votes_for_link
    (q : Finset Validator)
    (s t : Hash) (s_h t_h : Nat) :
    Finset (Vote Validator Hash) :=
  q.map ⟨fun v => { validator := v, source := s, target := t,
                     sourceHeight := s_h, targetHeight := t_h },
         fun _ _ h => congrArg Vote.validator h⟩

/--
# A vote is in the link set iff it matches a quorum member

Membership in {lit}`votes_for_link`:

$$`w \in \operatorname{votes\_for\_link}(q, s, t, h_s, h_t) \;\iff\; \exists\, v \in q,\; w = \langle v, s, t, h_s, h_t \rangle`

A vote belongs to the set iff it equals the canonical vote
$`\langle v, s, t, h_s, h_t \rangle` for some $`v \in q`.
Definitional, via {name}`Finset.mem_map`. The forward direction
decomposes the map membership; the backward direction reconstructs
it. This characterization is the interface through which
{lit}`vote_msg_extend_classify` identifies new votes.
-/
theorem mem_votes_for_link
    {q : Finset Validator} {s t : Hash} {s_h t_h : Nat}
    {vote : Vote Validator Hash} :
    vote ∈ votes_for_link q s t s_h t_h ↔
    ∃ v, v ∈ q ∧ vote = { validator := v, source := s, target := t,
                           sourceHeight := s_h, targetHeight := t_h } :=
  show vote ∈ q.map ⟨_, _⟩ ↔ _ from
    ⟨fun h => match Finset.mem_map.mp h with
       | ⟨v, hv, heq⟩ => ⟨v, hv, heq.symm⟩,
     fun ⟨v, hv, heq⟩ => Finset.mem_map.mpr ⟨v, hv, heq.symm⟩⟩



variable [DecidableEq Validator]
variable [DecidableEq Hash]

/--
# Greatest target height in a state

The **greatest target height** occurring in a state $`\sigma`:

$$`\operatorname{highest\_target}(\sigma) \;\;\coloneqq\;\; \operatorname{foldMaxNat}\bigl(\sigma,\; w \mapsto w.\mathit{targetHeight}\bigr)`

Returns $`0` for the empty state (the fold's seed). This value
bounds the height of every justified block
({lit}`justified_height_le_highest_target`) and determines the
target heights of the two new supermajority links in the
plausible-liveness construction ($`H + 1` and $`H + 2` where
$`H = \operatorname{highest\_target}(\sigma)`).

The characterizing lemmas are:
* {lit}`vote_target_height_le_highest_target` — upper bound
* {lit}`highest_target_is_bound` — it is a
  {lit}`target_height_bound`
* {lit}`highest_target_le_of_bound` — minimality among bounds
-/
def highest_target
    (st : State Validator Hash) : Nat :=
  foldMaxNat st (·.targetHeight)

/--
# Every vote's target height is at most the state's maximum

Every vote's target height is bounded by
{lit}`highest_target`:

$$`w \in \sigma \;\implies\; w.\mathit{targetHeight} \le \operatorname{highest\_target}(\sigma)`

This is the upper-bound property of the finite maximum
({name}`le_foldMaxNat_of_mem`) specialized to the target-height
function. It is the single bridge between individual vote data and
the global height bound, consumed by
{lit}`target_height_present_le_highest_target` and
{lit}`justified_height_le_highest_target`.
-/
theorem vote_target_height_le_highest_target
    {st : State Validator Hash}
    {vote : Vote Validator Hash}
    (hvote : vote ∈ st) :
    vote.targetHeight ≤ highest_target st :=
  le_foldMaxNat_of_mem hvote

/--
# All target heights bounded by $`H`

The property that every vote's target height is at most $`H`:

$$`\operatorname{target\_height\_bound}(\sigma, H) \;\;\coloneqq\;\; \forall\, w \in \sigma,\; w.\mathit{targetHeight} \le H`

Used as a hypothesis in the no-new-slashing arguments of
{lit}`Theories/PlausibleLiveness.lean` to bound the heights of old
votes before the state extension.
-/
def target_height_bound
    (st : State Validator Hash)
    (H : Nat) : Prop :=
  ∀ vote : Vote Validator Hash, vote ∈ st → vote.targetHeight ≤ H

/--
# A height is present if zero or witnessed by a vote

A height $`h` is **present** in the state if either $`h = 0` (the
genesis height, always considered present) or some vote in $`\sigma`
has target height $`h`:

$$`\operatorname{target\_height\_present}(\sigma, h) \;\;\coloneqq\;\; h = 0 \;\lor\; \exists\, w \in \sigma,\; w.\mathit{targetHeight} = h`

This predicate bridges justified-block heights (which start at $`0`
for genesis and are witnessed by votes for non-genesis blocks) to
the {lit}`highest_target` bound.
-/
def target_height_present
    (st : State Validator Hash)
    (h : Nat) : Prop :=
  h = 0 ∨ ∃ vote : Vote Validator Hash, vote ∈ st ∧ vote.targetHeight = h

/--
# Height zero is always present
The left disjunct $`0 = 0` holds by {lit}`rfl`. -/
theorem zero_target_height_present
    (st : State Validator Hash) :
    target_height_present st 0 :=
  Or.inl rfl

/--
# A vote's target height is present in the state
The right disjunct is witnessed by the vote itself. -/
theorem vote_target_height_present
    {st : State Validator Hash}
    {vote : Vote Validator Hash}
    (hvote : vote ∈ st) :
    target_height_present st vote.targetHeight :=
  Or.inr ⟨vote, hvote, rfl⟩

/--
# Present heights are bounded by the highest target

A present height is bounded by {lit}`highest_target`:

$$`\operatorname{target\_height\_present}(\sigma, h) \;\implies\; h \le \operatorname{highest\_target}(\sigma)`

The $`h = 0` case is immediate ($`0 \le` anything); the witnessed
case applies {lit}`vote_target_height_le_highest_target` to the
witnessing vote and transports via the height equality.
-/
theorem target_height_present_le_highest_target
    {st : State Validator Hash}
    {h : Nat}
    (hh : target_height_present st h) :
    h ≤ highest_target st :=
  hh.elim
    (fun h0 => Eq.subst (motive := fun x => x ≤ highest_target st) h0.symm (Nat.zero_le _))
    (fun ⟨_, hvote, heq⟩ =>
      Eq.subst (motive := fun x => x ≤ highest_target st) heq
        (vote_target_height_le_highest_target hvote))

/--
# The highest target is an upper bound for all target heights

{lit}`highest_target` is itself a {lit}`target_height_bound`:
every vote's target height is at most
$`\operatorname{highest\_target}(\sigma)`.
-/
theorem highest_target_is_bound
    (st : State Validator Hash) :
    target_height_bound st (highest_target st) :=
  fun _vote hvote => vote_target_height_le_highest_target hvote

/--
# Any bound on all target heights dominates the highest target

Any {lit}`target_height_bound` dominates {lit}`highest_target`:
the least-upper-bound property of {name}`foldMaxNat` via
{name}`foldMaxNat_le_of_forall_le`.
-/
theorem highest_target_le_of_bound
    {st : State Validator Hash}
    {H : Nat}
    (hH : target_height_bound st H) :
    highest_target st ≤ H :=
  foldMaxNat_le_of_forall_le hH

/--
# Heights below the highest target are strictly below its successor

Any height at most $`\operatorname{highest\_target}(\sigma)` is
strictly less than $`\operatorname{highest\_target}(\sigma) + 1`:
wrapper for {lit}`Nat.lt_succ_of_le`. This bridges the justified-
block height bound to the strict inequality needed when
constructing the forward link at height
$`\operatorname{highest\_target}(\sigma) + 1`.
-/
theorem height_lt_highest_target_succ
    (st : State Validator Hash)
    {h : Nat}
    (hle : h ≤ highest_target st) :
    h < highest_target st + 1 :=
  Nat.lt_succ_of_le hle

/--
# Extracting a finalization pair at the state's highest target

Specialization of {lit}`blocks_exist_extract_new_final_pair_from_bound`
to the bound $`H = \operatorname{highest\_target}(\sigma)`: extracts
a parent-child pair at height
$`\operatorname{highest\_target}(\sigma) + 1` above the base.
-/
theorem blocks_exist_extract_new_final_pair
    (parent : HashParent Hash)
    (st : State Validator Hash)
    {base : Hash}
    {base_h : Nat}
    (hblocks : blocks_exist_high_over parent base)
    (hbase_le : base_h ≤ highest_target st) :
    ∃ new_finalized new_final_child : Hash,
      nth_ancestor parent
        (highest_target st + 1 - base_h)
        base new_finalized
      ∧ parent new_finalized new_final_child :=
  blocks_exist_extract_new_final_pair_from_bound parent hblocks hbase_le

/-!
## State extension and vote classification

The next group builds the extended state
$`\sigma' = (\sigma \uplus V_1) \uplus V_2` and provides the
three-way classification of its votes
({lit}`vote_msg_extend_classify`), plus the derived properties
{lit}`unslashed_can_extend_two_vote_sets` and the well-formedness
preservation
{lit}`votes_from_target_vset_extend_two_vote_sets`.
-/


/--
# Building the extended state from two new vote batches

**State extension by two vote sets**: builds
$`\sigma' = (\sigma \uplus V_1) \uplus V_2` via nested
{name}`fUnion`. The two vote sets $`V_1, V_2` are the ballots cast
by the two quorums for the new finalization pair in the liveness
construction.
-/
def extend_state_with_two_vote_sets
    (st : State Validator Hash)
    (votes1 votes2 : Finset (Vote Validator Hash)) :
    State Validator Hash :=
  fUnion (fUnion st votes1) votes2

/--
# Old votes persist in the extended state
Every vote in the original state $`\sigma` belongs to the extended state $`\sigma'` (left-left inclusion through the nested {name}`fUnion`). -/
theorem old_votes_subset_extended
    {st : State Validator Hash}
    {votes1 votes2 : Finset (Vote Validator Hash)}
    {vote : Vote Validator Hash}
    (h : vote ∈ st) :
    vote ∈ extend_state_with_two_vote_sets st votes1 votes2 :=
  mem_fUnion_left (mem_fUnion_left h)

/--
# First batch of new votes belongs to the extended state
Every vote in $`V_1` belongs to the extended state (left-right through {name}`fUnion`). -/
theorem first_new_votes_subset_extended
    {st : State Validator Hash}
    {votes1 votes2 : Finset (Vote Validator Hash)}
    {vote : Vote Validator Hash}
    (h : vote ∈ votes1) :
    vote ∈ extend_state_with_two_vote_sets st votes1 votes2 :=
  mem_fUnion_left (mem_fUnion_right h)

/--
# Second batch of new votes belongs to the extended state
Every vote in $`V_2` belongs to the extended state (right through the outer {name}`fUnion`). -/
theorem second_new_votes_subset_extended
    {st : State Validator Hash}
    {votes1 votes2 : Finset (Vote Validator Hash)}
    {vote : Vote Validator Hash}
    (h : vote ∈ votes2) :
    vote ∈ extend_state_with_two_vote_sets st votes1 votes2 :=
  mem_fUnion_right h

/--
# Every vote in the extended state is old, from $`q_1`, or from $`q_2`

**Three-way vote classification**: every vote
in $`\sigma' = (\sigma \uplus V_1) \uplus V_2` either belongs to
the original state $`\sigma`, or matches the link of the first
quorum $`q_1` (with $`v \in q_1`), or matches the link of the
second quorum $`q_2` (with $`v \in q_2`).

The proof unfolds the nested {name}`fUnion` via
{lit}`mem_fUnion` and decomposes each new vote via
{lit}`mem_votes_for_link`, extracting the validator membership
and the field equalities by {lit}`Vote.mk.injEq`.

This is the central case-splitting lemma consumed in
{lit}`Theories/PlausibleLiveness.lean` by
{lit}`no_new_double_vote_two_link_extension` and
{lit}`no_new_surround_vote_two_link_extension` to classify each
vote in the extended state and rule out new slashing.
-/
theorem vote_msg_extend_classify
    {st : State Validator Hash}
    {q1 q2 : Finset Validator}
    {s1 t1 s2 t2 : Hash} {s1_h t1_h s2_h t2_h : Nat}
    {v : Validator} {s t : Hash} {s_h t_h : Nat}
    (hvote : vote_msg
      (extend_state_with_two_vote_sets st
        (votes_for_link q1 s1 t1 s1_h t1_h)
        (votes_for_link q2 s2 t2 s2_h t2_h))
      v s t s_h t_h) :
    vote_msg st v s t s_h t_h
    ∨ (v ∈ q1 ∧ s = s1 ∧ t = t1 ∧ s_h = s1_h ∧ t_h = t1_h)
    ∨ (v ∈ q2 ∧ s = s2 ∧ t = t2 ∧ s_h = s2_h ∧ t_h = t2_h) :=
  have hvote' : (⟨v, s, t, s_h, t_h⟩ : Vote Validator Hash) ∈
      fUnion (fUnion st (votes_for_link q1 s1 t1 s1_h t1_h))
        (votes_for_link q2 s2 t2 s2_h t2_h) := hvote
  (mem_fUnion.mp hvote').elim
    (fun hOldOrFirst => (mem_fUnion.mp hOldOrFirst).elim
      Or.inl
      (fun hFirst =>
        match mem_votes_for_link.mp hFirst with
        | ⟨_, hw, heq⟩ =>
          match (Vote.mk.injEq ..).mp heq with
          | ⟨rfl, rfl, rfl, rfl, rfl⟩ => Or.inr (Or.inl ⟨hw, rfl, rfl, rfl, rfl⟩)))
    (fun hSecond =>
      match mem_votes_for_link.mp hSecond with
      | ⟨_, hw, heq⟩ =>
        match (Vote.mk.injEq ..).mp heq with
        | ⟨rfl, rfl, rfl, rfl, rfl⟩ => Or.inr (Or.inr ⟨hw, rfl, rfl, rfl, rfl⟩))

/--
# New votes come only from unslashed validators

The two-vote-set extension satisfies {lit}`unslashed_can_extend`:

$$`\operatorname{unslashed\_can\_extend}\bigl(\sigma,\; (\sigma \uplus V_1) \uplus V_2\bigr)`

provided every validator in $`q_1` is unslashed in $`\sigma` and
every validator in $`q_2` is unslashed in $`\sigma`.

# Proof idea

For each vote in $`\sigma'`,
{lit}`vote_msg_extend_classify` classifies it into one of three
origins. If it belonged to $`\sigma`, the left disjunct holds
directly. If it came from $`q_1` (resp. $`q_2`), then the
voter is in $`q_1` (resp. $`q_2`) and the corresponding
quorum-unslashed hypothesis gives the right disjunct.

# Role in the development

One of the two properties (together with
{lit}`no_new_slashed_two_link_extension`) that the
plausible-liveness construction must verify for the extended state.
-/
theorem unslashed_can_extend_two_vote_sets
    {st : State Validator Hash}
    {q1 q2 : Finset Validator}
    {s1 t1 s2 t2 : Hash} {s1_h t1_h s2_h t2_h : Nat}
    (huns1 : ∀ v, v ∈ q1 → ¬ slashed st v)
    (huns2 : ∀ v, v ∈ q2 → ¬ slashed st v) :
    unslashed_can_extend st
      (extend_state_with_two_vote_sets st
        (votes_for_link q1 s1 t1 s1_h t1_h)
        (votes_for_link q2 s2 t2 s2_h t2_h)) :=
  fun _ _ _ _ _ hvote =>
    (vote_msg_extend_classify hvote).elim
      Or.inl
      (fun h => h.elim
        (fun ⟨hvq, rfl, rfl, rfl, rfl⟩ => Or.inr (huns1 _ hvq))
        (fun ⟨hvq, rfl, rfl, rfl, rfl⟩ => Or.inr (huns2 _ hvq)))




/-!
## Maximal-link and highest-block existence

The following chain of lemmas establishes, under the standing
hypotheses ({lit}`good_votes`, no slashing, quorum nonemptiness),
the existence of a unique highest justified block:

1. {lit}`supermajority_votes` — the domain of maximization
2. {lit}`good_votes_mean_source_justified` — a link's source is
   justified
3. {lit}`maximal_link_exists` — a link with maximal target height
   exists
4. {lit}`maximal_link_highest_block` — the maximal-link target is
   the unique highest justified block
5. {lit}`highest_exists` — the existence theorem
6. {lit}`justified_height_le_highest_target` — justified heights
   are bounded by the state's highest target
-/

variable [Fintype Validator]

/--
# Votes whose own link is already a supermajority link

The set of votes in $`\sigma` whose own source-target link already
forms a supermajority link:

$$`\operatorname{supermajority\_votes}(\sigma) \;\;\coloneqq\;\; \{\, w \in \sigma \;\mid\; \operatorname{supermajority\_link}(\sigma, w.s, w.t, w.h_s, w.h_t) \,\}`

A vote $`w` belongs to this set iff (1) $`w \in \sigma` and
(2) the supporters of $`w`'s own source-target link in $`\sigma`
form a $`\frac{2}{3}`-quorum. The set is a
{name}`Finset.filter` of $`\sigma`, hence finite.

# Interpretation

This is the *domain* on which the finite maximizer
{name}`exists_mem_maximal_by_nat` is applied to find the maximal
justification link. The key function is
$`w \mapsto w.\mathit{targetHeight}`: the vote with the largest
target height determines the highest justification link.

# Role in the development

Nonemptiness of {lit}`supermajority_votes` is the distinguishing
condition in {lit}`highest_exists`: when nonempty, a maximal link
exists and the highest justified block is its target; when empty,
genesis is the only justified block.
-/
def supermajority_votes
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (st : State Validator Hash) :
    Finset (Vote Validator Hash) :=
  st.filter (fun vote =>
    supermajority_link τ stake vset st
      vote.source vote.target vote.sourceHeight vote.targetHeight)

/--
# Membership in the supermajority-vote set

Membership in {lit}`supermajority_votes`: a vote belongs to the set
iff it is in $`\sigma` and its source-target link is a supermajority
link (definitional, via {name}`Finset.mem_filter`).
-/
theorem mem_supermajority_votes
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Hash → Finset Validator}
    {st : State Validator Hash}
    {vote : Vote Validator Hash} :
    vote ∈ supermajority_votes τ stake vset st
      ↔
    vote ∈ st ∧
    supermajority_link τ stake vset st
      vote.source vote.target vote.sourceHeight vote.targetHeight :=
  show vote ∈ st.filter _ ↔ _ from Finset.mem_filter

/--
# A justification link's source is justified (from good votes)

Under the {lit}`good_votes` hypothesis, a justification link's
**source is already justified**:

$$`\operatorname{good\_votes}(\sigma) \;\wedge\; \operatorname{justification\_link}(\sigma, s, t, h_s, h_t) \;\implies\; \operatorname{justified}(\sigma, s, h_s)`

# Proof idea

The justification link contains a supermajority link, hence a
$`\frac{2}{3}`-quorum $`q` at the target $`t`. By the
{name}`QuorumContext` nonemptiness property, $`q` contains at
least one validator $`v`. The {lit}`good_votes` hypothesis then
gives $`\operatorname{justified\_source\_votes}(\sigma, v)`, which —
applied to $`v`'s vote for the link $`(s, t, h_s, h_t)` (extracted
via {name}`mem_link_supporters`) — yields
$`\operatorname{justified}(\sigma, s, h_s)`.

# Role in the development

This lemma closes the gap between the {lit}`justification_link`
definition (which does *not* require justification of the source)
and the inductive {lit}`justified` closure (which does). It is the
mechanism by which the plausible-liveness argument can deduce
justification of the maximal link's source from {lit}`good_votes`,
without needing the source to be previously known as justified.
Consumed by {lit}`maximal_link_exists`,
{lit}`maximal_link_highest_block`, and {lit}`highest_exists`.
-/
theorem good_votes_mean_source_justified
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    {s t : Hash}
    {s_h t_h : Nat}
    (hgood : good_votes τ stake vset parent genesis st)
    (hlink : justification_link τ stake vset parent st s t s_h t_h) :
    justified τ stake vset parent genesis st s s_h :=
  match hlink with
  | ⟨_, _, hsm⟩ =>
    match qctx.quorum_2_nonempty t _ hsm with
    | ⟨v, hv⟩ =>
      match hgood t _ hsm v hv with
      | ⟨hjs_src, _⟩ => hjs_src s t s_h t_h (mem_link_supporters.mp hv)

/--
# There exists a justification link with maximal target height

**Existence of a maximal justification link**: given that at least
one justification link exists ({lit}`has_justification_link`),
there is one whose target height dominates every other:

$$`\exists\, s\, t\, h_s\, h_t,\; \operatorname{maximal\_justification\_link}(\sigma, s, t, h_s, h_t)`

# Proof idea

First, the existence of a justification link implies that
{lit}`supermajority_votes` is nonempty (witness: any validator in
the link's quorum gives a vote in the set). Then the finite
maximizer theorem ({name}`exists_mem_maximal_by_nat`) applied to
{lit}`supermajority_votes` with the key function
$`w \mapsto w.\mathit{targetHeight}` produces a vote $`\mathit{mv}`
whose target height is maximal. The {lit}`good_votes` hypothesis
extracts from $`\mathit{mv}`'s validator the forward-link property
($`h_s < h_t` and $`s \xrightarrow{h_t - h_s} t`), turning the
supermajority link into a full justification link.

For the maximality clause: given any other justification link
$`(s', t', h_s', h_t')`, its quorum witnesses a vote in
{lit}`supermajority_votes`, and the finite-maximum property gives
$`h_t' \le h_t`.

# Role in the development

The intermediate step between {lit}`has_justification_link` and
{lit}`maximal_link_highest_block`: it provides the maximal link
from which the unique highest justified block is derived.
-/
theorem maximal_link_exists
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    (hgood : good_votes τ stake vset parent genesis st)
    (hjust : has_justification_link τ stake vset parent genesis st) :
    ∃ s t : Hash, ∃ s_h t_h : Nat,
      maximal_justification_link τ stake vset parent st s t s_h t_h :=
  have hne : (supermajority_votes τ stake vset st).Nonempty :=
    match hjust with
    | ⟨s, t, s_h, t_h, _, _, _, hsm⟩ =>
      match qctx.quorum_2_nonempty t _ hsm with
      | ⟨v, hv⟩ => ⟨⟨v, s, t, s_h, t_h⟩,
          mem_supermajority_votes.mpr ⟨mem_link_supporters.mp hv, hsm⟩⟩
  match exists_mem_maximal_by_nat (supermajority_votes τ stake vset st)
    (fun v => v.targetHeight) hne with
  | ⟨mv, hmv_sm, hmv_max⟩ =>
    match mem_supermajority_votes.mp hmv_sm with
    | ⟨hmv_st, hmv_sup⟩ =>
    have hmv_supp : mv.validator ∈
        link_supporters st mv.source mv.target mv.sourceHeight mv.targetHeight :=
      mem_link_supporters.mpr (vote_msg_of_mem hmv_st)
    match hgood mv.target _ hmv_sup mv.validator hmv_supp with
    | ⟨_, hfwd_link⟩ =>
    match hfwd_link mv.source mv.target mv.sourceHeight mv.targetHeight
        (vote_msg_of_mem hmv_st) with
    | ⟨hlt, hnth⟩ =>
    ⟨mv.source, mv.target, mv.sourceHeight, mv.targetHeight,
      ⟨hlt, hnth, hmv_sup⟩,
      fun s' t' s_h' t_h' hlink' =>
        match hlink' with
        | ⟨_, _, hsm'⟩ =>
          match qctx.quorum_2_nonempty t' _ hsm' with
          | ⟨v', hv'⟩ =>
            hmv_max ⟨v', s', t', s_h', t_h'⟩
              (mem_supermajority_votes.mpr ⟨mem_link_supporters.mp hv', hsm'⟩)⟩

/--
# The maximal-link target is the unique highest justified block

**The maximal-link target is the unique highest justified block**:
under the standing hypotheses (no slashing, good votes), if
$`(s, t, h_s, h_t)` is a maximal justification link and $`b` is
justified at height $`b_h \ge h_t`, then $`b = t` and
$`b_h = h_t`.

# Proof idea

If $`b_h = h_t` and $`b \ne t`, apply
{lit}`no_two_justified_same_height` for a contradiction. If
$`b_h > h_t`, case-split $`b`'s justification via
{lit}`justified_cases`: genesis is impossible (height $`0 < h_t`);
a link case gives a justification link with target height
$`b_h > h_t`, contradicting the maximality of $`h_t`.

# Assumptions

* $`\operatorname{QuorumContext}` {lit}`qctx` — to extract a voter
  from $`b`'s justification link in the $`b_h > h_t` branch;
* $`\neg\,\operatorname{q\_intersection\_slashed}(\sigma)`
  {lit}`hno` — fuels {lit}`no_two_justified_same_height` in the
  equal-height branch;
* $`\operatorname{good\_votes}(\sigma)` {lit}`hgood` — to justify
  the maximal link's source and so its target $`t`;
* the maximality hypothesis
  $`\operatorname{maximal\_justification\_link}(\sigma, s, t, h_s, h_t)`
  {lit}`hmax` — that *no* justification link has a strictly greater
  target height;
* a justified block $`b` at height $`b_h \ge h_t`
  {lit}`hbj`, {lit}`hbh`.

# Non-assumptions

* $`b` is *not* assumed to be the target of any link, nor related to
  $`t` in the block tree — the conclusion $`b = t` is *derived*, not
  hypothesized;
* no upper bound on $`b_h` beyond $`\ge h_t` is needed; the proof
  rules out $`b_h > h_t` directly from maximality.

# Role in the development

The uniqueness engine behind {lit}`highest_exists`: it converts the
purely *quantitative* maximality of $`h_t` (greatest target height)
into the *qualitative* statement that the maximal-link target is the
one and only highest justified block. Without the no-slashing
hypothesis only "a highest" could be claimed; with it, "the
highest" follows.
-/
theorem maximal_link_highest_block
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    {s t : Hash} {s_h t_h : Nat}
    {b : Hash} {b_h : Nat}
    (hno : ¬ q_intersection_slashed τ stake vset st)
    (hgood : good_votes τ stake vset parent genesis st)
    (hmax : maximal_justification_link τ stake vset parent st s t s_h t_h)
    (hbj : justified τ stake vset parent genesis st b b_h)
    (hbh : t_h ≤ b_h) :
    b = t ∧ b_h = t_h :=
  match hmax with
  | ⟨hlink, hmaximal⟩ =>
    have hsj : justified τ stake vset parent genesis st s s_h :=
      good_votes_mean_source_justified τ stake vset parent genesis st qctx hgood hlink
    have htj : justified τ stake vset parent genesis st t t_h :=
      justified.justified_link hsj hlink
    if heq_h : b_h = t_h then
      if heq_b : b = t then ⟨heq_b, heq_h⟩
      else False.elim ((no_two_justified_same_height τ stake vset parent genesis st
        hbj (Eq.subst (motive := fun h => justified τ stake vset parent genesis st t h)
          heq_h.symm htj) hno heq_b) rfl)
    else
      have hlt_h : t_h < b_h :=
        Nat.lt_of_le_of_ne hbh (fun h => heq_h h.symm)
      (justified_cases τ stake vset parent genesis st hbj).elim
        (fun ⟨_, hb_zero⟩ =>
          False.elim ((Nat.not_lt_zero _) (match hb_zero with | rfl => hlt_h)))
        (fun ⟨_, _, _, hlink_b⟩ =>
          False.elim (heq_h (Nat.le_antisymm (hmaximal _ _ _ _ hlink_b) hbh)))

/--
# There exists a unique highest justified block

**Existence of a unique highest justified block**: under the
standing hypotheses (no quorum-intersection slashing, good votes,
quorum nonemptiness), there exists a block $`b` at height $`b_h`
that is both justified and {lit}`highest_justified` — i.e., any
justified block at height $`\ge b_h` must equal $`b` at the same
height.

# Proof idea

If the set of {lit}`supermajority_votes` is nonempty, a
justification link exists, so {lit}`maximal_link_exists` produces a
maximal link whose target $`t` is justified (by
{lit}`good_votes_mean_source_justified` plus the link rule). Any
justified block at height $`\ge h_t` equals $`t` by
{lit}`maximal_link_highest_block`. If no supermajority votes exist,
genesis is the only justified block (any non-genesis justification
would require a supermajority vote, contradicting the empty set),
and genesis at height $`0` is trivially highest.

# Assumptions

* $`\operatorname{QuorumContext}(\tau, \mathsf{stake}, \mathsf{vset})`
  — quorum nonemptiness {lit}`qctx`, needed to extract a witnessing
  validator from each supermajority link;
* $`\neg\,\operatorname{q\_intersection\_slashed}(\sigma)` — no
  slashing {lit}`hno`, which (via {lit}`maximal_link_highest_block`)
  upgrades "$`t` is *a* highest target" to "$`t` is *the unique*
  highest justified block";
* $`\operatorname{good\_votes}(\sigma)` — every supermajority link's
  validators have justified sources and forward links {lit}`hgood`.

The ambient $`[\mathsf{Fintype}\ \mathsf{Validator}]` is a section
variable, required for the finite maximization
{name}`exists_mem_maximal_by_nat`.

# Non-assumptions

* $`\sigma` need *not* contain any justification link at all — the
  empty branch returns genesis, so existence is unconditional;
* no lower bound on stake, no positivity of the threshold beyond
  what {lit}`qctx` provides;
* no assumption that a *finalized* (as opposed to merely justified)
  block exists — finalization is constructed later, on top of this
  highest justified block.

# Role in the development

This is the starting point of the plausible-liveness construction
({lit}`Theories/PlausibleLiveness.lean`): the highest justified
block becomes the common source of the two new supermajority links
whose targets form the freshly finalized pair. Its uniqueness (the
{lit}`highest_justified` conjunct) is what guarantees the two new
links extend a *single* well-defined frontier rather than branching.
-/
theorem highest_exists
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    (hno : ¬ q_intersection_slashed τ stake vset st)
    (hgood : good_votes τ stake vset parent genesis st) :
    ∃ b : Hash, ∃ b_h : Nat,
      justified τ stake vset parent genesis st b b_h ∧
      highest_justified τ stake vset parent genesis st b b_h :=
  if hne : (supermajority_votes τ stake vset st).Nonempty then
    have hhas : has_justification_link τ stake vset parent genesis st :=
      match hne with
      | ⟨vote, hvote⟩ =>
        match mem_supermajority_votes.mp hvote with
        | ⟨_, hvote_sm⟩ =>
        match qctx.quorum_2_nonempty _ _ hvote_sm with
        | ⟨v, hv⟩ =>
          match hgood _ _ hvote_sm v hv with
          | ⟨hjs_src, hfwd_link⟩ =>
            match hfwd_link _ _ _ _ (mem_link_supporters.mp hv) with
            | ⟨hlt, hnth⟩ =>
              ⟨vote.source, vote.target, vote.sourceHeight, vote.targetHeight,
                hjs_src _ _ _ _ (mem_link_supporters.mp hv), hlt, hnth, hvote_sm⟩
    match maximal_link_exists τ stake vset parent genesis st qctx hgood hhas with
    | ⟨_, t, _, t_h, hlink, hmaximal⟩ =>
      have htj : justified τ stake vset parent genesis st t t_h :=
        justified.justified_link
          (good_votes_mean_source_justified τ stake vset parent genesis st qctx hgood hlink) hlink
      ⟨t, t_h, htj, fun _ _ hle hbj =>
        maximal_link_highest_block τ stake vset parent genesis st qctx hno hgood
          ⟨hlink, hmaximal⟩ hbj hle⟩
  else
    ⟨genesis, 0, justified.justified_genesis, fun b' b_h' _ hbj =>
      (justified_cases τ stake vset parent genesis st hbj).elim
        (fun ⟨hb_gen, hb_h⟩ => ⟨hb_gen, hb_h⟩)
        (fun ⟨s, s_h, _, _, _, hsm⟩ =>
          match qctx.quorum_2_nonempty _ _ hsm with
          | ⟨v, hv⟩ => False.elim (hne
              ⟨⟨v, s, b', s_h, b_h'⟩,
                mem_supermajority_votes.mpr ⟨mem_link_supporters.mp hv, hsm⟩⟩))⟩

/--
# Justified blocks have height at most the state's highest target

**Justified height is bounded by the highest target**: a justified
block's height never exceeds the greatest target height in the
state. Proved by induction on the {lit}`justified` derivation:
genesis has height $`0 \le \operatorname{highest\_target}`; for
the link case, the link's quorum is nonempty (by
{name}`QuorumContext`), so some vote in $`\sigma` has target height
$`h_t`, and {lit}`vote_target_height_le_highest_target` gives
$`h_t \le \operatorname{highest\_target}(\sigma)`.
-/
theorem justified_height_le_highest_target
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    {b : Hash} {b_h : Nat}
    (hj : justified τ stake vset parent genesis st b b_h) :
    b_h ≤ highest_target st :=
  hj.rec
    (Nat.zero_le _)
    (fun _ hlink _ =>
      match hlink with
      | ⟨_, _, hsm⟩ =>
        match qctx.quorum_2_nonempty _ _ hsm with
        | ⟨_, hv⟩ => vote_target_height_le_highest_target
            (mem_of_vote_msg (mem_link_supporters.mp hv)))

/-!
## Supermajority-link construction

The final group provides the tools for constructing supermajority
links in the extended state $`\sigma'` from known quorums:

: {lit}`quorum_subset_link_supporters_of_votes_subset`

  Converts a vote-set subset condition into a quorum-subset-of-
  supporters condition.

: {lit}`supermajority_link_of_quorum_votes`

  Assembles a supermajority link in $`\sigma'` from a quorum, a
  vote-set subset, and the well-formedness of $`\sigma'`.

: {lit}`votes_from_target_vset_extend_two_vote_sets`

  Preserves {lit}`votes_from_target_vset_property` across the
  two-vote-set extension.
-/

/--
# A quorum's vote set in the state makes the quorum a subset of supporters

If the vote set {lit}`votes_for_link` $`q\,s\,t\,h_s\,h_t` is a
subset of $`\sigma'`, then $`q` itself is a subset of
$`\operatorname{link\_supporters}(\sigma', s, t, h_s, h_t)`: each
validator's canonical vote in $`\sigma'` witnesses the supporter
membership. This converts a subset-of-state condition into a
subset-of-supporters condition, preparing for
{lit}`quorum_2_upclosed`.
-/
theorem quorum_subset_link_supporters_of_votes_subset
    {q : Finset Validator} {s t : Hash} {s_h t_h : Nat}
    {st' : State Validator Hash}
    (hsub : votes_for_link q s t s_h t_h ⊆ st') :
    q ⊆ link_supporters st' s t s_h t_h :=
  fun v hv => mem_link_supporters.mpr
    (vote_msg_of_mem (hsub (Finset.mem_map.mpr ⟨v, hv, rfl⟩)))

/--
# A quorum whose votes are in the state produces a supermajority link

**Constructing a supermajority link from a quorum's vote set**: if
$`q` is a $`\frac{2}{3}`-quorum at block $`t`, the vote set
{lit}`votes_for_link` $`q\,s\,t\,h_s\,h_t` is a subset of
$`\sigma'`, and $`\sigma'` is well-formed, then
$`\operatorname{supermajority\_link}(\sigma', s, t, h_s, h_t)` holds.

The proof promotes $`q` to the full supporter set in $`\sigma'` via
{lit}`quorum_subset_link_supporters_of_votes_subset` and applies
{lit}`quorum_2_upclosed`.
-/
theorem supermajority_link_of_quorum_votes
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    {q : Finset Validator} {s t : Hash} {s_h t_h : Nat}
    {st' : State Validator Hash}
    (hq : quorum_2 τ stake vset q t)
    (hsub : votes_for_link q s t s_h t_h ⊆ st')
    (hwf : votes_from_target_vset_property vset st') :
    supermajority_link τ stake vset st' s t s_h t_h :=
  show quorum_2 τ stake vset (link_supporters st' s t s_h t_h) t from
    @quorum_2_upclosed Validator Hash _ τ stake vset t q _
      (quorum_subset_link_supporters_of_votes_subset hsub)
      (fun _ hv => hwf hv)
      hq

/--
# Vote well-formedness is preserved by the two-vote-set extension

The two-vote-set extension preserves
{lit}`votes_from_target_vset_property`: if the original state
$`\sigma` is well-formed and both quorums $`q_1 \subseteq V(t_1)`,
$`q_2 \subseteq V(t_2)`, then the extended state is also
well-formed. The proof applies {lit}`vote_msg_extend_classify` to
each link-supporter membership, routing old votes through the
original well-formedness and new votes through the quorum-subset
hypotheses.
-/
theorem votes_from_target_vset_extend_two_vote_sets
    (vset : Hash → Finset Validator)
    {st : State Validator Hash}
    {q1 q2 : Finset Validator}
    {s1 t1 s2 t2 : Hash} {s1_h t1_h s2_h t2_h : Nat}
    (hwf_st : votes_from_target_vset_property vset st)
    (hq1sub : q1 ⊆ vset t1)
    (hq2sub : q2 ⊆ vset t2) :
    votes_from_target_vset_property vset
      (extend_state_with_two_vote_sets st
        (votes_for_link q1 s1 t1 s1_h t1_h)
        (votes_for_link q2 s2 t2 s2_h t2_h)) :=
  fun {_} {_} {_} {_} {_} hx =>
    (vote_msg_extend_classify (mem_link_supporters.mp hx)).elim
      (fun hOld => hwf_st (mem_link_supporters.mpr hOld))
      (fun h => h.elim
        (fun ⟨hxq1, rfl, rfl, rfl, rfl⟩ => hq1sub hxq1)
        (fun ⟨hxq2, rfl, rfl, rfl, rfl⟩ => hq2sub hxq2))

end GasperBeaconChain.Core
