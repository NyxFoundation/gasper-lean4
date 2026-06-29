import GasperBeaconChain.Core.Lemmas.PlausibleLiveness
import Mathlib.Tactic.Explode


universe u v

namespace GasperBeaconChain.Core

/-!
# Plausible liveness

This file proves the plausible-liveness theorem: under the standing
hypotheses (no slashing, good votes, quorum nonemptiness,
two-thirds-good validators, and blocks at arbitrary heights), the
protocol state can **always** be extended with two new
supermajority links that finalize a new block — without introducing
any new slashing.

This formalises Casper FFG's Theorem 2 (Plausible Liveness) /
Gasper's Theorem 6.1: *regardless of any previous events, it is
always possible for new blocks to be finalized, provided that new
blocks can be created by the underlying blockchain*. The emphasis
is that honest validators are never forced to violate a slashing
condition in order to make progress — the protocol cannot
"deadlock" into a state where finalization requires voluntary
slashing. This is a purely non-probabilistic property about the
logic of the protocol, requiring no synchrony assumptions.

## Structure

The proof proceeds in three stages:

1. **No new slashing** ({lit}`no_new_double_vote_two_link_extension`,
   {lit}`no_new_surround_vote_two_link_extension`,
   {lit}`no_new_slashed_two_link_extension`): adding two
   carefully-chosen vote batches at heights $`H + 1` and $`H + 2`
   (where $`H = \operatorname{highest\_target}(\sigma)`) cannot
   create any new double-vote or surround-vote violation. The
   proof is a $`3 \times 3` case matrix (old / link-1 / link-2 for
   each of the two conflicting votes), with each off-diagonal cell
   ruled out by a height argument. The key insight is that the two
   new target heights $`H + 1, H + 2` are *strictly above* every
   existing target height $`\le H`, so they cannot collide with
   old votes (for (S1)) and cannot be surrounded by old votes
   (for (S2)).

2. **Extension construction**
   ({lit}`plausible_liveness_construct_extension`): assembles the
   extended state $`\sigma'` from the highest justified block, two
   fresh quorums from {lit}`two_thirds_good`, and two new
   supermajority links built by
   {lit}`supermajority_link_of_quorum_votes`. Verifies all five
   conditions: vote inclusion, well-formedness, no new slashing,
   justification of the new finalized block, and the finalizing
   parent edge. This is a 1-finalization construction: the new
   finalized block $`\mathit{nf}` is justified at height $`H + 1`,
   and the finalizing link goes from $`(\mathit{nf}, H{+}1)` to
   $`(\mathit{nc}, H{+}2)`, matching the definition of
   {lit}`finalized` at depth $`k = 1`.

3. **Coq-compatible wrapper**
   ({lit}`plausible_liveness_from_coq_blocks_exist`): replaces the
   corrected block-existence hypothesis with the Coq-faithful one
   via {lit}`blocks_exist_high_over_of_coq`.

## Non-goals of this file

This file proves *plausible* liveness only — it shows that
finalization is always *possible*. It does *not* prove
*probabilistic* liveness (that finalization is *likely* under
synchrony assumptions), which is a separate, stronger result
discussed in Gasper's Section 7 but not formalised in this
development.
-/

variable {Validator : Type u}
variable {Hash : Type v}
variable [DecidableEq Validator]
variable [DecidableEq Hash]


/-!
## Height-transport helpers

The following private lemmas transport strict/non-strict
inequalities and equalities across height-level identifications
(e.g. $`th = H + 1`). They are used in the $`3 \times 3` case
matrix of {lit}`no_new_double_vote_two_link_extension` and
{lit}`no_new_surround_vote_two_link_extension` to derive
contradictions when two votes from different height levels would
need to share a target or source height.
-/

/-- Transport $`a < b` along $`a = c` to get $`c < b`. -/
private theorem lt_of_eq_left {a b c : Nat} (ha : a = c) (hlt : a < b) : c < b :=
  match ha with | rfl => hlt
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode lt_of_eq_left

/-- Transport $`a < b` along $`b = c` to get $`a < c`. -/
private theorem lt_of_eq_right {a b c : Nat} (hb : b = c) (hlt : a < b) : a < c :=
  match hb with | rfl => hlt
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode lt_of_eq_right

/-- From $`a = b` derive $`b \le a`. -/
private theorem le_of_eq {a b : Nat} (h : a = b) : b ≤ a :=
  match h with | rfl => Nat.le_refl _
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode le_of_eq

/-- From $`th = H + 1` and $`th \le H` derive $`H + 1 \le H` (absurd). -/
private theorem le_of_height_eq_add_one
    {th H : Nat} (hth : th = H + 1) (hle : th ≤ H) : H + 1 ≤ H :=
  match hth with | rfl => hle
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode le_of_height_eq_add_one

/-- From $`th = H + 2` and $`th \le H` derive $`H + 2 \le H` (absurd). -/
private theorem le_of_height_eq_add_two
    {th H : Nat} (hth : th = H + 2) (hle : th ≤ H) : H + 2 ≤ H :=
  match hth with | rfl => hle
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode le_of_height_eq_add_two

/-- From $`a = c` and $`b = c` derive $`a = b`. -/
private theorem eq_of_eq_right
    {α : Type*} {a b c : α} (ha : a = c) (hb : b = c) : a = b :=
  match ha with | rfl => match hb with | rfl => rfl
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode eq_of_eq_right

/-- From $`x = y` and $`x = z` derive $`y = z`. -/
private theorem eq_of_eq_left
    {x y z : Nat} (hy : x = y) (hz : x = z) : y = z :=
  match hy with | rfl => hz
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode eq_of_eq_left


/--
# Adding two links at heights $`H+1` and $`H+2` creates no new double vote

# Statement

$$`\operatorname{slashed\_double\_vote}\bigl(\sigma \uplus V_1 \uplus V_2,\; v\bigr) \;\implies\; \operatorname{slashed\_double\_vote}(\sigma, v)`

where $`V_1 = \operatorname{votes\_for\_link}(q_1, s_1, t_1, s_{1,h}, H{+}1)`
and $`V_2 = \operatorname{votes\_for\_link}(q_2, s_2, t_2, H{+}1, H{+}2)`.
Any double vote in the extended state was already a double vote in
the original state.

# Assumptions

* {lit}`hBound` — every vote in $`\sigma` has target height
  $`\le H` ({lit}`target_height_bound`);
* {lit}`hdbl` — the double-vote witness in the extended state.

# Proof idea

Classify each of the two conflicting votes as old / from link 1 /
from link 2 via {lit}`vote_msg_extend_classify`, yielding a
$`3 \times 3` case matrix. The three target-height levels are
$`\le H` (old votes, by {lit}`target_height_bound`), $`H + 1`
(link 1), and $`H + 2` (link 2). A double vote requires a *shared*
target height, so:

* *old × old*: the pre-existing double vote is returned.
* *old × link* or *link × old* (4 cells): the shared target height
  would force $`H + 1 \le H` or $`H + 2 \le H`, both absurd
  ({lit}`Nat.not_add_one_le_self`, {lit}`not_add_two_le_self`).
* *link 1 × link 2* or *link 2 × link 1* (2 cells): the shared
  target height would force $`H + 1 = H + 2`, absurd
  ({lit}`add_one_ne_add_two`).
* *link 1 × link 1* or *link 2 × link 2* (2 cells): both votes
  target the same block, so $`t_1 = t_2` contradicts $`t_1 \ne t_2`
  ({lit}`eq_of_eq_right`).
-/
theorem no_new_double_vote_two_link_extension
    {st : State Validator Hash}
    {q1 q2 : Finset Validator}
    {s1 t1 s2 t2 : Hash}
    {s1_h : Nat} {H : Nat} {v : Validator}
    (hBound : target_height_bound st H)
    (hdbl : slashed_double_vote
      (extend_state_with_two_vote_sets st
        (votes_for_link q1 s1 t1 s1_h (H + 1))
        (votes_for_link q2 s2 t2 (H + 1) (H + 2))) v) :
    slashed_double_vote st v :=
  match hdbl with
  | ⟨ta, tb, hneq, sa, sha, sb, shb, th, hvA, hvB⟩ =>
  match vote_msg_extend_classify hvA with
  | Or.inl hOldA =>
    match vote_msg_extend_classify hvB with
    | Or.inl hOldB =>
        ⟨ta, tb, hneq, sa, sha, sb, shb, th, hOldA, hOldB⟩
    | Or.inr (Or.inl ⟨_, _, _, _, hthB⟩) =>
        False.elim ((Nat.not_add_one_le_self H)
          (le_of_height_eq_add_one hthB (target_height_le_of_vote_msg hBound hOldA)))
    | Or.inr (Or.inr ⟨_, _, _, _, hthB⟩) =>
        False.elim ((not_add_two_le_self H)
          (le_of_height_eq_add_two hthB (target_height_le_of_vote_msg hBound hOldA)))
  | Or.inr (Or.inl ⟨_, _, htaA, _, hthA⟩) =>
    match vote_msg_extend_classify hvB with
    | Or.inl hOldB =>
        False.elim ((Nat.not_add_one_le_self H)
          (le_of_height_eq_add_one hthA (target_height_le_of_vote_msg hBound hOldB)))
    | Or.inr (Or.inl ⟨_, _, htbB, _, _⟩) =>
        False.elim (hneq (eq_of_eq_right htaA htbB))
    | Or.inr (Or.inr ⟨_, _, _, _, hthB⟩) =>
        False.elim ((add_one_ne_add_two H) (eq_of_eq_left hthA hthB))
  | Or.inr (Or.inr ⟨_, _, htaA, _, hthA⟩) =>
    match vote_msg_extend_classify hvB with
    | Or.inl hOldB =>
        False.elim ((not_add_two_le_self H)
          (le_of_height_eq_add_two hthA (target_height_le_of_vote_msg hBound hOldB)))
    | Or.inr (Or.inl ⟨_, _, _, _, hthB⟩) =>
        False.elim ((add_two_ne_add_one H) (eq_of_eq_left hthA hthB))
    | Or.inr (Or.inr ⟨_, _, htbB, _, _⟩) =>
        False.elim (hneq (eq_of_eq_right htaA htbB))
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode no_new_double_vote_two_link_extension


variable [Fintype Validator]


/--
# Adding two links at heights $`H+1` and $`H+2` creates no new surround vote

# Statement

$$`\operatorname{slashed\_surround\_vote}\bigl(\sigma \uplus V_1 \uplus V_2,\; v\bigr) \;\implies\; \operatorname{slashed\_surround\_vote}(\sigma, v)`

Any surround vote in the extended state was already a surround
vote in the original state.

# Assumptions

* {lit}`hBound` — target-height bound: every vote in $`\sigma` has
  target height $`\le H`;
* {lit}`hJustBound` — justified-height bound: every justified
  block in $`\sigma` has height $`\le H` (needed for the
  *link 2 O $`\times` old I* cell, where the inner vote's justified
  source height is bounded by $`H` while the outer source height
  is $`H + 1`);
* {lit}`hHighest` — the block $`s_1` at height $`s_{1,h}` is the
  unique highest justified block (needed for the *link 1 O
  $`\times` old I* cell);
* {lit}`hGood` — good votes: every quorum member's votes have
  justified sources and forward links (extracts the inner vote's
  source justification from the outer quorum membership);
* {lit}`hq1`, {lit}`hq2` — $`q_1`, $`q_2` are
  $`\frac{2}{3}`-quorums at $`t_1`, $`t_2` respectively;
* {lit}`hs1_le` — $`s_{1,h} \le H` (the highest justified height
  does not exceed the target bound).

# Proof idea

Same $`3 \times 3` case matrix as the double-vote theorem (outer
vote O × inner vote I, each classified as old / link 1 / link 2),
but for the surround condition ($`h_{s_O} < h_{s_I}` and
$`h_{t_I} < h_{t_O}`).

* *old × old*: the pre-existing surround vote is returned.
* *old O × new I* (2 cells): the inner vote's target height
  ($`H+1` or $`H+2`) exceeds the outer vote's target height
  ($`\le H`), contradicting $`h_{t_I} < h_{t_O}`.
* *link 1 O × old I*: the **critical cell**. The outer vote is
  from $`q_1`, so {lit}`good_votes` gives
  $`\operatorname{justified}(\sigma, \mathit{is}, \mathit{ish})` for
  the inner vote's source. {lit}`highest_justified` then forces
  $`\mathit{ish} \le s_{1,h}`, but the surround's source ordering
  gives $`s_{1,h} < \mathit{ish}` — a contradiction.
* *link 2 O × old I*: similar, but uses {lit}`hJustBound`
  ($`\mathit{ish} \le H`) against $`H + 1 < \mathit{ish}` from
  the source ordering.
* *link 1 O × link 1 I*: both source heights equal $`s_{1,h}`,
  giving $`s_{1,h} < s_{1,h}` — absurd ({lit}`Nat.lt_irrefl`).
* *link 2 O × link 1 I*: $`s_{1,h} \le H` combined with
  $`H + 1 < s_{1,h}` via the source ordering — absurd.
* *link 1 O × link 2 I* or *link 2 O × link 2 I*: target heights
  give $`H + 2 < H + 1` or $`H + 2 < H + 2`, both absurd.
-/
theorem no_new_surround_vote_two_link_extension
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    {st : State Validator Hash}
    {q1 q2 : Finset Validator}
    {s1 t1 t2 : Hash} {s1_h : Nat} {H : Nat} {v : Validator}
    (hBound : target_height_bound st H)
    (hJustBound : ∀ {b : Hash} {h : Nat},
      justified τ stake vset parent genesis st b h → h ≤ H)
    (hHighest : highest_justified τ stake vset parent genesis st s1 s1_h)
    (hGood : good_votes τ stake vset parent genesis st)
    (hq1 : quorum_2 τ stake vset q1 t1)
    (hq2 : quorum_2 τ stake vset q2 t2)
    (hs1_le : s1_h ≤ H)
    (hsurr : slashed_surround_vote
      (extend_state_with_two_vote_sets st
        (votes_for_link q1 s1 t1 s1_h (H + 1))
        (votes_for_link q2 t1 t2 (H + 1) (H + 2))) v) :
    slashed_surround_vote st v :=
  match hsurr with
  | ⟨os, ot, osh, oth, is_, it_, ish, ith, hvO, hvI, hlt_src, hlt_tgt⟩ =>
  match vote_msg_extend_classify hvO with
  | Or.inl hOldO =>
    match vote_msg_extend_classify hvI with
    | Or.inl hOldI =>
        ⟨os, ot, osh, oth, is_, it_, ish, ith, hOldO, hOldI, hlt_src, hlt_tgt⟩
    | Or.inr (Or.inl ⟨_, _, _, _, hthI⟩) =>
        False.elim (not_add_one_lt_of_le (target_height_le_of_vote_msg hBound hOldO)
          (lt_of_eq_left hthI hlt_tgt))
    | Or.inr (Or.inr ⟨_, _, _, _, hthI⟩) =>
        False.elim (not_add_two_lt_of_le (target_height_le_of_vote_msg hBound hOldO)
          (lt_of_eq_left hthI hlt_tgt))
  | Or.inr (Or.inl ⟨hvqO, _, _, hoshO, hthO⟩) =>
    match vote_msg_extend_classify hvI with
    | Or.inl hOldI =>
        have hjs : justified τ stake vset parent genesis st is_ ish :=
          match hGood _ q1 hq1 v hvqO with
          | ⟨hjs_src, _⟩ => hjs_src is_ it_ ish ith hOldI
        match hHighest is_ ish (Nat.le_of_lt (lt_of_eq_left hoshO hlt_src)) hjs with
        | ⟨_, hEq⟩ => False.elim ((Nat.not_lt.mpr (Nat.le_of_eq hEq)) (lt_of_eq_left hoshO hlt_src))
    | Or.inr (Or.inl ⟨_, _, _, hishI, _⟩) =>
        False.elim (Nat.lt_irrefl _ (lt_of_eq_left hoshO (lt_of_eq_right hishI hlt_src)))
    | Or.inr (Or.inr ⟨_, _, _, _, hthI⟩) =>
        False.elim (not_add_two_lt_add_one H
          (lt_of_eq_left hthI (lt_of_eq_right hthO hlt_tgt)))
  | Or.inr (Or.inr ⟨hvqO, _, _, hoshO, hthO⟩) =>
    match vote_msg_extend_classify hvI with
    | Or.inl hOldI =>
        have hjs : justified τ stake vset parent genesis st is_ ish :=
          match hGood _ q2 hq2 v hvqO with
          | ⟨hjs_src, _⟩ => hjs_src is_ it_ ish ith hOldI
        False.elim (not_add_one_lt_of_le (hJustBound hjs) (lt_of_eq_left hoshO hlt_src))
    | Or.inr (Or.inl ⟨_, _, _, hishI, _⟩) =>
        False.elim (not_add_one_lt_of_le hs1_le (lt_of_eq_left hoshO (lt_of_eq_right hishI hlt_src)))
    | Or.inr (Or.inr ⟨_, _, _, _, hthI⟩) =>
        False.elim (Nat.lt_irrefl _
          (lt_of_eq_left hthI (lt_of_eq_right hthO hlt_tgt)))
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode no_new_surround_vote_two_link_extension


/--
# Adding two links creates no new slashing (either condition)

# Statement

$$`\operatorname{no\_new\_slashed}\bigl(\sigma,\; \sigma \uplus V_1 \uplus V_2\bigr)`

Every {name}`slashed` validator in the extended state was already
slashed in the original state $`\sigma`.

# Interpretation

This is the disjunctive combination: a slashing witness in the
extended state is either a double vote (handled by
{lit}`no_new_double_vote_two_link_extension`) or a surround vote
(handled by {lit}`no_new_surround_vote_two_link_extension`). In
both cases, the slashing already existed in $`\sigma`.

# Proof idea

Given a slashing witness {lit}`hslash` in the extended state,
case-split on the {name}`slashed` disjunction. The left branch
(double vote) delegates to
{lit}`no_new_double_vote_two_link_extension`; the right branch
(surround vote) delegates to
{lit}`no_new_surround_vote_two_link_extension`, passing through
all six standing hypotheses.

# Role in the development

One of the two conditions (together with
{lit}`unslashed_can_extend_two_vote_sets`) that the
plausible-liveness construction must verify for the extended state.
Consumed directly by
{lit}`plausible_liveness_construct_extension`.
-/
theorem no_new_slashed_two_link_extension
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    {st : State Validator Hash}
    {q1 q2 : Finset Validator}
    {s1 t1 t2 : Hash} {s1_h : Nat} {H : Nat}
    (hBound : target_height_bound st H)
    (hJustBound : ∀ {b : Hash} {h : Nat},
      justified τ stake vset parent genesis st b h → h ≤ H)
    (hHighest : highest_justified τ stake vset parent genesis st s1 s1_h)
    (hGood : good_votes τ stake vset parent genesis st)
    (hq1 : quorum_2 τ stake vset q1 t1)
    (hq2 : quorum_2 τ stake vset q2 t2)
    (hs1_le : s1_h ≤ H) :
    no_new_slashed st
      (extend_state_with_two_vote_sets st
        (votes_for_link q1 s1 t1 s1_h (H + 1))
        (votes_for_link q2 t1 t2 (H + 1) (H + 2))) :=
  fun _ hslash => hslash.elim
    (fun hdbl => Or.inl (no_new_double_vote_two_link_extension hBound hdbl))
    (fun hsurr => Or.inr (no_new_surround_vote_two_link_extension
      τ stake vset parent genesis hBound hJustBound hHighest hGood hq1 hq2 hs1_le hsurr))
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode no_new_slashed_two_link_extension



/--
# Plausible liveness: construction of the extension (main theorem)

# Statement

$$`\exists\, \sigma',\;\; \operatorname{unslashed\_can\_extend}(\sigma, \sigma') \;\wedge\; \operatorname{no\_new\_slashed}(\sigma, \sigma') \;\wedge\; \exists\, \mathit{nf}\, \mathit{nc}\, h,\;\; \operatorname{justified}(\sigma', \mathit{nf}, h) \;\wedge\; \mathit{nf} \to \mathit{nc} \;\wedge\; \operatorname{supermajority\_link}(\sigma', \mathit{nf}, \mathit{nc}, h, h{+}1)`

# Interpretation

Under the standing hypotheses, the protocol can *always* extend
the current state to finalize a new block — no matter what has
happened previously (attacks, latency, etc.). The extended state
$`\sigma'` satisfies three properties simultaneously: (1) only
unslashed validators contribute new votes, (2) no validator becomes
newly slashed, and (3) a fresh block $`\mathit{nf}` becomes both
justified and equipped with a finalizing supermajority link to its
child $`\mathit{nc}`. This is a *constructive* existence proof:
the state $`\sigma'` and the blocks $`\mathit{nf}, \mathit{nc}`
are explicitly assembled from the existing state, not merely
asserted to exist. The construction produces a 1-finalization
(the simplest case of {lit}`k_finalized` at $`k = 1`).

# Proof idea

Let $`H = \operatorname{highest\_target}(\sigma)`.

1. {lit}`highest_exists` produces the unique highest justified block
   $`(jm, jmh)` with $`jmh \le H`
   ({lit}`justified_height_le_highest_target`).
2. {lit}`blocks_exist_extract_new_final_pair` extracts two blocks
   $`\mathit{nf}, \mathit{nc}` with
   $`jm \xrightarrow{H + 1 - jmh} \mathit{nf}` and
   $`\mathit{nf} \to \mathit{nc}` in the block tree.
3. {lit}`two_thirds_good` supplies two fresh
   $`\frac{2}{3}`-quorums $`q_f \subseteq V(\mathit{nf})` and
   $`q_c \subseteq V(\mathit{nc})`, each consisting of unslashed
   validators.
4. The extended state is
   $`\sigma' = (\sigma \uplus V_1) \uplus V_2` where
   $`V_1 = \operatorname{votes\_for\_link}(q_f, jm, \mathit{nf}, jmh, H{+}1)`
   and
   $`V_2 = \operatorname{votes\_for\_link}(q_c, \mathit{nf}, \mathit{nc}, H{+}1, H{+}2)`.
5. Verify the five conjuncts:
   * {lit}`unslashed_can_extend` — each new voter is unslashed in
     $`\sigma` ({lit}`unslashed_can_extend_two_vote_sets`);
   * {lit}`no_new_slashed` — the two new links at heights $`H{+}1`
     and $`H{+}2` cannot create a double vote or surround vote with
     old votes whose target heights are $`\le H`
     ({lit}`no_new_slashed_two_link_extension`);
   * justification of $`\mathit{nf}` at height $`H{+}1` — carry
     $`jm`'s justification from $`\sigma` to $`\sigma'` via
     {lit}`justified_weaken`, then apply {lit}`justified_link` with
     the first supermajority link (built by
     {lit}`supermajority_link_of_quorum_votes` from $`q_f`);
   * parent edge $`\mathit{nf} \to \mathit{nc}` — from step 2;
   * finalizing supermajority link from $`(\mathit{nf}, H{+}1)` to
     $`(\mathit{nc}, H{+}2)` — built by a second application of
     {lit}`supermajority_link_of_quorum_votes` from $`q_c`.

# Assumptions

* {name}`QuorumContext` — quorum nonemptiness;
* {lit}`two_thirds_good` — fresh unslashed quorums exist at each
  block;
* $`\neg\,\operatorname{q\_intersection\_slashed}` — no slashing in
  $`\sigma` (used by {lit}`highest_exists` for uniqueness);
* {lit}`good_votes` — quorum voters have justified sources and
  forward links (used by {lit}`highest_exists` and
  {lit}`no_new_slashed_two_link_extension`);
* {lit}`votes_from_target_vset_property` — vote well-formedness of
  $`\sigma` (used by {lit}`justified_weaken` and
  {lit}`supermajority_link_of_quorum_votes`);
* block-existence hypothesis — blocks at arbitrarily large heights
  above the highest justified block (used by
  {lit}`blocks_exist_extract_new_final_pair`).

# Non-assumptions

* no assumption about the *content* of $`\sigma` beyond the standing
  hypotheses — the construction works regardless of how many votes
  or links the state already contains;
* the new finalized block $`\mathit{nf}` is not assumed to be
  previously known or justified — its justification is *constructed*
  in the proof;
* no specific value of $`H` or $`jmh` is required — the proof
  adapts to whatever the current highest target and highest justified
  height happen to be.
-/
theorem plausible_liveness_construct_extension
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash) (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    (htwothirds : two_thirds_good τ stake vset st)
    (hunslashed : ¬ q_intersection_slashed τ stake vset st)
    (hgood : good_votes τ stake vset parent genesis st)
    (hwf_st : votes_from_target_vset_property vset st)
    (hheight : ∀ b b_h,
      highest_justified τ stake vset parent genesis st b b_h →
      blocks_exist_high_over parent b) :
    ∃ st' : State Validator Hash,
      unslashed_can_extend st st' ∧
      no_new_slashed st st' ∧
      ∃ nf nc : Hash, ∃ nh : Nat,
        justified τ stake vset parent genesis st' nf nh ∧
        parent nf nc ∧
        supermajority_link τ stake vset st' nf nc nh (nh + 1) :=
  match highest_exists τ stake vset parent genesis st qctx hunslashed hgood with
  | ⟨jm, jmh, hjm_j, hjm_high⟩ =>
  have hjmh_le : jmh ≤ highest_target st :=
    justified_height_le_highest_target τ stake vset parent genesis st qctx hjm_j
  match blocks_exist_extract_new_final_pair parent st
    (hheight jm jmh hjm_high) hjmh_le with
  | ⟨nf, nc, hnth, hpar⟩ =>
  match htwothirds nf, htwothirds nc with
  | ⟨qf, hqf, hunsf⟩, ⟨qc, hqc, hunsc⟩ =>
  match hqf, hqc with
  | ⟨hqf_sub, _⟩, ⟨hqc_sub, _⟩ =>
  have hsub : ∀ vote, vote ∈ st → vote ∈
      extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)) :=
    fun _ h => old_votes_subset_extended h
  have hwf' : votes_from_target_vset_property vset
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1))) :=
    votes_from_target_vset_extend_two_vote_sets vset hwf_st hqf_sub hqc_sub
  have huce : unslashed_can_extend st
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1))) :=
    unslashed_can_extend_two_vote_sets hunsf hunsc
  have hNoNew : no_new_slashed st
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1))) :=
    no_new_slashed_two_link_extension τ stake vset parent genesis
      (highest_target_is_bound st)
      (fun hj => justified_height_le_highest_target τ stake vset parent genesis st qctx hj)
      hjm_high hgood hqf hqc hjmh_le
  have hjm' : justified τ stake vset parent genesis
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)))
      jm jmh :=
    justified_weaken τ stake vset parent genesis hsub hwf' hjm_j
  have hv1_sub : votes_for_link qf jm nf jmh (highest_target st + 1) ⊆
      extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)) :=
    fun _ h => first_new_votes_subset_extended h
  have hsm1 : supermajority_link τ stake vset
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)))
      jm nf jmh (highest_target st + 1) :=
    supermajority_link_of_quorum_votes τ stake vset hqf hv1_sub hwf'
  have hfwd : jmh < highest_target st + 1 := height_lt_highest_target_succ st hjmh_le
  have hjnf : justified τ stake vset parent genesis
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)))
      nf (highest_target st + 1) :=
    justified.justified_link hjm' ⟨hfwd, hnth, hsm1⟩
  have hv2_sub : votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1) ⊆
      extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)) :=
    fun _ h => second_new_votes_subset_extended h
  have hsm2 : supermajority_link τ stake vset
      (extend_state_with_two_vote_sets st
        (votes_for_link qf jm nf jmh (highest_target st + 1))
        (votes_for_link qc nf nc (highest_target st + 1) (highest_target st + 1 + 1)))
      nf nc (highest_target st + 1) (highest_target st + 1 + 1) :=
    supermajority_link_of_quorum_votes τ stake vset hqc hv2_sub hwf'
  ⟨_, huce, hNoNew, nf, nc, highest_target st + 1, hjnf, hpar, hsm2⟩
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode plausible_liveness_construct_extension


/--
# Plausible liveness (Coq-compatible block-existence hypothesis)

# Statement

The same conclusion as
{lit}`plausible_liveness_construct_extension` — existence of an
extended state with no new slashing, a justified new finalized
block, and a finalizing supermajority link — but with the
block-existence hypothesis stated in the Coq-faithful form
{lit}`blocks_exist_high_over_coq` rather than the corrected
{lit}`blocks_exist_high_over`.

# Interpretation

A compatibility wrapper: the Coq formulation of block existence
places the height guard $`1 < n` inside the existential, making it
unsatisfiable as written (see
{lit}`not_blocks_exist_high_over_coq`). Nevertheless, this
theorem accepts the Coq predicate as input and converts it via
{lit}`blocks_exist_high_over_of_coq` before delegating to the
main construction. This preserves a faithful interface for
comparison with the Coq development while using the corrected
formulation internally.

# Non-assumptions

All hypotheses are identical to those of
{lit}`plausible_liveness_construct_extension` except for the
block-existence predicate. In particular, no additional
assumptions are introduced by the Coq-compatibility wrapping.
-/
theorem plausible_liveness_from_coq_blocks_exist
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash) (st : State Validator Hash)
    (qctx : QuorumContext τ stake vset)
    (htwothirds : two_thirds_good τ stake vset st)
    (hunslashed : ¬ q_intersection_slashed τ stake vset st)
    (hgood : good_votes τ stake vset parent genesis st)
    (hwf_st : votes_from_target_vset_property vset st)
    (hheight : ∀ b b_h,
      highest_justified τ stake vset parent genesis st b b_h →
      blocks_exist_high_over_coq parent b) :
    ∃ st' : State Validator Hash,
      unslashed_can_extend st st' ∧
      no_new_slashed st st' ∧
      ∃ nf nc : Hash, ∃ nh : Nat,
        justified τ stake vset parent genesis st' nf nh ∧
        parent nf nc ∧
        supermajority_link τ stake vset st' nf nc nh (nh + 1) :=
  plausible_liveness_construct_extension
    τ stake vset parent genesis st qctx htwothirds hunslashed hgood hwf_st
    (fun b b_h hh => blocks_exist_high_over_of_coq (hheight b b_h hh))
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode plausible_liveness_from_coq_blocks_exist


end GasperBeaconChain.Core
