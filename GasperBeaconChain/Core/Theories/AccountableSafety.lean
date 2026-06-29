import GasperBeaconChain.Core.Lemmas.AccountableSafety
import GasperBeaconChain.Core.Lemmas.StrongInductionLtn
import GasperBeaconChain.Core.Lemmas.ListExt
import Mathlib.Tactic.Explode

universe u v

namespace GasperBeaconChain.Core

/-!
# Accountable safety

This file proves the main accountable-safety theorem: a
**finalization fork** — two $`k`-finalized blocks that are mutual
non-ancestors — forces a {lit}`q_intersection_slashed` witness.
This is the *structural* half of the Casper FFG accountable-safety
guarantee: it produces a pair of $`\frac{2}{3}`-quorums whose
intersection consists entirely of slashed validators, without
asserting that the intersection is nonempty (the *quantitative*
half, carried out in {lit}`Theories/SlashableBound.lean`).

The result generalises the original Casper FFG theorem (Casper FFG,
Theorem 1 / Gasper, Theorem 5.2) from $`1`-finalization to
arbitrary $`k`-finalization, and from static to dynamic validator
sets (the two quorums may belong to different blocks with different
validator sets $`V(b_L), V(b_R)`).

## Definitions

* {lit}`finalization_fork` — a pair of finalized blocks with mutual
  non-ancestry (the safety-violation predicate)
* {lit}`k_finalization_fork` / {lit}`same_k_finalization_fork` — the
  $`k`-finalized generalisation with independent depths

## Case analysis

The proof of {lit}`k_safety'` proceeds by three-way case split on
the heights $`b_{1,h}` and $`b_{2,h}` of the two $`k`-finalized
blocks. Each branch terminates by exhibiting a
{lit}`q_intersection_slashed` witness from one of two slashing
conditions:

* *Equal heights* ({lit}`k_equal_height_case`) — Casper (S1):
  two distinct justified blocks at the same height force a
  double-vote witness via
  {lit}`two_justified_same_height_slashed`.
* *Surround case* ({lit}`k_slash_surround_case_general`) —
  Casper (S2): a justification link that spans the finalized
  block's chain on the height axis produces a surround-vote
  witness, or collapses to a same-height double-vote.
* *Non-equal heights, inductive*
  ({lit}`k_non_equal_height_case_ind`) — strong induction on the
  height gap $`b_{1,h} - b_{2,h}` via {lit}`strong_induction_sub`,
  descending along justification links until one of the two base
  cases above applies.

## Derivation chain

$$`\operatorname{accountable\_safety} \;\xleftarrow{\text{convert}}\; \operatorname{k\_accountable\_safety} \;\xleftarrow{\text{destruct}}\; \operatorname{k\_safety'} \;\xleftarrow{\text{3-way}}\; \begin{cases} \operatorname{k\_equal\_height\_case} \\ \operatorname{k\_non\_equal\_height\_case} \to \operatorname{k\_non\_equal\_height\_case\_ind} \end{cases}`

## Non-goals of this file

This file is the *structural* half only. It proves that every
shared validator is slashed, but does *not* prove that the shared
set has positive weight. The quantitative bound
$`\operatorname{wt}(V_L \cap V_R) - f_{1/3}(\operatorname{wt}(V_L)) - f_{1/3}(\operatorname{wt}(V_R)) \le \operatorname{wt}(q_L \cap q_R)`
is established independently in {lit}`Theories/SlashableBound.lean`.
-/

variable {Validator : Type u}
variable {Hash : Type v}
variable [DecidableEq Validator]
variable [DecidableEq Hash]
variable [Fintype Validator]

/--
# Two finalized blocks with mutual non-ancestry

A **finalization fork**: two blocks $`b_1, b_2`, each finalized in
$`\sigma`, such that neither is an ancestor of the other.

# Formal content

$$`\exists\, b_1\, b_{1,h}\, b_2\, b_{2,h},\;\; \operatorname{finalized}(\sigma, b_1, b_{1,h}) \;\wedge\; \operatorname{finalized}(\sigma, b_2, b_{2,h}) \;\wedge\; \neg\,(b_2 \xrightarrow{*} b_1) \;\wedge\; \neg\,(b_1 \xrightarrow{*} b_2)`

# Interpretation

This is the abstract formulation of a safety violation in
Casper FFG: two blocks have been irreversibly committed by
$`\frac{2}{3}`-quorum support, yet neither lies on the other's
chain. In a tree-structured block universe, this means the protocol
has committed to two incompatible histories.

# Non-assumptions

The predicate does *not* assert that $`b_1 \ne b_2` (distinctness
is a consequence of the mutual non-ancestry, since reflexivity of
ancestry gives $`b \xrightarrow{*} b`). It also does not assert
any relationship between the two heights $`b_{1,h}` and $`b_{2,h}`.
-/
def finalization_fork
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash) : Prop :=
  ∃ b1 : Hash, ∃ b1_h : Nat, ∃ b2 : Hash, ∃ b2_h : Nat,
    finalized τ stake vset parent genesis st b1 b1_h ∧
    finalized τ stake vset parent genesis st b2 b2_h ∧
    ¬ hash_ancestor parent b2 b1 ∧
    ¬ hash_ancestor parent b1 b2


/--
# $`k`-finalization fork

The $`k`-finalized generalisation of {lit}`finalization_fork`: two
blocks $`b_1, b_2`, each $`k_i`-finalized, with mutual non-ancestry.

# Formal content

$$`\exists\, b_1\, b_{1,h}\, b_2\, b_{2,h},\;\; \operatorname{k\_finalized}(\sigma, b_1, b_{1,h}, k_1) \;\wedge\; \operatorname{k\_finalized}(\sigma, b_2, b_{2,h}, k_2) \;\wedge\; \neg\,(b_2 \xrightarrow{*} b_1) \;\wedge\; \neg\,(b_1 \xrightarrow{*} b_2)`

# Interpretation

The two finalization depths $`k_1, k_2` are independent parameters,
allowing the two conflicting blocks to have different depths of
confirmation. At $`k_1 = k_2 = 1` this recovers
{lit}`finalization_fork` (via
{lit}`finalization_fork_means_same_finalization_fork_one`).
-/
def k_finalization_fork
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (k1 k2 : Nat) : Prop :=
  ∃ b1 : Hash, ∃ b1_h : Nat, ∃ b2 : Hash, ∃ b2_h : Nat,
    k_finalized τ stake vset parent genesis st b1 b1_h k1 ∧
    k_finalized τ stake vset parent genesis st b2 b2_h k2 ∧
    ¬ hash_ancestor parent b2 b1 ∧
    ¬ hash_ancestor parent b1 b2


/--
# Symmetric $`k`-finalization fork

Both blocks share the same finalization depth $`k`:

$$`\operatorname{same\_k\_finalization\_fork}(\sigma, k) \;\;\coloneqq\;\; \operatorname{k\_finalization\_fork}(\sigma, k, k)`

This specialisation is the form consumed by
{lit}`finalization_fork_means_same_finalization_fork_one`, where
the $`k = 1` instance recovers {lit}`finalization_fork`.
-/
def same_k_finalization_fork
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (k : Nat) : Prop :=
  k_finalization_fork τ stake vset parent genesis st k k


/--
# Finalization fork is equivalent to $`1`-finalization fork

# Statement

$$`\operatorname{finalization\_fork}(\sigma) \;\iff\; \operatorname{same\_k\_finalization\_fork}(\sigma, 1)`

# Proof idea

Both directions apply {lit}`finalized_means_one_finalized` to
each of the two finalized blocks in the fork, converting between
{lit}`finalized` and $`\operatorname{k\_finalized}(\cdot, \cdot, 1)`.
The non-ancestry hypotheses $`\neg\,(b_2 \xrightarrow{*} b_1)` and
$`\neg\,(b_1 \xrightarrow{*} b_2)` pass through unchanged.

# Role in the development

The single bridge between the {lit}`finalization_fork` definition
(stated in terms of {lit}`finalized`) and the $`k`-parameterised
proof machinery. Consumed by {lit}`accountable_safety` to enter
the $`k`-finalized world, and inversely available if the user wishes
to return to the one-step formulation.
-/
theorem finalization_fork_means_same_finalization_fork_one
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash) :
    finalization_fork τ stake vset parent genesis st
      ↔
    same_k_finalization_fork τ stake vset parent genesis st 1 :=
  ⟨fun ⟨b1, b1_h, b2, b2_h, hfin1, hfin2, hn1, hn2⟩ =>
    ⟨b1, b1_h, b2, b2_h,
      (finalized_means_one_finalized τ stake vset parent genesis st b1 b1_h).mp hfin1,
      (finalized_means_one_finalized τ stake vset parent genesis st b2 b2_h).mp hfin2,
      hn1, hn2⟩,
   fun ⟨b1, b1_h, b2, b2_h, hk1, hk2, hn1, hn2⟩ =>
    ⟨b1, b1_h, b2, b2_h,
      (finalized_means_one_finalized τ stake vset parent genesis st b1 b1_h).mpr hk1,
      (finalized_means_one_finalized τ stake vset parent genesis st b2 b2_h).mpr hk2,
      hn1, hn2⟩⟩
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode finalization_fork_means_same_finalization_fork_one


/--
# A $`k`-finalized block and a distinct justified block have different heights

# Statement

$$`\operatorname{k\_finalized}(\sigma, b_f, h_f, k) \;\wedge\; \operatorname{justified}(\sigma, b_j, h_j) \;\wedge\; \neg\,\operatorname{q\_intersection\_slashed}(\sigma) \;\wedge\; b_j \ne b_f \;\implies\; h_j \ne h_f`

# Interpretation

A $`k`-finalized block occupies a unique height slot among
justified blocks: no other justified block can share its height
without triggering slashing. This is the height-separation
guarantee that feeds the three-way case split in {lit}`k_safety'`.

# Proof idea

Extract $`b_f`'s justification from its $`k`-finalization via
{lit}`k_finalized_means_justified`, then apply
{lit}`no_two_justified_same_height` to the two justified blocks
$`b_j` and $`b_f` at heights $`h_j` and $`h_f` with the
non-slashing hypothesis.

# Role in the development

A convenience lemma that packages the two-step reduction
($`k`-finalized $`\to` justified $`\to` height-separation) into
a single invocation. Used in the equal-height branch of the safety
argument to derive a contradiction when two non-ancestor blocks
appear at the same height.
-/
theorem no_k_finalized_justified_same_height
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {bf bj : Hash}
    {bf_h bj_h k : Nat}
    (hf : k_finalized τ stake vset parent genesis st bf bf_h k)
    (hj : justified τ stake vset parent genesis st bj bj_h)
    (hno : ¬ q_intersection_slashed τ stake vset st)
    (hneq : bj ≠ bf) :
    bj_h ≠ bf_h :=
  no_two_justified_same_height τ stake vset parent genesis st
    hj (k_finalized_means_justified τ stake vset parent genesis st hf)
    hno hneq
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode no_k_finalized_justified_same_height


/--
# Equal-height case: both blocks at the same height

# Statement

$$`\operatorname{k\_finalized}(\sigma, b_1, h, k_1) \;\wedge\; \operatorname{k\_finalized}(\sigma, b_2, h, k_2) \;\wedge\; b_1 \ne b_2 \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Interpretation

Two distinct $`k`-finalized blocks at the **same** height $`h` —
this is the direct manifestation of Casper's slashing condition
(S1): the two supporting $`\frac{2}{3}`-quorums have cast votes
to distinct targets at the same target height, so every shared
validator has equivocated ({lit}`slashed_double_vote`).

# Proof idea

Extract both blocks' justifications via
{lit}`k_finalized_means_justified`, then apply
{lit}`two_justified_same_height_slashed` — the same-height
slashing kernel from {lit}`Lemmas/AccountableSafety.lean` — to
the two justified blocks $`b_1, b_2` at height $`h` with
$`b_1 \ne b_2`.

# Role in the development

The base case of the safety case analysis: the equal-height branch
of {lit}`k_safety'`. The other two branches (surround and
inductive) eventually reduce to this case or to a direct surround
witness.
-/
theorem k_equal_height_case
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b1 b2 : Hash}
    {h k1 k2 : Nat}
    (hf1 : k_finalized τ stake vset parent genesis st b1 h k1)
    (hf2 : k_finalized τ stake vset parent genesis st b2 h k2)
    (hneq : b1 ≠ b2) :
    q_intersection_slashed τ stake vset st :=
  two_justified_same_height_slashed τ stake vset parent genesis st
    (k_finalized_means_justified τ stake vset parent genesis st hf1)
    (k_finalized_means_justified τ stake vset parent genesis st hf2)
    hneq
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_equal_height_case


/--
# Surround case: full containment

# Statement

$$`\operatorname{justification\_link}(\sigma, s, t, h_s, h_t) \;\wedge\; \operatorname{k\_finalized}(\sigma, b, b_h, k) \;\wedge\; b_h + k < h_t \;\wedge\; h_s < b_h \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

The outer link $`(s, t)` fully contains the finalized chain
$`(b, b_h) \to (b_h + k)` on the height axis: $`h_s < b_h` and
$`b_h + k < h_t`.

# Interpretation

This is the direct manifestation of Casper's slashing condition
(S2): the outer justification link's vote spans
$`[h_s,\, h_t]` and the inner finalization link's vote spans
$`[b_h,\, b_h + k]`, with the strict containment
$`h_s < b_h \le b_h + k < h_t` giving the surround ordering
$`h_{s_{\text{outer}}} < h_{s_{\text{inner}}}` and
$`h_{t_{\text{inner}}} < h_{t_{\text{outer}}}`. Every validator
who voted in both links has cast a surround vote.

# Proof idea

The outer vote is the justification link's supermajority link from
$`(s, h_s)` to $`(t, h_t)`, witnessed by
{lit}`link_supporters` $`(s, t, h_s, h_t)`. The inner vote is the
$`k`-finalization chain's supermajority link from
$`(\mathit{final}, b_h)` to $`(\mathit{ls.getLastD\, final},\, b_h + k)`.
The four heights satisfy
$`h_s < b_h \le b_h + k < h_t` (the surround condition),
and every validator in the intersection of the two quorums has cast
both votes — hence satisfies {lit}`slashed_surround_vote`, wrapped
in {lit}`Or.inr` to inhabit {name}`slashed`.
-/
theorem k_slash_surround_full_containment
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {s t final : Hash}
    {s_h t_h final_h k : Nat}
    (hlink_st : justification_link τ stake vset parent st s t s_h t_h)
    (hfinal : k_finalized τ stake vset parent genesis st final final_h k)
    (h_full : final_h + k < t_h)
    (h_surround_start : s_h < final_h) :
    q_intersection_slashed τ stake vset st :=
  match hlink_st, hfinal with
  | ⟨_, _, hsm_outer⟩, ⟨_, ls, _, _, _, hsm_inner⟩ =>
    match hsm_outer, hsm_inner with
    | ⟨hsm_outer_sub, _⟩, ⟨hsm_inner_sub, _⟩ =>
    ⟨t, ls.getLastD final,
      link_supporters st s t s_h t_h,
      link_supporters st final (ls.getLastD final) final_h (final_h + k),
      hsm_outer_sub, hsm_inner_sub, hsm_outer, hsm_inner,
      fun _ hvO hvI => Or.inr ⟨s, t, s_h, t_h, final, ls.getLastD final,
        final_h, final_h + k,
        mem_link_supporters.mp hvO, mem_link_supporters.mp hvI,
        h_surround_start, h_full⟩⟩
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_slash_surround_full_containment


/--
# Surround case: general

# Statement

$$`\operatorname{justified}(\sigma, s, h_s) \;\wedge\; \operatorname{justification\_link}(\sigma, s, t, h_s, h_t) \;\wedge\; \operatorname{k\_finalized}(\sigma, b, b_h, k) \;\wedge\; b_h < h_t \;\wedge\; \neg\,(b \xrightarrow{*} t) \;\wedge\; h_s < b_h \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Interpretation

Given a justified source $`s` at height $`h_s < b_h`, a
justification link from $`s` to $`t` at height $`h_t > b_h`, a
$`k`-finalized block $`b` at height $`b_h`, and
$`\neg\,(b \xrightarrow{*} t)`, produces a slashing witness.
This generalises {lit}`k_slash_surround_full_containment` to the
case where $`h_t` may equal or fall within the finalization chain's
height range $`[b_h,\, b_h + k]`, not only above it. The three
sub-cases correspond to the three possible positions of $`h_t`
relative to $`b_h + k`.

# Proof idea

First justify $`t` via {lit}`justified_link`. Then case-split on
$`b_h + k` vs $`h_t`:

* $`b_h + k < h_t`: {lit}`k_slash_surround_full_containment`
  produces a surround-vote witness.
* $`b_h + k = h_t`: extract the chain's last block via
  {lit}`k_finalized_last_justified`. If $`t` equals the last block,
  then $`b \xrightarrow{*} t`
  (by {lit}`nth_ancestor_ancestor`), contradicting the non-ancestry
  hypothesis. Otherwise two distinct blocks are justified at height
  $`h_t = b_h + k`, so
  {lit}`two_justified_same_height_slashed` applies.
* $`h_t < b_h + k`: the chain's interior block at index
  $`h_t - b_h` is justified at height $`h_t`
  (from the chain's universal quantifier, transported via
  {lit}`Nat.add_sub_cancel'`). If $`t` equals this block, ancestry
  $`b \xrightarrow{*} t` contradicts the hypothesis; otherwise
  {lit}`two_justified_same_height_slashed` applies.
-/
theorem k_slash_surround_case_general
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {s t final : Hash}
    {s_h t_h final_h k : Nat}
    (hjust_s : justified τ stake vset parent genesis st s s_h)
    (hlink_st : justification_link τ stake vset parent st s t s_h t_h)
    (hfinal : k_finalized τ stake vset parent genesis st final final_h k)
    (hft : final_h < t_h)
    (hnoans : ¬ hash_ancestor parent final t)
    (hsf : s_h < final_h) :
    q_intersection_slashed τ stake vset st :=
  have hjust_t : justified τ stake vset parent genesis st t t_h :=
    justified.justified_link hjust_s hlink_st
  if hlt : final_h + k < t_h then
    k_slash_surround_full_containment
      τ stake vset parent genesis st hlink_st hfinal hlt hsf
  else if heq : final_h + k = t_h then
    match k_finalized_last_justified τ stake vset parent genesis st hfinal with
    | ⟨last, hjust_last, hanc_last, _⟩ =>
      if htlast : t = last then
        False.elim (hnoans (match htlast with | rfl => nth_ancestor_ancestor hanc_last))
      else
        two_justified_same_height_slashed
          τ stake vset parent genesis st hjust_t
          (Eq.subst (motive := fun h => justified τ stake vset parent genesis st last h)
            heq hjust_last) htlast
  else
    have hgt : t_h < final_h + k :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => heq h.symm)
    match hfinal with
    | ⟨_, ls, _, _, hrel, _⟩ =>
      have hhn : final_h + (t_h - final_h) = t_h :=
        Nat.add_sub_cancel' (Nat.le_of_lt hft)
      match hrel (t_h - final_h)
          (Nat.sub_le_of_le_add
            (Eq.subst (motive := fun x => t_h ≤ x)
              (Nat.add_comm final_h k) (Nat.le_of_lt hgt))) with
      | ⟨hj_mid, ha_mid⟩ =>
        have hjust_mid : justified τ stake vset parent genesis st
            (ls.getD (t_h - final_h) final) t_h :=
          Eq.subst (motive := fun h =>
              justified τ stake vset parent genesis st
                (ls.getD (t_h - final_h) final) h)
            hhn hj_mid
        if htm : t = ls.getD (t_h - final_h) final then
          False.elim (hnoans
            (Eq.subst (motive := fun x => hash_ancestor parent final x)
              htm.symm (nth_ancestor_ancestor ha_mid)))
        else
          two_justified_same_height_slashed
            τ stake vset parent genesis st hjust_t hjust_mid htm
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_slash_surround_case_general


/--
# Non-equal-height case: strong induction on the height gap

# Statement

$$`\operatorname{justified}(\sigma, b_1, b_{1,h}) \;\wedge\; \operatorname{k\_finalized}(\sigma, b_2, b_{2,h}, k) \;\wedge\; \neg\,(b_2 \xrightarrow{*} b_1) \;\wedge\; b_{2,h} < b_{1,h} \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Interpretation

This is the inductive core of the safety argument: given a
justified block $`b_1` strictly above a $`k`-finalized block
$`b_2` that is *not* its ancestor, trace $`b_1`'s justification
chain downward toward $`b_2`. At each step the predecessor's
height is strictly smaller (since justification links are
forward), so the gap $`b_{1,h} - b_{2,h}` strictly decreases.
The descent terminates in one of two base cases: if the
predecessor's height equals $`b_{2,h}`, the equal-height case
(S1) applies; if it falls below $`b_{2,h}`, the surround case
(S2) applies. The argument mirrors the "walking backwards along
supermajority links" in Gasper's proof of Lemma 5.1.

# Proof idea

Strong induction on the gap $`b_{1,h} - b_{2,h}` via
{lit}`strong_induction_sub` (offset $`k = b_{2,h}`). Case-split
$`b_1`'s justification via {lit}`justified_cases`:

* *Genesis*: height $`0 < b_{2,h}` is impossible.
* *Link from $`(s, h_s)`*: the non-ancestry of $`b_2` propagates to
  $`s` via {lit}`hash_ancestor_conflict`. Then:
  * if $`h_s > b_{2,h}`: the gap $`h_s - b_{2,h} < b_{1,h} - b_{2,h}`
    and the induction hypothesis applies to $`s`;
  * if $`h_s = b_{2,h}`: {lit}`two_justified_same_height_slashed`
    on $`s` and $`b_2`;
  * if $`h_s < b_{2,h}`: {lit}`k_slash_surround_case_general` on
    the link $`(s, b_1)` and the finalized $`b_2`.
-/
theorem k_non_equal_height_case_ind
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b1 b2 : Hash}
    {b1_h b2_h k : Nat}
    (hb1j : justified τ stake vset parent genesis st b1 b1_h)
    (hb2f : k_finalized τ stake vset parent genesis st b2 b2_h k)
    (hconf : ¬ hash_ancestor parent b2 b1)
    (hh : b2_h < b1_h) :
    q_intersection_slashed τ stake vset st :=
  (strong_induction_sub
    (P := fun h1_h (h1 : Hash) =>
      justified τ stake vset parent genesis st h1 h1_h →
      k_finalized τ stake vset parent genesis st b2 b2_h k →
      ¬ hash_ancestor parent b2 h1 →
      b2_h < h1_h →
      q_intersection_slashed τ stake vset st)
    (fun _ _ IH hj1 hb2f' hconf1 hh1 =>
      (justified_cases τ stake vset parent genesis st hj1).elim
        (fun ⟨_, hh_zero⟩ =>
          False.elim ((Nat.not_lt_zero _) (match hh_zero with | rfl => hh1)))
        (fun ⟨s, s_h, hsj, hlink⟩ =>
          match hlink with
          | ⟨hlink_lt, hlink_nth, _⟩ =>
          have hconf_s : ¬ hash_ancestor parent b2 s :=
            hash_ancestor_conflict (nth_ancestor_ancestor hlink_nth) hconf1
          if hlt : b2_h < s_h then
            IH s_h s hlt
              (Nat.sub_lt_sub_right (Nat.le_of_lt hlt) hlink_lt)
              hsj hb2f' hconf_s hlt
          else if heq : b2_h = s_h then
            two_justified_same_height_slashed
              τ stake vset parent genesis st hsj
              (Eq.subst (motive := fun h => justified τ stake vset parent genesis st b2 h)
                heq (k_finalized_means_justified τ stake vset parent genesis st hb2f'))
              (fun hs =>
                False.elim (hconf_s
                  (Eq.subst (motive := fun x => hash_ancestor parent x s)
                    hs (hash_ancestor.refl (parent := parent) s))))
          else
            k_slash_surround_case_general
              τ stake vset parent genesis st hsj hlink hb2f'
              hh1 hconf1
              (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => heq h.symm)))))
    b1_h b1 hb1j hb2f hconf hh
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_non_equal_height_case_ind


/--
# Non-equal-height case: lifting from justified to $`k`-finalized

# Statement

$$`\operatorname{k\_finalized}(\sigma, b_1, b_{1,h}, k_1) \;\wedge\; \operatorname{k\_finalized}(\sigma, b_2, b_{2,h}, k_2) \;\wedge\; \neg\,(b_2 \xrightarrow{*} b_1) \;\wedge\; b_{2,h} < b_{1,h} \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Interpretation

The version of the non-equal-height case where *both* blocks are
$`k`-finalized (not merely justified). The asymmetry in the
height condition $`b_{2,h} < b_{1,h}` is absorbed by {lit}`k_safety'`,
which handles the symmetric case by swapping the two blocks.

# Proof idea

Extract $`b_1`'s justification from its $`k`-finalization via
{lit}`k_finalized_means_justified`, then delegate to
{lit}`k_non_equal_height_case_ind` with the justified $`b_1` and
the $`k`-finalized $`b_2`.

# Role in the development

The $`b_{2,h} < b_{1,h}` and $`b_{1,h} < b_{2,h}` branches of
{lit}`k_safety'` both route through this lemma (the latter after
swapping $`b_1 \leftrightarrow b_2`).
-/
theorem k_non_equal_height_case
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b1 b2 : Hash}
    {b1_h b2_h k1 k2 : Nat}
    (hb1f : k_finalized τ stake vset parent genesis st b1 b1_h k1)
    (hb2f : k_finalized τ stake vset parent genesis st b2 b2_h k2)
    (hconf : ¬ hash_ancestor parent b2 b1)
    (hh : b2_h < b1_h) :
    q_intersection_slashed τ stake vset st :=
  k_non_equal_height_case_ind τ stake vset parent genesis st
    (k_finalized_means_justified τ stake vset parent genesis st hb1f)
    hb2f hconf hh
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_non_equal_height_case


/--
# $`k`-safety: two $`k`-finalized mutual non-ancestors force slashing

# Statement

$$`\operatorname{k\_finalized}(\sigma, b_1, b_{1,h}, k_1) \;\wedge\; \operatorname{k\_finalized}(\sigma, b_2, b_{2,h}, k_2) \;\wedge\; \neg\,(b_2 \xrightarrow{*} b_1) \;\wedge\; \neg\,(b_1 \xrightarrow{*} b_2) \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Assumptions

* two $`k`-finalized blocks $`(b_1, b_{1,h}, k_1)` and
  $`(b_2, b_{2,h}, k_2)` in the same state $`\sigma`;
* mutual non-ancestry: $`\neg\,(b_2 \xrightarrow{*} b_1)` and
  $`\neg\,(b_1 \xrightarrow{*} b_2)`.

No {lit}`good_votes`, no {name}`QuorumContext` — the justification
derivations carried by the $`k`-finalized hypotheses already encode
the required supermajority links.

# Proof idea

Three-way case split on $`b_{1,h}` vs $`b_{2,h}`:

* $`b_{1,h} = b_{2,h}`: transport $`b_2`'s finalization to height
  $`b_{1,h}` via {lit}`Eq.subst`, derive $`b_1 \ne b_2` from
  $`\neg\,(b_1 \xrightarrow{*} b_2)` via
  {lit}`hash_nonancestor_nonequal`, then apply
  {lit}`k_equal_height_case`.
* $`b_{2,h} < b_{1,h}`: {lit}`k_non_equal_height_case`.
* $`b_{1,h} < b_{2,h}`: symmetric application of
  {lit}`k_non_equal_height_case` with the two blocks swapped.

# Role in the development

The core of the safety proof, consumed by
{lit}`k_accountable_safety` and ultimately by
{lit}`accountable_safety`.
-/
theorem k_safety'
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b1 b2 : Hash}
    {b1_h b2_h k1 k2 : Nat}
    (hb1f : k_finalized τ stake vset parent genesis st b1 b1_h k1)
    (hb2f : k_finalized τ stake vset parent genesis st b2 b2_h k2)
    (hconf1 : ¬ hash_ancestor parent b2 b1)
    (hconf2 : ¬ hash_ancestor parent b1 b2) :
    q_intersection_slashed τ stake vset st :=
  if heq : b1_h = b2_h then
    k_equal_height_case τ stake vset parent genesis st
      hb1f
      (Eq.subst (motive := fun h => k_finalized τ stake vset parent genesis st b2 h k2)
        heq.symm hb2f)
      (hash_nonancestor_nonequal hconf2)
  else if hgt : b2_h < b1_h then
    k_non_equal_height_case τ stake vset parent genesis st
      hb1f hb2f hconf1 hgt
  else
    k_non_equal_height_case τ stake vset parent genesis st
      hb2f hb1f hconf2 (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hgt) heq)
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_safety'


/--
# $`k`-accountable safety

# Statement

$$`\operatorname{k\_finalization\_fork}(\sigma, k_1, k_2) \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Interpretation

The existential wrapper around {lit}`k_safety'`: given a
$`k`-finalization fork (two $`k`-finalized blocks with mutual
non-ancestry, packed as an existential), produces the slashing
witness. This converts the bundled fork into the unbundled
hypotheses that {lit}`k_safety'` consumes.

# Proof idea

Destruct the fork existential to obtain the two blocks
$`b_1, b_2`, their heights $`b_{1,h}, b_{2,h}`, the two
$`k`-finalization hypotheses, and the mutual non-ancestry
conditions. Pass all six components directly to {lit}`k_safety'`.
-/
theorem k_accountable_safety
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {k1 k2 : Nat}
    (hfork : k_finalization_fork τ stake vset parent genesis st k1 k2) :
    q_intersection_slashed τ stake vset st :=
  match hfork with
  | ⟨_, _, _, _, hb1f, hb2f, hc1, hc2⟩ =>
    k_safety' τ stake vset parent genesis st hb1f hb2f hc1 hc2
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode k_accountable_safety


/--
# Accountable safety (main theorem)

# Statement

$$`\operatorname{finalization\_fork}(\sigma) \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Interpretation

The formal counterpart of Casper FFG's Theorem 1 (Accountable
Safety): if two conflicting blocks are both finalized — i.e. the
protocol has committed to two incompatible histories — then there
exist two $`\frac{2}{3}`-quorums whose shared members have all
violated a slashing condition and can therefore be held
*accountable* (their deposits destroyed). The word "accountable"
is the key: the theorem does not merely assert that honest
validators would not create a fork, but that *if* a fork occurs,
provable evidence exists to identify and punish the responsible
validators.

# Proof idea

Convert the {lit}`finalization_fork` to a
{lit}`same_k_finalization_fork` at $`k = 1` via
{lit}`finalization_fork_means_same_finalization_fork_one`, then
apply {lit}`k_accountable_safety`.

# Assumptions

Only the fork hypothesis {lit}`hfork` — no {lit}`good_votes`,
no {lit}`QuorumContext`, no block-tree axioms beyond those already
encoded in the justification derivations that the fork carries.

# Non-assumptions

This theorem does *not* assert that the slashed intersection is
nonempty (that is the quantitative half in
{lit}`Theories/SlashableBound.lean`). It asserts that *every*
validator in the intersection is slashed.
-/
theorem accountable_safety
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (hfork : finalization_fork τ stake vset parent genesis st) :
    q_intersection_slashed τ stake vset st :=
  k_accountable_safety τ stake vset parent genesis st
    ((finalization_fork_means_same_finalization_fork_one
      τ stake vset parent genesis st).mp hfork)
set_option pp.proofs true in
set_option pp.notation false in
set_option pp.fieldNotation false in
set_option pp.proofs.withType true in
#explode accountable_safety


end GasperBeaconChain.Core
