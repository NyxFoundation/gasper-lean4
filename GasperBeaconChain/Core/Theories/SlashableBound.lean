import GasperBeaconChain.Core.Theories.AccountableSafety
import GasperBeaconChain.Core.Lemmas.Weight
import GasperBeaconChain.Core.Lemmas.SetTheoryProps
import GasperBeaconChain.Core.DetailExplode

universe u v

namespace GasperBeaconChain.Core

/-!
# Slashable bound

This file proves the **quantitative** half of accountable safety:
the weight of the slashable quorum intersection is lower-bounded by
a churn-adjusted expression involving the validator-set overlap and
the one-third residuals. Combined with the *structural* half
({lit}`Theories/AccountableSafety.lean`), this yields the full
Gasper accountable-safety guarantee with dynamic validator sets.

The main theorem {lit}`slashable_bound` formalises Gasper's
Theorem 8.3 (dynamic-validator-set safety bound): given two
conflicting $`k`-finalized blocks and a reference validator set
$`V_0`, the weight of the slashable quorum intersection is at
least

$$`\max\bigl(\operatorname{wt}(V_L) - a_L - e_R,\;\operatorname{wt}(V_R) - a_R - e_L\bigr) - f_{1/3}(\operatorname{wt}(V_L)) - f_{1/3}(\operatorname{wt}(V_R))`

where $`a_L, a_R` are activation weights and $`e_L, e_R` are exit
weights relative to $`V_0`. When $`V_L = V_R = V_0` (no churn),
the bound specialises to $`\operatorname{wt}(V) - 2\,f_{1/3}(\operatorname{wt}(V))`,
recovering the static Casper FFG overlap.

## Validator-set churn

Four functions capture validator churn between a reference set
$`V_0` and a branch set $`V`:

* {lit}`activated` $`= V \setminus V_0` (validators that entered)
* {lit}`exited` $`= V_0 \setminus V` (validators that left)
* {lit}`actwt`, {lit}`extwt` — their weights

## Derivation chain

The proof builds in two independent pipelines that merge in
{lit}`slashable_bound`:

1. **Quorum overlap** (purely weight-algebraic, no block tree):

   {lit}`wt_meet_bound_fUnion` $`\to`
   {lit}`wt_meet_subbound_fUnion` $`\to`
   {lit}`wt_quorum_union_bound_fUnion` $`\to`
   {lit}`quorum_intersection_weight_lower`

2. **Churn bound** (Venn-diagram geometry on three sets):

   {lit}`wt_meet_tri_bound_fDiff` $`\to`
   {lit}`validator_intersection_lower_bound`

The merger in {lit}`slashable_bound` invokes {lit}`k_safety'`
to obtain the structural witness, then chains the two pipelines
by truncated-subtraction monotonicity.

## Non-goals of this file

This file does *not* prove that the displayed lower bound is
strictly positive — that depends on the concrete threshold instance
and the magnitude of churn (see the appendix of
{lit}`Lemmas/AccountableSafety.lean`).
-/

variable {Validator : Type u}
variable [DecidableEq Validator]

/--
# Activated validators

Validators present in $`s_2` but absent from $`s_1`:
$`\operatorname{activated}(s_1, s_2) = \operatorname{fDiff}(s_2, s_1) = s_2 \setminus s_1`.
The first argument $`s_1` is the reference set, the second $`s_2`
the branch set; the result is the set that **entered** between them.
-/
def activated (s1 s2 : Finset Validator) : Finset Validator :=
  fDiff s2 s1

/--
# Exited validators

Validators present in $`s_1` but absent from $`s_2`:
$`\operatorname{exited}(s_1, s_2) = \operatorname{fDiff}(s_1, s_2) = s_1 \setminus s_2`.
The first argument $`s_1` is the reference set, the second $`s_2`
the branch set; the result is the set that **left** between them.
-/
def exited (s1 s2 : Finset Validator) : Finset Validator :=
  fDiff s1 s2

/-- Weight of the activated validators: $`\operatorname{wt}(\operatorname{activated}(s_1, s_2))`. -/
def actwt (stake : Validator → Nat) (s1 s2 : Finset Validator) : Nat :=
  wt stake (activated s1 s2)

/-- Weight of the exited validators: $`\operatorname{wt}(\operatorname{exited}(s_1, s_2))`. -/
def extwt (stake : Validator → Nat) (s1 s2 : Finset Validator) : Nat :=
  wt stake (exited s1 s2)


/--
# Nested-intersection weight bound via inclusion–exclusion

$$`\operatorname{wt}(s_1 \cap s_2) + \operatorname{wt}(s_1' \cap s_2') \;\ge\; \operatorname{wt}(s_1 \cap (s_1' \cap s_2')) + \operatorname{wt}(s_2 \cap (s_1' \cap s_2'))`

# Assumptions

$`s_1 \subseteq s_1'` and $`s_2 \subseteq s_2'` — quorum–set
inclusion hypotheses.

# Interpretation

Each quorum's share of the validator-set intersection, when summed,
is bounded by the sum of the quorum–quorum intersection and the
validator–validator intersection. This is the first step in the
derivation chain toward the slashable bound.

# Proof idea

Apply {lit}`wt_add_inter_fUnion` to the two crossed terms
$`s_1 \cap (s_1' \cap s_2')` and $`s_2 \cap (s_1' \cap s_2')`,
yielding their weight sum as a union weight plus an intersection
weight. Then:

* *Union bound*: the union
  $`\operatorname{fUnion}(s_1 \cap (s_1' \cap s_2'),\, s_2 \cap (s_1' \cap s_2'))`
  is a subset of $`s_1' \cap s_2'` (each element comes from a
  crossed term whose second factor is $`s_1' \cap s_2'`), so
  {lit}`wt_inc_leq` gives
  $`\operatorname{wt}(\text{union}) \le \operatorname{wt}(s_1' \cap s_2')`.

* *Intersection simplification*: the intersection of the two
  crossed terms simplifies to $`s_1 \cap s_2` ({lit}`hIeq`, proved
  by {name}`Finset.ext` — the $`s_1' \cap s_2'` factors cancel
  because $`s_1 \subseteq s_1'` and $`s_2 \subseteq s_2'` make
  them redundant when both are present). This replaces the
  intersection weight with $`\operatorname{wt}(s_1 \cap s_2)`.

Combining and commuting gives the conclusion.
-/
theorem wt_meet_bound_fUnion
    (stake : Validator → Nat)
    (s1 s2 s1' s2' : Finset Validator)
    (hs1 : s1 ⊆ s1')
    (hs2 : s2 ⊆ s2') :
    wt stake (s1 ∩ s2) + wt stake (s1' ∩ s2')
      ≥
    wt stake (s1 ∩ (s1' ∩ s2'))
      +
    wt stake (s2 ∩ (s1' ∩ s2')) :=
  have hAdd : wt stake (s1 ∩ (s1' ∩ s2')) + wt stake (s2 ∩ (s1' ∩ s2')) =
      wt stake (fUnion (s1 ∩ (s1' ∩ s2')) (s2 ∩ (s1' ∩ s2'))) +
      wt stake ((s1 ∩ (s1' ∩ s2')) ∩ (s2 ∩ (s1' ∩ s2'))) :=
    wt_add_inter_fUnion stake (s1 ∩ (s1' ∩ s2')) (s2 ∩ (s1' ∩ s2'))
  have hUle : wt stake (fUnion (s1 ∩ (s1' ∩ s2')) (s2 ∩ (s1' ∩ s2')))
      ≤ wt stake (s1' ∩ s2') :=
    wt_inc_leq stake (fun _ hx => (mem_fUnion.mp hx).elim
      (fun hxA => match Finset.mem_inter.mp hxA with | ⟨_, h⟩ => h)
      (fun hxB => match Finset.mem_inter.mp hxB with | ⟨_, h⟩ => h))
  have hIeq : (s1 ∩ (s1' ∩ s2')) ∩ (s2 ∩ (s1' ∩ s2')) = s1 ∩ s2 :=
    Finset.ext fun _ =>
      ⟨fun hx =>
        match Finset.mem_inter.mp hx with
        | ⟨hxA, hxB⟩ =>
          Finset.mem_inter.mpr
            ⟨match Finset.mem_inter.mp hxA with | ⟨h, _⟩ => h,
             match Finset.mem_inter.mp hxB with | ⟨h, _⟩ => h⟩,
       fun hx =>
        match Finset.mem_inter.mp hx with
        | ⟨h1, h2⟩ =>
          Finset.mem_inter.mpr
            ⟨Finset.mem_inter.mpr ⟨h1, Finset.mem_inter.mpr ⟨hs1 h1, hs2 h2⟩⟩,
             Finset.mem_inter.mpr ⟨h2, Finset.mem_inter.mpr ⟨hs1 h1, hs2 h2⟩⟩⟩⟩
  hAdd.le.trans
    ((Nat.add_le_add_right hUle _).trans
      (Nat.le_of_eq
        ((congrArg (wt stake (s1' ∩ s2') + wt stake ·) hIeq).trans
          (Nat.add_comm (wt stake (s1' ∩ s2')) (wt stake (s1 ∩ s2))))))
#detail_explode wt_meet_bound_fUnion


/--
# A quorum's share of the validator-set intersection

# Statement

$$`\operatorname{wt}(s_1 \cap (s_1' \cap s_2')) + \operatorname{wt}(\operatorname{fDiff}(s_1', s_2')) \;\ge\; \operatorname{wt}(s_1)`

# Interpretation

Each quorum $`s_1` can be split, relative to the validator-set
intersection $`s_1' \cap s_2'`, into a part that lies *inside* the
intersection and a part that lies in the *difference*
$`s_1' \setminus s_2'`. Their combined weight is at least
$`\operatorname{wt}(s_1)`, giving a lower bound on how much of
$`s_1`'s weight is accounted for by these two regions.

# Proof idea

Every element of $`s_1 \subseteq s_1'` either lies in
$`s_1' \cap s_2'` (and hence in $`s_1 \cap (s_1' \cap s_2')`) or
in $`s_1' \setminus s_2'`. The two parts are disjoint
({lit}`disjointMF`): an element of $`s_1 \cap (s_1' \cap s_2')`
has its second factor in $`s_1' \cap s_2'`, whereas every
element of $`\operatorname{fDiff}(s_1', s_2')` lies outside
$`s_2'`, so no element can belong to both. The subset inclusion

$$`s_1 \;\subseteq\; \operatorname{fUnion}\bigl(s_1 \cap (s_1' \cap s_2'),\;\operatorname{fDiff}(s_1', s_2')\bigr)`

then gives
$`\operatorname{wt}(s_1) \le \operatorname{wt}(\operatorname{fUnion}(\ldots))`
by {lit}`wt_inc_leq`, and disjointness expands the right side
to the plain sum by {lit}`wt_fUnion_of_disjointMF`.

# Role in the development

Supplies the per-quorum weight bound consumed by
{lit}`wt_meet_bound_fUnion` (which sums two such bounds) and
ultimately by {lit}`quorum_intersection_weight_lower`.
-/
theorem wt_meet_subbound_fUnion
    (stake : Validator → Nat)
    (s1 s1' s2' : Finset Validator)
    (hs1 : s1 ⊆ s1') :
    wt stake (s1 ∩ (s1' ∩ s2')) + wt stake (fDiff s1' s2')
      ≥
    wt stake s1 :=
  have hsub : s1 ⊆ fUnion (s1 ∩ (s1' ∩ s2')) (fDiff s1' s2') :=
    fun _ hx =>
      if hx2 : _ ∈ s2'
      then mem_fUnion_left (Finset.mem_inter.mpr
        ⟨hx, Finset.mem_inter.mpr ⟨hs1 hx, hx2⟩⟩)
      else mem_fUnion_right (mem_fDiff_of_mem_of_not_mem (hs1 hx) hx2)
  have hdisMF : disjointMF (s1 ∩ (s1' ∩ s2')).val (fDiff s1' s2').val :=
    fun x hxA hxB =>
      (not_mem_right_of_mem_fDiff (show x ∈ fDiff s1' s2' from hxB))
        ((Finset.mem_inter.mp
          (Finset.mem_inter.mp (show x ∈ s1 ∩ (s1' ∩ s2') from hxA)).2).2)
  (wt_inc_leq stake hsub).trans (Nat.le_of_eq (wt_fUnion_of_disjointMF stake hdisMF))
#detail_explode wt_meet_subbound_fUnion


/--
# Triangle bound on difference weights

$$`\operatorname{wt}(\operatorname{fDiff}(s_1, s_2)) \;\le\; \operatorname{wt}(\operatorname{fDiff}(s_0, s_2)) + \operatorname{wt}(\operatorname{fDiff}(s_1, s_0))`

The weight of $`s_1 \setminus s_2` is bounded by the sum of the
weights of $`s_0 \setminus s_2` and $`s_1 \setminus s_0`.

# Proof idea

{lit}`fDiff_subset_triangle` gives the set-level containment
$`s_1 \setminus s_2 \subseteq \operatorname{fUnion}(s_0 \setminus s_2,\, s_1 \setminus s_0)`.
Weighing via {lit}`wt_inc_leq` gives
$`\operatorname{wt}(s_1 \setminus s_2) \le \operatorname{wt}(\operatorname{fUnion}(\ldots))`.
{lit}`wt_fUnion` expands the right side to
$`\operatorname{wt}(s_0 \setminus s_2) + \operatorname{wt}(\operatorname{fDiff}(\operatorname{fDiff}(s_1, s_0),\, \operatorname{fDiff}(s_0, s_2)))`,
and the inner {lit}`fDiff` is idempotent (an element of
$`s_1 \setminus s_0` cannot also lie in $`s_0 \setminus s_2`,
since the latter requires $`\in s_0`), so the auxiliary fact
{lit}`hfdf` simplifies the sum to
$`\operatorname{wt}(s_0 \setminus s_2) + \operatorname{wt}(s_1 \setminus s_0)`.
-/
theorem wt_meet_tri_bound_fDiff
    (stake : Validator → Nat)
    (s0 s1 s2 : Finset Validator) :
    wt stake (fDiff s1 s2)
      ≤
    wt stake (fDiff s0 s2) + wt stake (fDiff s1 s0) :=
  have hfdf : fDiff (fDiff s1 s0) (fDiff s0 s2) = fDiff s1 s0 :=
    Finset.ext fun _ =>
      ⟨fun hx => mem_left_of_mem_fDiff hx,
       fun hx => mem_fDiff_of_mem_of_not_mem hx
         (fun hxfD => (not_mem_right_of_mem_fDiff hx) (mem_left_of_mem_fDiff hxfD))⟩
  (wt_inc_leq stake (fDiff_subset_triangle s0 s1 s2)).trans
    (Nat.le_of_eq ((wt_fUnion stake (fDiff s0 s2) (fDiff s1 s0)).trans
      (congrArg (wt stake (fDiff s0 s2) + wt stake ·) hfdf)))
#detail_explode wt_meet_tri_bound_fDiff


/--
# Quorum sum bounded by overlap plus union

# Statement

$$`\operatorname{wt}(q_L) + \operatorname{wt}(q_R) \;\le\; \operatorname{wt}(q_L \cap q_R) + \operatorname{wt}(\operatorname{fUnion}(V_L, V_R))`

# Interpretation

The total weight of two quorums exceeds their intersection weight
by at most the weight of the union of the two validator sets. This
is the quorum-level restatement of inclusion–exclusion: the
"double-counted" part is $`\operatorname{wt}(q_L \cap q_R)`, and
the "universe" that bounds the remainder is
$`\operatorname{fUnion}(V_L, V_R)`.

# Proof idea

Apply {lit}`wt_add_inter_fUnion` to the quorums themselves:

$$`\operatorname{wt}(q_L) + \operatorname{wt}(q_R) = \operatorname{wt}(\operatorname{fUnion}(q_L, q_R)) + \operatorname{wt}(q_L \cap q_R)`

Then bound $`\operatorname{wt}(\operatorname{fUnion}(q_L, q_R))`
by $`\operatorname{wt}(\operatorname{fUnion}(V_L, V_R))` via
{lit}`wt_inc_leq` composed with {lit}`fUnion_subset` (using
$`q_L \subseteq V_L` and $`q_R \subseteq V_R`). Commuting the sum
gives the conclusion.

# Assumptions

* $`q_L \subseteq V_L` — quorum–set inclusion {lit}`hqLsub`;
* $`q_R \subseteq V_R` — quorum–set inclusion {lit}`hqRsub`.

# Role in the development

The quorum-level inclusion–exclusion step that feeds
{lit}`quorum_intersection_weight_lower`: it combines the two
quorum thresholds with the union weight to lower-bound the
quorum intersection.
-/
theorem wt_quorum_union_bound_fUnion
    (stake : Validator → Nat)
    {qL qR vL vR : Finset Validator}
    (hqLsub : qL ⊆ vL)
    (hqRsub : qR ⊆ vR) :
    wt stake qL + wt stake qR
      ≤
    wt stake (qL ∩ qR) + wt stake (fUnion vL vR) :=
  have hUle : wt stake (fUnion qL qR) ≤ wt stake (fUnion vL vR) :=
    wt_inc_leq stake (fUnion_subset
      (fun _ hx => mem_fUnion_left (hqLsub hx))
      (fun _ hx => mem_fUnion_right (hqRsub hx)))
  have hAdd : wt stake qL + wt stake qR =
      wt stake (fUnion qL qR) + wt stake (qL ∩ qR) :=
    wt_add_inter_fUnion stake qL qR
  hAdd.le.trans
    ((Nat.le_of_eq (Nat.add_comm (wt stake (fUnion qL qR)) (wt stake (qL ∩ qR)))).trans
      (Nat.add_le_add_left hUle _))
#detail_explode wt_quorum_union_bound_fUnion


/--
# Quorum-intersection weight lower bound

# Statement

$$`\operatorname{wt}(V_L \cap V_R) - f_{1/3}(\operatorname{wt}(V_L)) - f_{1/3}(\operatorname{wt}(V_R)) \;\le\; \operatorname{wt}(q_L \cap q_R)`

# Interpretation

The weight of the quorum intersection $`q_L \cap q_R` — the set
whose members are all slashed by the structural half — is at least
the validator-set overlap $`\operatorname{wt}(V_L \cap V_R)` minus
the two one-third residuals. This is the quantitative core of the
pigeonhole argument: two $`\frac{2}{3}`-quorums drawn from
overlapping validator sets must share a substantial portion. In
the static case $`V_L = V_R = V` this reduces to
$`\operatorname{wt}(V) - 2\,f_{1/3}(\operatorname{wt}(V)) \le \operatorname{wt}(q_L \cap q_R)`,
the classic $`\frac{1}{3}`-overlap bound.

# Assumptions

* $`q_L \subseteq V_L`, $`q_R \subseteq V_R` — quorum–set inclusion;
* $`f_{2/3}(\operatorname{wt}(V_L)) \le \operatorname{wt}(q_L)`,
  $`f_{2/3}(\operatorname{wt}(V_R)) \le \operatorname{wt}(q_R)` — the
  quorum weight conditions.

# Proof idea

Instantiate the pure-arithmetic kernel
{lit}`nat_quorum_intersection_arith` with:
* $`A + B = U + I` ← {lit}`wt_add_inter_fUnion` on $`V_L, V_R`;
* $`A = O_L + T_L`, $`B = O_R + T_R` ←
  {lit}`threshold_decomposition` on each set's weight;
* $`T_L + T_R \le Q + U` ←
  {lit}`wt_quorum_union_bound_fUnion` composed with the quorum
  weight hypotheses.

# Non-assumptions

The two validator sets $`V_L, V_R` need not be equal — this is the
dynamic-validator-set reading. When they coincide the bound
specialises to the static Casper FFG form.
-/
theorem quorum_intersection_weight_lower
    (τ : Threshold)
    (stake : Validator → Nat)
    {qL qR vL vR : Finset Validator}
    (hqLsub : qL ⊆ vL)
    (hqRsub : qR ⊆ vR)
    (hqLwt : τ.two_third (wt stake vL) ≤ wt stake qL)
    (hqRwt : τ.two_third (wt stake vR) ≤ wt stake qR) :
    wt stake (vL ∩ vR)
      - τ.one_third (wt stake vL)
      - τ.one_third (wt stake vR)
      ≤
    wt stake (qL ∩ qR) :=
  nat_quorum_intersection_arith
    (wt_add_inter_fUnion stake vL vR)
    (threshold_decomposition τ (wt stake vL))
    (threshold_decomposition τ (wt stake vR))
    (le_trans (Nat.add_le_add hqLwt hqRwt)
      (wt_quorum_union_bound_fUnion stake hqLsub hqRsub))
#detail_explode quorum_intersection_weight_lower


/--
# Venn-diagram bound on validator-set overlap

# Statement

$$`\max\bigl(\operatorname{wt}(V_L) - a_L - e_R,\; \operatorname{wt}(V_R) - a_R - e_L\bigr) \;\le\; \operatorname{wt}(V_L \cap V_R)`

where $`a_L = \operatorname{actwt}(V_0, V_L)`,
$`e_R = \operatorname{extwt}(V_0, V_R)`, etc.

# Interpretation

The overlap $`V_L \cap V_R` of two branch validator sets is
lower-bounded by the weight of each branch minus the churn relative
to a reference set $`V_0`. The two branches of the $`\max` give
two independent lower bounds — one from the $`V_L` perspective
(subtracting $`V_L`'s activations and $`V_R`'s exits) and one
from $`V_R`'s — and the $`\max` selects the tighter one. This
captures the Venn-diagram geometry of three overlapping sets
$`V_0, V_L, V_R`: the part of $`V_L` that survives in $`V_R` is
at least $`V_L` minus the validators that entered $`V_L` after
$`V_0` (who were never in $`V_0 \cap V_R`) and the validators
that left $`V_0` before reaching $`V_R`.

# Proof idea

Each branch of {lit}`max_le` follows the same pattern:
{lit}`wt_fDiff` rewrites
$`\operatorname{wt}(V_L) - \operatorname{wt}(V_L \cap V_R)` as
$`\operatorname{wt}(\operatorname{fDiff}(V_L, V_R))`, then
{lit}`wt_meet_tri_bound_fDiff` bounds that difference by
$`\operatorname{wt}(\operatorname{fDiff}(V_0, V_R)) + \operatorname{wt}(\operatorname{fDiff}(V_L, V_0))`,
which unfold to $`e_R + a_L`. The helper
{lit}`nat_sub_sub_le_of_sub_le_add` converts this additive bound
into the displayed truncated-subtraction form. The second branch
is symmetric, with {lit}`inter_commF` swapping $`V_L \cap V_R` to
$`V_R \cap V_L`.

# Role in the development

The churn-pipeline terminus: feeds into {lit}`slashable_bound` as
the lower bound on
$`\operatorname{wt}(V_L \cap V_R)`, which is then chained with
{lit}`quorum_intersection_weight_lower` (the quorum-pipeline
terminus) via truncated-subtraction monotonicity.
-/
theorem validator_intersection_lower_bound
    (stake : Validator → Nat)
    (v0 vL vR : Finset Validator) :
    max
      (wt stake vL - actwt stake v0 vL - extwt stake v0 vR)
      (wt stake vR - actwt stake v0 vR - extwt stake v0 vL)
      ≤
    wt stake (vL ∩ vR) :=
  max_le
    (nat_sub_sub_le_of_sub_le_add
      ((Nat.le_of_eq (wt_fDiff stake vL vR).symm).trans
        (wt_meet_tri_bound_fDiff stake v0 vL vR)))
    (nat_sub_sub_le_of_sub_le_add
      ((Nat.le_of_eq ((congrArg (wt stake vR - wt stake ·) (inter_commF vR vL).symm).trans
        (wt_fDiff stake vR vL).symm)).trans
        (wt_meet_tri_bound_fDiff stake v0 vR vL)))
#detail_explode validator_intersection_lower_bound


variable {Hash : Type v}
variable [DecidableEq Hash]
variable [Fintype Validator]


/--
# Slashable bound (main theorem)

A finalization fork produces a quorum pair whose intersection has
weight at least the churn-adjusted bound:

$$`\max(\operatorname{wt}(V_L) - a_L - e_R,\; \operatorname{wt}(V_R) - a_R - e_L) - f_{1/3}(\operatorname{wt}(V_L)) - f_{1/3}(\operatorname{wt}(V_R)) \;\le\; \operatorname{wt}(q_L \cap q_R)`

# Proof idea

Apply {lit}`k_safety'` to the two $`k`-finalized blocks and
their mutual non-ancestry hypotheses. This produces the
{lit}`q_intersection_slashed` witness — a 9-tuple
$`(b_L, b_R, q_L, q_R, \text{subset}_L, \text{subset}_R, \text{quorum}_L, \text{quorum}_R, \text{slashing})` — from
which the first eight components are retained and the ninth
(the universal slashing quantifier over the intersection) is
discarded (written {lit}`_` in the match), since the quantitative
bound does not need the slashing itself.

With the two quorums in hand, compose two inequalities by
truncated-subtraction monotonicity ({lit}`Nat.sub_le_sub_right`):

1. {lit}`validator_intersection_lower_bound` — bounds
   $`\operatorname{wt}(V_L \cap V_R)` from below by the churn
   expression $`\max(\operatorname{wt}(V_L) - a_L - e_R,\; \operatorname{wt}(V_R) - a_R - e_L)`;
2. {lit}`quorum_intersection_weight_lower` — bounds
   $`\operatorname{wt}(q_L \cap q_R)` from below by
   $`\operatorname{wt}(V_L \cap V_R) - f_{1/3}(\operatorname{wt}(V_L)) - f_{1/3}(\operatorname{wt}(V_R))`.

The transitivity of $`\le` under iterated truncated subtraction
chains the two bounds into the displayed conclusion.

# Assumptions

Two $`k`-finalized blocks with mutual non-ancestry, plus a
reference block $`b_0` from which the churn is measured.

# Non-assumptions

The theorem does *not* assert the intersection is nonempty; whether
the displayed lower bound is strictly positive depends on the
concrete threshold instance and the magnitude of churn (see the
appendix of {lit}`Lemmas/AccountableSafety.lean`).
-/
theorem slashable_bound
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (b0 b1 b2 : Hash)
    (b1_h b2_h k1 k2 : Nat)
    (hb1f : k_finalized τ stake vset parent genesis st b1 b1_h k1)
    (hb2f : k_finalized τ stake vset parent genesis st b2 b2_h k2)
    (hconf12 : ¬ hash_ancestor parent b1 b2)
    (hconf21 : ¬ hash_ancestor parent b2 b1) :
    ∃ bL bR : Hash,
    ∃ qL qR : Finset Validator,
      qL ⊆ vset bL ∧
      qR ⊆ vset bR ∧
      max
        (wt stake (vset bL) - actwt stake (vset b0) (vset bL) - extwt stake (vset b0) (vset bR))
        (wt stake (vset bR) - actwt stake (vset b0) (vset bR) - extwt stake (vset b0) (vset bL))
        - τ.one_third (wt stake (vset bL))
        - τ.one_third (wt stake (vset bR))
        ≤
      wt stake (qL ∩ qR) :=
  match k_safety' τ stake vset parent genesis st hb1f hb2f hconf21 hconf12 with
  | ⟨bL, bR, qL, qR, hqLsub, hqRsub, hqLq2, hqRq2, _⟩ =>
    ⟨bL, bR, qL, qR, hqLsub, hqRsub,
      le_trans
        (Nat.sub_le_sub_right
          (Nat.sub_le_sub_right
            (validator_intersection_lower_bound stake (vset b0) (vset bL) (vset bR)) _) _)
        (quorum_intersection_weight_lower τ stake hqLsub hqRsub hqLq2.2 hqRq2.2)⟩
#detail_explode slashable_bound


end GasperBeaconChain.Core
