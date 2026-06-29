import GasperBeaconChain.Core.AtomicDef.Weight
import GasperBeaconChain.Core.Lemmas.SetTheoryProps
import Mathlib.Algebra.Order.BigOperators.Group.Finset

universe u

namespace GasperBeaconChain.Core

/-!
# Weight as a finitely additive measure

This file develops the arithmetic of {name}`wt`, the total-stake
functional on validator sets, as a *finitely additive measure*:
monotone under inclusion and obeying inclusion–exclusion over the
disjoint-union set algebra of {lit}`Lemmas/SetTheoryProps.lean`.

## Monotonicity

{lit}`wt_inc_leq` is the cornerstone: $`s_1 \subseteq s_2` implies
$`\operatorname{wt}(s_1) \le \operatorname{wt}(s_2)`. From it follow
the intersection bounds {lit}`wt_meet_leq1`, {lit}`wt_meet_leq2`,
{lit}`wt_meet_leq`.

## Additivity and inclusion–exclusion

Over the disjoint union {name}`fUnion` and difference {name}`fDiff`,
weight is *additive*:

$$`\operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(A) + \operatorname{wt}(\operatorname{fDiff}(B, A))`

({lit}`wt_fUnion`). Splitting $`A` into $`A \cap B` and
$`A \setminus B` gives
$`\operatorname{wt}(A) = \operatorname{wt}(A \cap B) + \operatorname{wt}(A \setminus B)`
({lit}`wt_inter_add_fDiff`), and together these yield the
**inclusion–exclusion** identity

$$`\operatorname{wt}(A) + \operatorname{wt}(B) = \operatorname{wt}(\operatorname{fUnion}(A, B)) + \operatorname{wt}(A \cap B)`

({lit}`wt_add_inter_fUnion`).

## Downstream use

{lit}`wt_inc_leq` underpins {lit}`quorum_2_upclosed`; the
inclusion–exclusion and difference laws
({lit}`wt_add_inter_fUnion`, {lit}`wt_fDiff`,
{lit}`wt_fUnion_of_disjointMF`) power
{lit}`quorum_intersection_weight_lower` and
{lit}`validator_intersection_lower_bound` of
{lit}`Theories/SlashableBound.lean`.
-/

variable {Validator : Type u}

/-!
## Basic properties

The weight function $`\operatorname{wt}` is non-negative,
vanishes on the empty set, respects set equality, and is monotone
under inclusion.
-/

/--
# Non-negativity

Weights are non-negative:

$$`0 \le \operatorname{wt}(\mathsf{stake}, s)`

Immediate from $`\mathbb{N}`-valuedness ({lit}`Nat.zero_le`).
This is rarely invoked explicitly — it holds by the type — but
serves as the base case in inductive weight arguments.
-/
theorem wt_nonneg
    (stake : Validator → Nat)
    (s : Finset Validator) :
    0 ≤ wt stake s :=
  Nat.zero_le _

/--
# Empty weight

The empty set has zero weight:

$$`\operatorname{wt}(\mathsf{stake}, \emptyset) = 0`

The sum over the empty {name}`Finset` is $`0`
({name}`Finset.sum_empty`). This is the identity element for the
additive structure: $`\operatorname{wt}(\emptyset)` plays the role
of the zero measure.
-/
theorem wt_set0
    (stake : Validator → Nat) :
    wt stake (∅ : Finset Validator) = 0 :=
  Finset.sum_empty

/--
# Monotonicity under inclusion

**Monotonicity of weight**:

$$`s_1 \subseteq s_2 \;\implies\; \operatorname{wt}(\mathsf{stake}, s_1) \le \operatorname{wt}(\mathsf{stake}, s_2)`

# Assumptions

Only the subset hypothesis $`s_1 \subseteq s_2` {lit}`hsub`, and
that the stake codomain $`\mathbb{N}` has non-negative elements.

# Proof idea

Write $`s_2` as the multiset sum of $`s_1` with a remainder $`t`
(from $`s_1 \subseteq s_2`), so the stake-mapped sums satisfy
$`\textstyle\sum_{s_2} = \sum_{s_1} + \sum_{t}`; non-negativity of
the remainder term ($`\mathbb{N}`-valued, hence $`\ge 0`) gives the
inequality.

# Non-assumptions

* No $`[\mathsf{DecidableEq}\ \mathsf{Validator}]` — this lemma sits
  *above* the {lit}`variable [DecidableEq Validator]` declaration in
  the file, and the proof goes through the raw multiset remainder
  rather than a {name}`Finset` difference. This is a deliberate
  placement, not an accident: monotonicity is the one weight fact
  that needs no decidable equality.
* No positivity of $`\mathsf{stake}` — zero stakes are allowed.
* Strictness is *not* claimed: $`s_1 \subsetneq s_2` may still give
  equal weights when the extra elements carry zero stake.

# Role in the development

The cornerstone of the measure layer: it yields the intersection
bounds {lit}`wt_meet_leq1`/{lit}`wt_meet_leq2`, the quorum
up-closure {lit}`quorum_2_upclosed`, and every $`\subseteq`-monotone
step in {lit}`Theories/SlashableBound.lean`.
-/
theorem wt_inc_leq
    (stake : Validator → Nat)
    {s₁ s₂ : Finset Validator}
    (hsub : s₁ ⊆ s₂) :
    wt stake s₁ ≤ wt stake s₂ :=
  match Multiset.le_iff_exists_add.mp (Finset.val_le_iff.mpr hsub) with
  | ⟨t, ht⟩ =>
    have hmapped : s₂.val.map stake = s₁.val.map stake + t.map stake :=
      (congrArg (Multiset.map stake) ht).trans (Multiset.map_add stake s₁.val t)
    have hsum : (s₂.val.map stake).sum = (s₁.val.map stake).sum + (t.map stake).sum :=
      (Multiset.sum_add (s₁.val.map stake) (t.map stake)).symm.trans
        (congrArg Multiset.sum hmapped).symm |>.symm
    Eq.mpr
      (congrArg₂ (· ≤ ·)
        (Finset.sum_eq_multiset_sum s₁ stake)
        (Finset.sum_eq_multiset_sum s₂ stake))
      (Eq.subst (motive := fun n => (s₁.val.map stake).sum ≤ n)
        hsum.symm (Nat.le_add_right _ _))

/--
# Congruence

Weight respects set equality:

$$`s_1 = s_2 \;\implies\; \operatorname{wt}(s_1) = \operatorname{wt}(s_2)`

By {lit}`congrArg`.
-/
theorem wt_eq
    (stake : Validator → Nat)
    {s₁ s₂ : Finset Validator}
    (h : s₁ = s₂) :
    wt stake s₁ = wt stake s₂ :=
  congrArg (wt stake) h

variable [DecidableEq Validator]

/-!
## Intersection bounds

The weight of an intersection is bounded by the weight of each
constituent set. These bounds are immediate corollaries of
monotonicity ({lit}`wt_inc_leq`) and the subset relations
$`s_1 \cap s_2 \subseteq s_1` and $`s_1 \cap s_2 \subseteq s_2`.
-/

/--
# Left intersection bound

The intersection weighs at most the left set:

$$`\operatorname{wt}(s_1 \cap s_2) \le \operatorname{wt}(s_1)`

Immediate from {lit}`wt_inc_leq` and the subset
$`s_1 \cap s_2 \subseteq s_1`
({name}`Finset.inter_subset_left`). Together with
{lit}`wt_meet_leq2` this supplies the two-sided bound needed
in the quorum-overlap arguments.
-/
theorem wt_meet_leq1
    (stake : Validator → Nat)
    (s₁ s₂ : Finset Validator) :
    wt stake (s₁ ∩ s₂) ≤ wt stake s₁ :=
  wt_inc_leq stake Finset.inter_subset_left

/--
# Right intersection bound

The intersection weighs at most the right set:

$$`\operatorname{wt}(s_1 \cap s_2) \le \operatorname{wt}(s_2)`

The symmetric counterpart of {lit}`wt_meet_leq1`, from
$`s_1 \cap s_2 \subseteq s_2`
({name}`Finset.inter_subset_right`).
-/
theorem wt_meet_leq2
    (stake : Validator → Nat)
    (s₁ s₂ : Finset Validator) :
    wt stake (s₁ ∩ s₂) ≤ wt stake s₂ :=
  wt_inc_leq stake Finset.inter_subset_right

/--
# Sum bound

The intersection weighs at most the sum of the two sets:

$$`\operatorname{wt}(s_1 \cap s_2) \le \operatorname{wt}(s_1) + \operatorname{wt}(s_2)`

Obtained by chaining {lit}`wt_meet_leq1` with
$`\operatorname{wt}(s_1) \le \operatorname{wt}(s_1) + \operatorname{wt}(s_2)`
({lit}`Nat.le_add_right`). A coarser bound than either
{lit}`wt_meet_leq1` or {lit}`wt_meet_leq2` individually, but
sometimes the only form needed when both summands are present.
-/
theorem wt_meet_leq
    (stake : Validator → Nat)
    (s₁ s₂ : Finset Validator) :
    wt stake (s₁ ∩ s₂) ≤ wt stake s₁ + wt stake s₂ :=
  le_trans (wt_meet_leq1 stake s₁ s₂) (Nat.le_add_right _ _)

/--
# Commutativity of intersection weight

Intersection weight is symmetric:

$$`\operatorname{wt}(s_1 \cap s_2) = \operatorname{wt}(s_2 \cap s_1)`

Lifts the set-level commutativity {lit}`inter_commF` through
{name}`wt` by congruence. Used in {lit}`wt_inter_add_fDiff`
(to split $`B`'s weight along $`A` by commuting the intersection)
and in {lit}`validator_intersection_lower_bound` (to swap the two
checkpoint validator sets).
-/
theorem wt_meetC
    (stake : Validator → Nat)
    (s₁ s₂ : Finset Validator) :
    wt stake (s₁ ∩ s₂) = wt stake (s₂ ∩ s₁) :=
  congrArg (wt stake) (inter_commF s₁ s₂)

/-!
## Additivity and inclusion–exclusion

The disjoint-union presentation of {name}`fUnion` makes weight
*additive*: the weight of a union splits as a plain sum (no
truncated subtraction). From this additive law the file derives
the partition identity, the inclusion–exclusion formula, and
its subtractive rearrangements. The derivation chain is:

1. {lit}`wt_fUnion` — additivity of weight over {name}`fUnion`
2. {lit}`inter_fDiff_partition` — the set-level partition
   $`A = (A \cap B) \uplus (A \setminus B)`
3. {lit}`wt_inter_add_fDiff` — weighing the partition
4. {lit}`wt_fDiff` — subtractive rearrangement
5. {lit}`wt_add_inter_fUnion` — inclusion–exclusion (additive)
6. {lit}`wt_fUnion_of_disjointMF` — disjoint special case
7. {lit}`wt_join_partition_fUnion` — three-block decomposition
8. {lit}`wt_join_fUnion` — inclusion–exclusion (subtractive)
-/

/--
# Additivity over disjoint union

**Additivity of weight**:

$$`\operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(A) + \operatorname{wt}(\operatorname{fDiff}(B, A))`

Because {name}`fUnion` is the *disjoint* sum $`A \uplus (B \setminus A)`,
the stake-mapped multiset sum splits additively — with no truncated
subtraction. This is the additive engine on which the
inclusion–exclusion identities below rest.

# Proof idea

The carrier of {name}`fUnion` is the raw multiset sum
$`A.\mathrm{val} + (\operatorname{fDiff}(B, A)).\mathrm{val}`.
Mapping {lit}`stake` distributes over multiset addition
({name}`Multiset.map_add`), and multiset sum distributes over
multiset addition ({name}`Multiset.sum_add`), giving the
$`\mathbb{N}`-level identity. The two
{name}`Finset.sum_eq_multiset_sum` conversions bridge between the
{name}`Finset.sum` presentation of {name}`wt` and the raw multiset
sum.
-/
theorem wt_fUnion
    (stake : Validator → Nat)
    (A B : Finset Validator) :
    wt stake (fUnion A B) = wt stake A + wt stake (fDiff B A) :=
  have hMultiset : ((A.val + (fDiff B A).val).map stake).sum
      = (A.val.map stake).sum + ((fDiff B A).val.map stake).sum :=
    (congrArg Multiset.sum (Multiset.map_add stake A.val (fDiff B A).val)).trans
      (Multiset.sum_add (A.val.map stake) ((fDiff B A).val.map stake))
  (Finset.sum_eq_multiset_sum (fUnion A B) stake).trans
    (hMultiset.trans
      (congrArg₂ (· + ·)
        (Finset.sum_eq_multiset_sum A stake).symm
        (Finset.sum_eq_multiset_sum (fDiff B A) stake).symm))

/--
# Set partition

**Partition of a set** into its intersection with $`B` and its
difference from $`B`:

$$`A = \operatorname{fUnion}(A \cap B,\, \operatorname{fDiff}(A, B))`

Every element of $`A` either lies in $`B` (landing in $`A \cap B`)
or not (landing in $`A \setminus B`); the two parts are disjoint.
This is the set-level identity (proved by {name}`Finset.ext`)
underlying the additive weight split {lit}`wt_inter_add_fDiff`.
-/
theorem inter_fDiff_partition
    (A B : Finset Validator) :
    A = fUnion (A ∩ B) (fDiff A B) :=
  Finset.ext fun x =>
    ⟨fun hxA =>
      if hxB : x ∈ B
      then mem_fUnion_left (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
      else mem_fUnion_right (mem_fDiff_of_mem_of_not_mem hxA hxB),
     fun hx => (mem_fUnion.mp hx).elim
      (fun hxI => match Finset.mem_inter.mp hxI with | ⟨hxA, _⟩ => hxA)
      (fun hxD => mem_left_of_mem_fDiff hxD)⟩

/--
# Additive weight split

**Additive split of a set's weight** along $`B`:

$$`\operatorname{wt}(A) = \operatorname{wt}(A \cap B) + \operatorname{wt}(\operatorname{fDiff}(A, B))`

The weight of $`A` is the weight of its part inside $`B` plus the
weight of its part outside $`B`. Together with {lit}`wt_fUnion` it
produces the inclusion–exclusion identity
{lit}`wt_add_inter_fUnion`, and rearranged it gives the subtractive
form {lit}`wt_fDiff`.

# Proof idea

First, {lit}`inter_fDiff_partition` gives the set-level partition
$`A = \operatorname{fUnion}(A \cap B,\, \operatorname{fDiff}(A, B))`.
Weighing this through {lit}`wt_fUnion` would yield
$`\operatorname{wt}(A) = \operatorname{wt}(A \cap B) + \operatorname{wt}(\operatorname{fDiff}(\operatorname{fDiff}(A,B),\, A \cap B))`,
but the inner {lit}`fDiff` is idempotent:
$`\operatorname{fDiff}(\operatorname{fDiff}(A, B),\, A \cap B) = \operatorname{fDiff}(A, B)`
(proved by {name}`Finset.ext` — an element of $`A \setminus B`
cannot lie in $`A \cap B`). This auxiliary fact {lit}`hfdf` simplifies
the right side to $`\operatorname{wt}(\operatorname{fDiff}(A, B))`,
completing the split.
-/
theorem wt_inter_add_fDiff
    (stake : Validator → Nat)
    (A B : Finset Validator) :
    wt stake A = wt stake (A ∩ B) + wt stake (fDiff A B) :=
  have hfdf : fDiff (fDiff A B) (A ∩ B) = fDiff A B :=
    Finset.ext fun _ =>
      ⟨fun hx => mem_left_of_mem_fDiff hx,
       fun hx => mem_fDiff_of_mem_of_not_mem hx
         (fun hxI => match Finset.mem_inter.mp hxI with
           | ⟨_, hxB⟩ => (not_mem_right_of_mem_fDiff hx) hxB)⟩
  have hpart : A = fUnion (A ∩ B) (fDiff A B) := inter_fDiff_partition A B
  have hwt : wt stake (fUnion (A ∩ B) (fDiff A B)) =
      wt stake (A ∩ B) + wt stake (fDiff A B) :=
    Eq.subst (motive := fun s =>
        wt stake (fUnion (A ∩ B) (fDiff A B)) = wt stake (A ∩ B) + wt stake s)
      hfdf (wt_fUnion stake (A ∩ B) (fDiff A B))
  Eq.subst (motive := fun s => wt stake s = wt stake (A ∩ B) + wt stake (fDiff A B))
    hpart.symm hwt

/--
# Difference weight (subtractive form)

**Subtractive form of the difference weight**:

$$`\operatorname{wt}(\operatorname{fDiff}(A, B)) = \operatorname{wt}(A) - \operatorname{wt}(A \cap B)`

The truncated-subtraction rearrangement of {lit}`wt_inter_add_fDiff`;
legitimate as a genuine subtraction because $`A \cap B \subseteq A`,
so the minuend dominates. Consumed by
{lit}`validator_intersection_lower_bound` to express the weight of
validators that exited (the part of one checkpoint's set not in the
other's).
-/
theorem wt_fDiff
    (stake : Validator → Nat)
    (A B : Finset Validator) :
    wt stake (fDiff A B) = wt stake A - wt stake (A ∩ B) :=
  (Nat.sub_eq_of_eq_add
    ((wt_inter_add_fDiff stake A B).trans
      (Nat.add_comm (wt stake (A ∩ B)) (wt stake (fDiff A B))))).symm

/--
# Inclusion–exclusion (additive form)

**Inclusion–exclusion** for weight:

$$`\operatorname{wt}(A) + \operatorname{wt}(B) = \operatorname{wt}(\operatorname{fUnion}(A, B)) + \operatorname{wt}(A \cap B)`

# Assumptions

An arbitrary $`\mathsf{stake} : V \to \mathbb{N}`, and
$`[\mathsf{DecidableEq}\ V]` (in scope as a section variable) for
the intersection on the right.

# Interpretation

Summing the two sets' weights double-counts exactly their
intersection; moving that shared weight to the right gives the
union weight. The classical $`|A| + |B| = |A \cup B| + |A \cap B|`,
weighed by stake.

# Proof idea

Split $`\operatorname{wt}(B)` as
$`\operatorname{wt}(A \cap B) + \operatorname{wt}(B \setminus A)`
({lit}`wt_inter_add_fDiff` with {lit}`inter_commF`), then recognize
$`\operatorname{wt}(A) + \operatorname{wt}(B \setminus A) = \operatorname{wt}(\operatorname{fUnion}(A, B))`
({lit}`wt_fUnion`).

# Non-assumptions

* $`A` and $`B` need *not* be disjoint — the $`\operatorname{wt}(A \cap B)`
  term is precisely the correction handling overlap (the disjoint
  special case, where it vanishes, is {lit}`wt_fUnion_of_disjointMF`).
* No positivity of stake and no quorum hypothesis: the identity is
  purely algebraic and holds for every pair of finite validator
  sets.

# Role in the development

The algebraic heart of the quorum-overlap arguments: it is the
purely additive precursor that {lit}`wt_quorum_union_bound_fUnion`
and {lit}`quorum_intersection_weight_lower`
({lit}`Theories/SlashableBound.lean`) instantiate with quorum and
validator-set weights to lower-bound the slashed intersection.

# Remarks

The identity is stated in its *additive* (subtraction-free) form.
This is a deliberate representation choice, not a cosmetic one: over
$`\mathbb{N}` the additive equality is the primitive statement —
it holds in any commutative monoid, needing neither subtraction nor
an order — whereas the familiar subtractive form
$`\operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(A) + \operatorname{wt}(B) - \operatorname{wt}(A \cap B)`
({lit}`wt_join_fUnion`) is recovered only afterward by truncated
rearrangement, and is specific to natural-number arithmetic.
-/
theorem wt_add_inter_fUnion
    (stake : Validator → Nat)
    (A B : Finset Validator) :
    wt stake A + wt stake B
      =
    wt stake (fUnion A B) + wt stake (A ∩ B) :=
  have hB : wt stake B = wt stake (A ∩ B) + wt stake (fDiff B A) :=
    (wt_inter_add_fDiff stake B A).trans
      (congrArg (· + wt stake (fDiff B A)) (congrArg (wt stake) (inter_commF B A)))
  have hwtU : wt stake (fUnion A B) = wt stake A + wt stake (fDiff B A) :=
    wt_fUnion stake A B
  calc wt stake A + wt stake B
      = wt stake A + (wt stake (A ∩ B) + wt stake (fDiff B A)) := congrArg _ hB
    _ = wt stake (A ∩ B) + (wt stake A + wt stake (fDiff B A)) :=
        Nat.add_left_comm (wt stake A) (wt stake (A ∩ B)) (wt stake (fDiff B A))
    _ = wt stake (fUnion A B) + wt stake (A ∩ B) :=
        (congrArg (wt stake (A ∩ B) + ·) hwtU.symm).trans
          (Nat.add_comm (wt stake (A ∩ B)) (wt stake (fUnion A B)))

/--
# Disjoint union weight

For genuinely disjoint sets the union weight is the plain sum:

$$`\operatorname{disjointMF}(A.\mathrm{val},\, B.\mathrm{val}) \;\implies\; \operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(A) + \operatorname{wt}(B)`

When $`A` and $`B` already share no element,
$`\operatorname{fDiff}(B, A) = B`, so the general additive law
{lit}`wt_fUnion` collapses to the unqualified sum (no intersection
correction). Used in {lit}`wt_meet_subbound_fUnion` of
{lit}`Theories/SlashableBound.lean`.
-/
theorem wt_fUnion_of_disjointMF
    (stake : Validator → Nat)
    {A B : Finset Validator}
    (hdis : disjointMF A.val B.val) :
    wt stake (fUnion A B) = wt stake A + wt stake B :=
  have hfDiff_eq : fDiff B A = B :=
    Finset.ext fun x =>
      ⟨fun hx => mem_left_of_mem_fDiff hx,
       fun hx => mem_fDiff_of_mem_of_not_mem hx (fun hxA => hdis x hxA hx)⟩
  Eq.subst (motive := fun s => wt stake (fUnion A B) = wt stake A + wt stake s)
    hfDiff_eq (wt_fUnion stake A B)

/--
# Three-block decomposition

**Three-block weight decomposition** of the union:

$$`\operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(\operatorname{fDiff}(A, B)) + \operatorname{wt}(\operatorname{fDiff}(B, A)) + \operatorname{wt}(A \cap B)`

The weight of $`A \cup B` split across its three pairwise-disjoint
blocks — left-only $`A \setminus B`, right-only $`B \setminus A`,
and shared $`A \cap B` — obtained by combining {lit}`wt_fUnion` with
the split {lit}`wt_inter_add_fDiff`. The weight image of the
set partition {lit}`setU_parF`.
-/
theorem wt_join_partition_fUnion
    (stake : Validator → Nat)
    (A B : Finset Validator) :
    wt stake (fUnion A B)
      =
    wt stake (fDiff A B) + wt stake (fDiff B A) + wt stake (A ∩ B) :=
  calc wt stake (fUnion A B)
      = wt stake A + wt stake (fDiff B A) := wt_fUnion stake A B
    _ = (wt stake (A ∩ B) + wt stake (fDiff A B))
          + wt stake (fDiff B A) :=
        congrArg (· + _) (wt_inter_add_fDiff stake A B)
    _ = wt stake (fDiff A B) + wt stake (fDiff B A) + wt stake (A ∩ B) :=
        (Nat.add_assoc (wt stake (A ∩ B)) (wt stake (fDiff A B))
          (wt stake (fDiff B A))).trans
        (Nat.add_comm (wt stake (A ∩ B))
          (wt stake (fDiff A B) + wt stake (fDiff B A)))

/--
# Inclusion–exclusion (subtractive form)

**Subtractive inclusion–exclusion** for the union weight:

$$`\operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(A) + \operatorname{wt}(B) - \operatorname{wt}(A \cap B)`

The familiar $`|A \cup B| = |A| + |B| - |A \cap B|`, obtained as the
truncated-subtraction rearrangement of the additive form
{lit}`wt_add_inter_fUnion` (valid since $`\operatorname{wt}(A \cap B)`
is dominated by $`\operatorname{wt}(A) + \operatorname{wt}(B)`).
-/
theorem wt_join_fUnion
    (stake : Validator → Nat)
    (A B : Finset Validator) :
    wt stake (fUnion A B)
      =
    wt stake A + wt stake B - wt stake (A ∩ B) :=
  (Nat.sub_eq_of_eq_add (wt_add_inter_fUnion stake A B)).symm

/-!
# Appendix: weight as a finitely additive measure

*This appendix is a non-load-bearing aside. Nothing in the
{lit}`Core` development depends on the perspective recorded here;
it is collected at the file's end as added context, deliberately
separated from the load-bearing docstrings above. It may be read or
skipped without affecting any proof.*

The lemmas above can be read through a single organising lens: the
total-stake functional
$`\operatorname{wt}(\mathsf{stake}, s) = \sum_{v \in s} \mathsf{stake}(v)`
is the **finitely additive measure** induced on the finite Boolean
algebra $`\mathcal{P}(V)` of validator subsets by the point mass
$`\mathsf{stake} : V \to \mathbb{N}`. Reading the file's results in
that language:

* **Base laws** — {lit}`wt_set0` ($`\operatorname{wt}(\emptyset) = 0`)
  and {lit}`wt_fUnion_of_disjointMF` (additivity on disjoint pairs)
  are exactly the two axioms of a finitely additive measure
  (null empty set, finite additivity).
* **Monotonicity** — {lit}`wt_inc_leq` is the order-theoretic
  shadow of additivity: for a measure valued in an ordered monoid
  with non-negative masses,
  $`s_1 \subseteq s_2 \implies \mu(s_2) = \mu(s_1) + \mu(s_2 \setminus s_1) \ge \mu(s_1)`,
  the remainder being $`\mathbb{N}`-valued and hence $`\ge 0`.
* **Inclusion–exclusion** — {lit}`wt_add_inter_fUnion` is the
  $`N = 2` additive instance of the classical inclusion–exclusion
  principle (Poincaré's formula). The file does not state or use
  the general $`N`-ary signed formula; over $`\mathbb{N}` the
  additive two-set form is primitive (valid in any commutative
  monoid) and the subtractive rearrangement
  ({lit}`wt_join_fUnion`) is a derived convenience specific to
  natural-number arithmetic.

The value of this lens is taxonomic: it explains *why* the eight
lemmas of the additivity block form a closed family (they are the
finite-measure laws plus their truncated-subtraction rearrangements)
rather than an ad-hoc list. But the proofs themselves use only
$`\mathbb{N}`-arithmetic and the disjoint-union set algebra of
{lit}`Lemmas/SetTheoryProps.lean`; no measure-theoretic machinery is
imported or required.
-/

end GasperBeaconChain.Core
