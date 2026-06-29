import Mathlib.Data.Finset.Basic

universe u

namespace GasperBeaconChain.Core

/-!
# Finite-set algebra: disjoint union and difference

A self-contained fragment of the Boolean algebra of {name}`Finset`s,
organized so that the weight functional {lit}`wt` decomposes
*additively* over it.

## The disjoint-union presentation

The two operations are presented in a deliberately concrete form:

* {lit}`fDiff` $`A\,B = A \cap B^{c}`, as a {name}`Finset.filter`;
* {lit}`fUnion` $`A\,B = A \uplus (B \setminus A)`, a genuinely
  *disjoint* union assembled from the underlying multisets together
  with an explicit {name}`Multiset.Nodup` proof.

Presenting the union as the disjoint sum $`A \uplus (B \setminus A)`
is what makes weight additive:

$$`\operatorname{wt}(A \uplus (B \setminus A)) = \operatorname{wt}(A) + \operatorname{wt}(B \setminus A)`

with no truncated subtraction (see {lit}`wt_fUnion` in
{lit}`Lemmas/Weight.lean`) — in contrast to the ordinary union,
whose weight obeys only the subtractive inclusion–exclusion
$`\operatorname{wt}(A) + \operatorname{wt}(B) - \operatorname{wt}(A \cap B)`.
Every disjointness and partition identity collected here exists to
feed exactly such additive weight decompositions.

## Contents

* {lit}`disjointMF` / {lit}`disjointF` — disjointness of multisets
  and of finite sets, with their stability lemmas;
* {lit}`fDiff` — filter-based difference and its membership API;
* {lit}`fUnion` — disjoint union and its membership API;
* the {lit}`setU_parF` partition and the
  {lit}`set*_disjointF` / {lit}`set*_subsetF` family — disjointness
  and containment identities among nested intersections and
  differences.

## Downstream use

{lit}`Lemmas/Weight.lean` turns these into the inclusion–exclusion
identities for {lit}`wt`; those in turn power the quorum-overlap
bounds {lit}`quorum_intersection_weight_lower` and
{lit}`validator_intersection_lower_bound` of
{lit}`Theories/SlashableBound.lean`.
-/

variable {α : Type u}




/-!
## Disjointness of multisets and finite sets
-/

/--
# Multiset disjointness: no shared elements

$`\operatorname{disjointMF}(s, t)` holds
when no element of $`s` occurs in $`t`:

$$`\operatorname{disjointMF}(s, t) \;\;\coloneqq\;\; \forall a,\; a \in s \to a \notin t`

A {lit}`Prop`-valued, decidability-free formulation (it does not go
through Mathlib's {lit}`Disjoint` typeclass), used to state the
nodup-preservation law {lit}`nodup_add_of_disjointMF` for the
multiset sum underlying {lit}`fUnion`.
-/
def disjointMF (s t : Multiset α) : Prop :=
  ∀ a, a ∈ s → a ∉ t

/--
# Duplicate-free multiset sum from disjointness

The multiset sum of two duplicate-free multisets is again
duplicate-free, provided they are {lit}`disjointMF`:

$$`s.\mathrm{Nodup} \;\wedge\; t.\mathrm{Nodup} \;\wedge\; \operatorname{disjointMF}(s, t) \;\implies\; (s + t).\mathrm{Nodup}`

# Proof idea

Induction on $`s` ({name}`Multiset.induction_on`). The base case
$`s = 0` is just $`t`'s {name}`Multiset.Nodup`. In the cons step
$`a ::ₘ s`, the head $`a` avoids $`s` (from cons-nodup) and avoids
$`t` (from disjointness), so it avoids $`s + t`; the tail follows
from the induction hypothesis on the restricted disjointness.

# Assumptions

* $`s.\mathrm{Nodup}`, $`t.\mathrm{Nodup}` — both summands are
  already duplicate-free {lit}`hs`, {lit}`ht`;
* $`\operatorname{disjointMF}(s, t)` — they share no element
  {lit}`hd`.

# Non-assumptions

* no $`[\mathsf{DecidableEq}\ \alpha]` — the statement and proof are
  decidability-free, which is exactly why {lit}`disjointMF` is
  phrased as a bare $`\forall` rather than through Mathlib's
  $`\mathsf{Disjoint}` typeclass (this lemma sits *above* the
  $`\mathsf{DecidableEq}` section variable);
* disjointness is required only *between* $`s` and $`t`, not within
  either (within-duplicates are already excluded by the two
  $`\mathrm{Nodup}` hypotheses);
* commutativity of the roles is not used — the induction is on the
  left summand $`s`, so the asymmetric phrasing is faithful to the
  proof.

# Role in the development

This discharges the {name}`Multiset.Nodup` obligation when building
{lit}`fUnion` as a {name}`Finset` from the raw multiset sum
$`A.\mathrm{val} + (\operatorname{fDiff}(B, A)).\mathrm{val}` —
the single fact that makes the disjoint union well-defined as a
{name}`Finset` and hence makes weight additive.
-/
theorem nodup_add_of_disjointMF
    {s t : Multiset α}
    (hs : s.Nodup) (ht : t.Nodup)
    (hd : disjointMF s t) :
    (s + t).Nodup :=
  @Multiset.induction_on α (fun s => s.Nodup → disjointMF s t → (s + t).Nodup) s
    (fun _ _ => Eq.subst (motive := fun x => x.Nodup) (Multiset.zero_add t).symm ht)
    (fun a s ih hs hd =>
      match Multiset.nodup_cons.mp hs with
      | ⟨ha_not_mem, hs_nodup⟩ =>
      Eq.subst (motive := fun x => x.Nodup) (Multiset.cons_add a s t).symm
        (Multiset.nodup_cons.mpr
        ⟨fun hmem =>
          (Multiset.mem_add.mp hmem).elim
            ha_not_mem
            (hd a (Multiset.mem_cons_self a s)),
         ih hs_nodup
            (fun b hb => hd b (Multiset.mem_cons_of_mem hb))⟩))
    hs hd




/--
# Finite-set disjointness: joint membership yields $`\bot`

**Finite-set disjointness** as a $`\bot`-valued predicate:

$$`\operatorname{disjointF}(A, B) \;\;\coloneqq\;\; \forall x,\; x \in A \to x \in B \to \bot`

This *negative* phrasing (joint membership yields a contradiction)
is preferred over $`A \cap B = \emptyset`: it threads directly
through the case analyses of the weight and slashing arguments
without an intervening emptiness rewrite.
-/
def disjointF (A B : Finset α) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False

/--
# Disjointness is symmetric

$$`\operatorname{disjointF}(A, B) \;\implies\; \operatorname{disjointF}(B, A)`

The proof simply swaps the two membership arguments. This is the
commutativity law of the disjointness relation, used in
{lit}`disjointF_of_subset_right` to reduce a right-side weakening
to a left-side weakening via symmetry.
-/
theorem disjointF_comm
    {A B : Finset α}
    (h : disjointF A B) :
    disjointF B A :=
  fun x hxB hxA => h x hxA hxB

/--
# Shrinking the left side preserves disjointness

$$`A \subseteq B \;\wedge\; \operatorname{disjointF}(B, C) \;\implies\; \operatorname{disjointF}(A, C)`

Shrinking one side of a disjoint pair preserves disjointness: if
no element of $`B` lies in $`C`, then a fortiori no element of
$`A \subseteq B` lies in $`C`. The proof routes membership
through the subset inclusion before applying the disjointness
hypothesis.
-/
theorem disjointF_of_subset_left
    {A B C : Finset α}
    (hsub : A ⊆ B)
    (h : disjointF B C) :
    disjointF A C :=
  fun x hxA hxC => h x (hsub hxA) hxC

/--
# Shrinking the right side preserves disjointness

$$`B \subseteq C \;\wedge\; \operatorname{disjointF}(A, C) \;\implies\; \operatorname{disjointF}(A, B)`

The symmetric counterpart of {lit}`disjointF_of_subset_left`:
shrinking the *right* side of a disjoint pair also preserves
disjointness.
-/
theorem disjointF_of_subset_right
    {A B C : Finset α}
    (hsub : B ⊆ C)
    (h : disjointF A C) :
    disjointF A B :=
  fun x hxA hxB => h x hxA (hsub hxB)



/-!
## Intersection and difference

From here on $`\alpha` carries {name}`DecidableEq`, so membership is
decidable and {name}`Finset.filter` is available.
-/

variable [DecidableEq α]

/--
# Intersection is commutative

**Commutativity of intersection**, proved pointwise by
{name}`Finset.ext`:

$$`A \cap B = B \cap A`

A membership-level proof, avoiding any lattice-theoretic detour.
Consumed by {lit}`wt_meetC` (to commute intersection weights) and by
{lit}`validator_intersection_lower_bound` (to swap the two checkpoint
validator sets).
-/
theorem inter_commF
    (A B : Finset α) :
    A ∩ B = B ∩ A :=
  Finset.ext fun _ =>
    ⟨fun h => match Finset.mem_inter.mp h with
              | ⟨ha, hb⟩ => Finset.mem_inter.mpr ⟨hb, ha⟩,
     fun h => match Finset.mem_inter.mp h with
              | ⟨hb, ha⟩ => Finset.mem_inter.mpr ⟨ha, hb⟩⟩


/--
# Set difference by filtering

**Set difference** $`A \setminus B`, realised as a
{name}`Finset.filter`:

$$`\operatorname{fDiff}(A, B) \;\;\coloneqq\;\; \{\, x \in A \;\mid\; x \notin B \,\}`

Defining the difference by filtering keeps it a transparent subset
of $`A` with a definitional membership rule ({lit}`mem_fDiff`),
rather than relying on Mathlib's $`\setminus`. It is the building
block of the disjoint union {lit}`fUnion` and of the subtractive
weight law {lit}`wt_fDiff`.
-/
def fDiff (A B : Finset α) : Finset α :=
  A.filter (fun x => x ∉ B)

/--
# Membership in the difference: in $`A` and not in $`B`

Membership characterization of {lit}`fDiff`:

$$`x \in \operatorname{fDiff}(A, B) \;\iff\; x \in A \;\wedge\; x \notin B`

Definitional, via {name}`Finset.mem_filter`. This is the primary
interface through which all other {lit}`fDiff` lemmas — projections,
introduction, subset — are derived.
-/
theorem mem_fDiff
    {A B : Finset α}
    {x : α} :
    x ∈ fDiff A B ↔ x ∈ A ∧ x ∉ B :=
  (show x ∈ A.filter (· ∉ B) ↔ _ from Finset.mem_filter)

/--
# An element of the difference lies in the minuend

Left projection: an element of the difference lies in the
minuend.

$$`x \in \operatorname{fDiff}(A, B) \;\implies\; x \in A`

Forward direction of {lit}`mem_fDiff`, projecting the first
conjunct.
-/
theorem mem_left_of_mem_fDiff
    {A B : Finset α}
    {x : α}
    (hx : x ∈ fDiff A B) :
    x ∈ A :=
  match mem_fDiff.mp hx with | ⟨hxA, _⟩ => hxA

/--
# An element of the difference lies outside the subtrahend

Right projection: an element of the difference lies outside the
subtrahend.

$$`x \in \operatorname{fDiff}(A, B) \;\implies\; x \notin B`

Forward direction of {lit}`mem_fDiff`, projecting the second
conjunct. This is the workhorse of every disjointness argument
in this file: the contradiction
$`x \in B \;\wedge\; x \notin B` is produced by applying this
lemma to one membership and the other's inclusion in $`B`.
-/
theorem not_mem_right_of_mem_fDiff
    {A B : Finset α}
    {x : α}
    (hx : x ∈ fDiff A B) :
    x ∉ B :=
  match mem_fDiff.mp hx with | ⟨_, hxnB⟩ => hxnB

/--
# Constructing a difference membership proof

Introduction rule for {lit}`fDiff`:

$$`x \in A \;\wedge\; x \notin B \;\implies\; x \in \operatorname{fDiff}(A, B)`

Backward direction of {lit}`mem_fDiff`, assembling the two
conditions into a membership proof.
-/
theorem mem_fDiff_of_mem_of_not_mem
    {A B : Finset α}
    {x : α}
    (hxA : x ∈ A) (hxnB : x ∉ B) :
    x ∈ fDiff A B :=
  mem_fDiff.mpr ⟨hxA, hxnB⟩

/--
# The difference is a subset of the minuend

$$`\operatorname{fDiff}(A, B) \;\subseteq\; A`

Every element of $`A \setminus B` lies in $`A` (via
{lit}`mem_left_of_mem_fDiff`). This corollary is the subset
condition that feeds {lit}`wt_inc_leq` when bounding the weight
of a difference.
-/
theorem fDiff_subset_left (A B : Finset α) :
    fDiff A B ⊆ A :=
  fun _ hx => mem_left_of_mem_fDiff hx

/--
# The intersection and difference of $`A` along $`B` are disjoint

The intersection and the difference form a disjoint partition of
$`A`:

$$`\forall x,\; x \in A \cap B \;\to\; x \in \operatorname{fDiff}(A, B) \;\to\; \bot`

The intersection forces $`x \in B`; the difference forces
$`x \notin B` (via {lit}`not_mem_right_of_mem_fDiff`). Their
conjunction is therefore contradictory. This fact — that
$`A = (A \cap B) \uplus (A \setminus B)` is a genuinely disjoint
decomposition — is what makes the weight split
{lit}`wt_inter_add_fDiff` additive. Restated as
{lit}`setID_disjointF`.
-/
theorem inter_fDiff_disjointF
    (A B : Finset α) :
    ∀ x, x ∈ A ∩ B → x ∈ fDiff A B → False :=
  fun _ hxI hxD =>
    match Finset.mem_inter.mp hxI with
    | ⟨_, hxB⟩ => (not_mem_right_of_mem_fDiff hxD) hxB

/--
# The two one-sided differences $`A \setminus B` and $`B \setminus A` are disjoint

The two one-sided differences are disjoint:

$$`\forall x,\; x \in \operatorname{fDiff}(A, B) \;\to\; x \in \operatorname{fDiff}(B, A) \;\to\; \bot`

An element of $`A \setminus B` lies in $`A`; an element of
$`B \setminus A` lies outside $`A`
({lit}`not_mem_right_of_mem_fDiff`). Joint membership would
require $`x \in A` and $`x \notin A` simultaneously. Restated as
{lit}`setDD_disjointF`.
-/
theorem fDiff_disjointF_swap
    (A B : Finset α) :
    ∀ x, x ∈ fDiff A B → x ∈ fDiff B A → False :=
  fun _ hxAB hxBA =>
    (not_mem_right_of_mem_fDiff hxBA) (mem_left_of_mem_fDiff hxAB)




/-!
## Disjoint union
-/

/--
# Disjoint union: $`A \uplus (B \setminus A)`

**Disjoint union** $`A \uplus (B \setminus A)`, the central
construction of this file:

$$`\operatorname{fUnion}(A, B) \;\;\coloneqq\;\; A.\mathrm{val} + (\operatorname{fDiff}(B, A)).\mathrm{val}`

# Construction

The carrier is the *multiset sum* of $`A` with the part of $`B` not
already in $`A`. Because that second summand is disjoint from $`A`
({lit}`not_mem_right_of_mem_fDiff`), the sum stays duplicate-free,
and {lit}`nodup_add_of_disjointMF` supplies the
{name}`Multiset.Nodup` field of the resulting {name}`Finset`.

# Why disjoint

As a *set*, $`\operatorname{fUnion}(A, B)` has the same elements as
$`A \cup B` ({lit}`mem_fUnion`). The point of the disjoint
presentation is *weight*: since the two summands share no element,
$`\operatorname{wt}` adds without correction —
$`\operatorname{wt}(\operatorname{fUnion}(A, B)) = \operatorname{wt}(A) + \operatorname{wt}(\operatorname{fDiff}(B, A))`
({lit}`wt_fUnion`) — which is the additive engine of the
inclusion–exclusion lemmas in {lit}`Lemmas/Weight.lean`.

# Design choices and non-properties

The construction is *deliberately asymmetric* in its two arguments:
$`\operatorname{fUnion}(A, B)` keeps all of $`A` and only the
$`A`-complement of $`B`. Consequently:

* It is *not* literally symmetric — $`\operatorname{fUnion}(A, B)`
  and $`\operatorname{fUnion}(B, A)` are equal as *sets* (both have
  underlying set $`A \cup B`) but their multiset carriers differ in
  general. Symmetry is therefore stated and used only at the level
  of membership / weight, never as carrier equality.
* It is *not* Mathlib's $`A \cup B`: that operation deduplicates via
  $`\mathsf{DecidableEq}` after concatenation, whereas
  $`\operatorname{fUnion}` is duplicate-free *by construction* (the
  second summand is pre-filtered), which is what lets
  {lit}`wt_fUnion` avoid any truncated-subtraction correction.
-/
def fUnion (A B : Finset α) : Finset α where
  val := A.val + (fDiff B A).val
  nodup := nodup_add_of_disjointMF A.nodup (fDiff B A).nodup
    (fun a haA haBA =>
      (not_mem_right_of_mem_fDiff (show a ∈ fDiff B A from haBA))
        (show a ∈ A from haA))

/--
# Union membership: $`x \in A` or $`x \in B`

Membership in {lit}`fUnion` matches ordinary union:
$`x \in \operatorname{fUnion}(A, B) \iff x \in A \vee x \in B`.

The forward direction reads off the two multiset summands; the
backward direction routes $`x \in B` either to $`A` (if already
there) or to $`\operatorname{fDiff}(B, A)`.
-/
theorem mem_fUnion
    {A B : Finset α}
    {x : α} :
    x ∈ fUnion A B ↔ x ∈ A ∨ x ∈ B :=
  have forward : x ∈ A.val + (fDiff B A).val → x ∈ A ∨ x ∈ B :=
    fun h => (Multiset.mem_add.mp h).elim
      Or.inl
      (fun hBA => Or.inr (mem_left_of_mem_fDiff hBA))
  have backward : x ∈ A ∨ x ∈ B → x ∈ A.val + (fDiff B A).val :=
    fun h => h.elim
      (fun hA => Multiset.mem_add.mpr (Or.inl hA))
      (fun hB => if hA : x ∈ A
        then Multiset.mem_add.mpr (Or.inl hA)
        else Multiset.mem_add.mpr (Or.inr (mem_fDiff_of_mem_of_not_mem hB hA)))
  ⟨forward, backward⟩

/--
# Left inclusion into the union
Left introduction: $`x \in A \implies x \in \operatorname{fUnion}(A, B)`. -/
theorem mem_fUnion_left
    {A B : Finset α}
    {x : α}
    (hx : x ∈ A) :
    x ∈ fUnion A B :=
  mem_fUnion.mpr (Or.inl hx)

/--
# Right inclusion into the union
Right introduction: $`x \in B \implies x \in \operatorname{fUnion}(A, B)`. -/
theorem mem_fUnion_right
    {A B : Finset α}
    {x : α}
    (hx : x ∈ B) :
    x ∈ fUnion A B :=
  mem_fUnion.mpr (Or.inr hx)

/--
# The union is the smallest superset of both sets

Universal property of the union: if $`A \subseteq C` and
$`B \subseteq C`, then $`\operatorname{fUnion}(A, B) \subseteq C`.
-/
theorem fUnion_subset
    {A B C : Finset α}
    (hA : A ⊆ C)
    (hB : B ⊆ C) :
    fUnion A B ⊆ C :=
  fun _ hx => (mem_fUnion.mp hx).elim (fun h => hA h) (fun h => hB h)

/--
# The difference splits through an intermediary (triangle bound)

**Triangle containment for differences** through an intermediary
$`s_0`:

$$`\operatorname{fDiff}(s_1, s_2) \;\subseteq\; \operatorname{fUnion}\bigl(\operatorname{fDiff}(s_0, s_2),\; \operatorname{fDiff}(s_1, s_0)\bigr)`

# Interpretation

An element of $`s_1` outside $`s_2` is — depending on whether it
lies in the intermediary $`s_0` — either in $`s_0 \setminus s_2` or
in $`s_1 \setminus s_0`. This is the set-level form of the triangle
bound $`s_1 \setminus s_2 \le (s_0 \setminus s_2) + (s_1 \setminus s_0)`
that {lit}`wt_meet_tri_bound_fDiff` weighs, ultimately bounding
validator churn between checkpoints in
{lit}`validator_intersection_lower_bound`.
-/
theorem fDiff_subset_triangle
    (s0 s1 s2 : Finset α) :
    fDiff s1 s2 ⊆ fUnion (fDiff s0 s2) (fDiff s1 s0) :=
  fun _ hx =>
    if hx0 : _ ∈ s0
    then mem_fUnion_left (mem_fDiff_of_mem_of_not_mem hx0 (not_mem_right_of_mem_fDiff hx))
    else mem_fUnion_right (mem_fDiff_of_mem_of_not_mem (mem_left_of_mem_fDiff hx) hx0)




/-!
## Partition and containment identities

The remaining lemmas record disjointness, partition, and
containment facts among nested intersections and differences,
mirroring the Coq {lit}`set*` lemma family. They form a *reusable
toolkit*: the weight layer's additive decompositions
({lit}`Lemmas/Weight.lean`) rest on the underlying
{lit}`fUnion`/{lit}`fDiff` operations and on
{lit}`fDiff_subset_triangle`, rather than on these bundled
identities individually.

Each {lit}`set*_disjointF` asserts that two assembled pieces share
no element; each {lit}`set*_subsetF` bounds one assembled set inside
another.
-/

/--
# $`A \cap B` and $`A \setminus B` are disjoint (in {lit}`disjointF` form)

The intersection and the difference are disjoint, restated in
{lit}`disjointF` form:

$$`\operatorname{disjointF}(A \cap B,\; \operatorname{fDiff}(A, B))`

Direct restatement of {lit}`inter_fDiff_disjointF` using the
{lit}`disjointF` wrapper (which packages the $`\bot`-valued
predicate for use in the weight arguments).
-/
theorem setID_disjointF
    (A B : Finset α) :
    disjointF (A ∩ B) (fDiff A B) :=
  inter_fDiff_disjointF A B

/--
# $`A \setminus B` and $`B \setminus A` are disjoint (in {lit}`disjointF` form)

The two one-sided differences are disjoint, restated in
{lit}`disjointF` form:

$$`\operatorname{disjointF}(\operatorname{fDiff}(A, B),\; \operatorname{fDiff}(B, A))`

Direct restatement of {lit}`fDiff_disjointF_swap`.
-/
theorem setDD_disjointF
    (A B : Finset α) :
    disjointF (fDiff A B) (fDiff B A) :=
  fDiff_disjointF_swap A B

/--
# The symmetric difference and the intersection are disjoint

The symmetric difference is disjoint from the intersection:

$$`\operatorname{disjointF}\bigl(\operatorname{fUnion}(\operatorname{fDiff}(A, B),\, \operatorname{fDiff}(B, A)),\; A \cap B\bigr)`

The left union consists of elements that are in exactly one of
$`A, B` but not both; the intersection consists of elements in
both. Joint membership would require an element to be both
"in exactly one" and "in both" — contradictory. The proof
extracts $`x \in A` and $`x \in B` from the intersection, then
applies {lit}`not_mem_right_of_mem_fDiff` to whichever difference
$`x` came from.
-/
theorem setDDI_disjointF
    (A B : Finset α) :
    disjointF (fUnion (fDiff A B) (fDiff B A)) (A ∩ B) :=
  fun _ hxU hxI =>
    match Finset.mem_inter.mp hxI with
    | ⟨hxA, hxB⟩ =>
    (mem_fUnion.mp hxU).elim
      (fun hxAB => (not_mem_right_of_mem_fDiff hxAB) hxB)
      (fun hxBA => (not_mem_right_of_mem_fDiff hxBA) hxA)

/--
# The union partitions into symmetric difference and intersection

**Partition of the union**:

$$`\operatorname{fUnion}(A, B) \;=\; \operatorname{fUnion}\bigl(\operatorname{fUnion}(\operatorname{fDiff}(A, B),\, \operatorname{fDiff}(B, A)),\; A \cap B\bigr)`

The three-block decomposition
$`A \cup B = (A \setminus B) \uplus (B \setminus A) \uplus (A \cap B)`,
proved pointwise by {name}`Finset.ext`. It is the set-level
skeleton of the weight identity {lit}`wt_join_partition_fUnion`.
-/
theorem setU_parF
    (A B : Finset α) :
    fUnion A B = fUnion (fUnion (fDiff A B) (fDiff B A)) (A ∩ B) :=
  Finset.ext fun x =>
    ⟨fun hx => (mem_fUnion.mp hx).elim
      (fun hxA => if hxB : x ∈ B
        then mem_fUnion_right (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
        else mem_fUnion_left (mem_fUnion_left (mem_fDiff_of_mem_of_not_mem hxA hxB)))
      (fun hxB => if hxA : x ∈ A
        then mem_fUnion_right (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
        else mem_fUnion_left (mem_fUnion_right (mem_fDiff_of_mem_of_not_mem hxB hxA))),
     fun hx => (mem_fUnion.mp hx).elim
      (fun hxSym => (mem_fUnion.mp hxSym).elim
        (fun hxAB => mem_fUnion_left (mem_left_of_mem_fDiff hxAB))
        (fun hxBA => mem_fUnion_right (mem_left_of_mem_fDiff hxBA)))
      (fun hxI => match Finset.mem_inter.mp hxI with
        | ⟨hxA, _⟩ => mem_fUnion_left hxA)⟩

/--
# Intersecting the right side preserves disjointness

Disjointness is preserved when the second set is restricted by
intersection:

$$`\operatorname{disjointF}(A, B) \;\implies\; \operatorname{disjointF}(A, B \cap C)`

If $`A` and $`B` share no element, then $`A` and any subset
$`B \cap C \subseteq B` share no element a fortiori. The proof
projects membership in $`B \cap C` to membership in $`B` via
{name}`Finset.mem_inter` before applying the original
disjointness.
-/
theorem setIs_disjointF
    {A B : Finset α}
    (C : Finset α)
    (h : disjointF A B) :
    disjointF A (B ∩ C) :=
  fun x hxA hxBC =>
    match Finset.mem_inter.mp hxBC with
    | ⟨hxB, _⟩ => h x hxA hxB

/--
# $`A \cap B` is disjoint from $`(A \cap C) \setminus B`

$`A \cap B` and $`\operatorname{fDiff}(A \cap C,\, B)` are
disjoint:

$$`\operatorname{disjointF}(A \cap B,\; \operatorname{fDiff}(A \cap C,\, B))`

Both sets restrict to $`A`, but the first demands membership in
$`B` and the second demands non-membership in $`B`; joint
membership would require $`x \in B` and $`x \notin B`
simultaneously. The proof extracts $`x \in B` from the
intersection and $`x \notin B` from the difference, deriving
$`\bot`.
-/
theorem setIID_disjointF
    (A B C : Finset α) :
    disjointF (A ∩ B) (fDiff (A ∩ C) B) :=
  fun _ hxAB hxACnotB =>
    match Finset.mem_inter.mp hxAB with
    | ⟨_, hxB⟩ => (not_mem_right_of_mem_fDiff hxACnotB) hxB

/--
# The parts inside $`A` are disjoint from the parts outside $`A`

The assembled piece inside $`A` is disjoint from the piece outside
$`A`:

$$`\operatorname{disjointF}\bigl(\operatorname{fUnion}(A \cap B,\, \operatorname{fDiff}(A \cap C,\, B)),\; \operatorname{fDiff}(B \cap D,\, A)\bigr)`

Both components of the left union ($`A \cap B` and
$`\operatorname{fDiff}(A \cap C,\, B)`) produce elements in $`A`;
the right difference $`\operatorname{fDiff}(B \cap D,\, A)`
produces elements outside $`A`. Joint membership therefore yields
$`x \in A` and $`x \notin A` simultaneously.
-/
theorem setIIDD_disjointF
    (A B C D : Finset α) :
    disjointF
      (fUnion (A ∩ B) (fDiff (A ∩ C) B))
      (fDiff (B ∩ D) A) :=
  fun _ hxLeft hxRight =>
    (mem_fUnion.mp hxLeft).elim
      (fun hxAB =>
        match Finset.mem_inter.mp hxAB with
        | ⟨hxA, _⟩ => (not_mem_right_of_mem_fDiff hxRight) hxA)
      (fun hxACnotB =>
        match Finset.mem_inter.mp (mem_left_of_mem_fDiff hxACnotB) with
        | ⟨hxA, _⟩ => (not_mem_right_of_mem_fDiff hxRight) hxA)

/--
# A nested assembly is contained in the intersection of the supersets

A nested-intersection assembly is contained in $`C \cap D`, given
$`A \subseteq C` and $`B \subseteq D`:

$$`\operatorname{fUnion}\bigl(\operatorname{fUnion}(A \cap B,\, \operatorname{fDiff}(A \cap D,\, B)),\; \operatorname{fDiff}(B \cap C,\, A)\bigr) \;\subseteq\; C \cap D`

A containment available for re-expressing intersection weights of
checkpoint validator sets under an activated/exited split.
-/
theorem setIIDD_subsetF
    {A B C D : Finset α}
    (hAC : A ⊆ C)
    (hBD : B ⊆ D) :
    fUnion
      (fUnion (A ∩ B) (fDiff (A ∩ D) B))
      (fDiff (B ∩ C) A)
      ⊆ C ∩ D :=
  fun _ hx => (mem_fUnion.mp hx).elim
    (fun hxLeft => (mem_fUnion.mp hxLeft).elim
      (fun hxAB =>
        match Finset.mem_inter.mp hxAB with
        | ⟨hxA, hxB⟩ =>
          Finset.mem_inter.mpr ⟨hAC hxA, hBD hxB⟩)
      (fun hxADnotB =>
        match Finset.mem_inter.mp (mem_left_of_mem_fDiff hxADnotB) with
        | ⟨hxA, hxD⟩ => Finset.mem_inter.mpr ⟨hAC hxA, hxD⟩))
    (fun hxRight =>
      match Finset.mem_inter.mp (mem_left_of_mem_fDiff hxRight) with
      | ⟨hxB, hxC⟩ => Finset.mem_inter.mpr ⟨hxC, hBD hxB⟩)

/--
# $`A \cap C` is disjoint from $`B \setminus C`

$`A \cap C` and $`\operatorname{fDiff}(B, C)` are disjoint:

$$`\operatorname{disjointF}(A \cap C,\; \operatorname{fDiff}(B, C))`

The intersection forces $`x \in C`; the difference forces
$`x \notin C`. Joint membership is therefore contradictory.
-/
theorem setID2_disjointF
    (A B C : Finset α) :
    disjointF (A ∩ C) (fDiff B C) :=
  fun _ hxAC hxBnotC =>
    match Finset.mem_inter.mp hxAC with
    | ⟨_, hxC⟩ => (not_mem_right_of_mem_fDiff hxBnotC) hxC

/--
# A subset splits along a third set

For $`A \subseteq B`, the set $`A` splits along $`C`:

$$`A \subseteq B \;\implies\; A \;\subseteq\; \operatorname{fUnion}(A \cap C,\, \operatorname{fDiff}(B, C))`

Every element of $`A` either lies in $`C` (landing in
$`A \cap C`) or not (and since $`A \subseteq B`, the element
lies in $`B \setminus C`). This is the membership-splitting
principle used in {lit}`wt_meet_subbound_fUnion`.
-/
theorem setID2_subsetF
    {A B : Finset α}
    (C : Finset α)
    (hAB : A ⊆ B) :
    A ⊆ fUnion (A ∩ C) (fDiff B C) :=
  fun _ hxA =>
    if hxC : _ ∈ C
    then mem_fUnion_left (Finset.mem_inter.mpr ⟨hxA, hxC⟩)
    else mem_fUnion_right (mem_fDiff_of_mem_of_not_mem (hAB hxA) hxC)

/--
# Differences through a common intermediary are disjoint

The two differences through a common intermediary are disjoint:

$$`\operatorname{disjointF}(\operatorname{fDiff}(C, B),\; \operatorname{fDiff}(A, C))`

The first difference lies in $`C`
({lit}`mem_left_of_mem_fDiff`); the second lies outside $`C`
({lit}`not_mem_right_of_mem_fDiff`). Joint membership would
require $`x \in C` and $`x \notin C` simultaneously. This is
the disjointness half of the triangle decomposition that
{lit}`fDiff_subset_triangle` uses.
-/
theorem set3D_disjointF
    (A B C : Finset α) :
    disjointF (fDiff C B) (fDiff A C) :=
  fun _ hxCB hxAC =>
    (not_mem_right_of_mem_fDiff hxAC) (mem_left_of_mem_fDiff hxCB)

/--
# Triangle containment (reindexed)

The triangle containment {lit}`fDiff_subset_triangle` with
reindexed arguments:

$$`\operatorname{fDiff}(A, B) \;\subseteq\; \operatorname{fUnion}(\operatorname{fDiff}(C, B),\; \operatorname{fDiff}(A, C))`

Direct application of {lit}`fDiff_subset_triangle` with the
intermediary $`C` placed first.
-/
theorem set3D_subsetF
    (A B C : Finset α) :
    fDiff A B ⊆ fUnion (fDiff C B) (fDiff A C) :=
  fDiff_subset_triangle C A B

end GasperBeaconChain.Core
