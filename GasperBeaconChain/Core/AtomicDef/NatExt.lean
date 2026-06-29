import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Fold

namespace GasperBeaconChain.Core

/-!
# Natural-number extensions

This file provides arithmetic infrastructure for the Casper FFG
formalization: finite-set maximum operations, natural-number
lemmas used in height and quorum arguments, and the abstract
threshold specification.

## Finite maximum (§ 1)

{lit}`foldMaxNat` computes the maximum of a
$`\mathbb{N}`-valued function over a {name}`Finset`, returning
$`0` for the empty set. Its three characterizing lemmas (upper
bound, least upper bound, and attainment) identify it as a
genuine maximum. In the Plausible Liveness development,
{lit}`foldMaxNat` and its bound lemmas underpin
{lit}`highest_target` (the greatest target height of a state),
while {lit}`exists_mem_maximal_by_nat` (an explicit maximizer)
supplies the maximal justification link; the
identity-specialization {lit}`highest` is also provided. The
whole section stays within the choice-free fragment.

## Arithmetic lemmas (§ 2)

Natural-number lemmas in four subsections: height-offset
impossibilities (§ 2A, used in the Plausible Liveness case
analysis to rule out height configurations), a
truncated-subtraction transposition (§ 2B), the
**quorum-intersection arithmetic kernel** (§ 2C, powering
{lit}`quorum_intersection_weight_lower`, the overlap step of the
{lit}`slashable_bound` theorem), and conditional subtraction
associativity (§ 2D).

## Threshold specification (§ 3–5)

An abstract {lit}`Threshold` structure bundles two functions
$`f_{1/3}, f_{2/3} : \mathbb{N} \to \mathbb{N}` with laws:

$$`\begin{aligned} \forall n,\quad n - f_{2/3}(n) &= f_{1/3}(n) \\ \forall n,\quad f_{2/3}(n) &\le n \end{aligned}`

This replaces Coq's global axioms. A canonical implementation
$`f_{2/3}(n) = n - \lfloor n/3 \rfloor = \lceil 2n/3 \rceil` is
provided by {lit}`canonicalThreshold`.

Coq source: {lit}`NatExt.v`.
-/


-- § 1. Finite maximum


/--
The maximum of a $`\mathbb{N}`-valued function over a finite
set, or $`0` for the empty set:

$$`\operatorname{foldMaxNat}(s, f) = \begin{cases} \max_{a \in s} f(a) & s \ne \emptyset \\ 0 & s = \emptyset \end{cases}`

The construction relies on three properties of $`\max` on
$`\mathbb{N}`:

* **Associativity** ($`\max(a, \max(b, c)) = \max(\max(a, b), c)`)
  and **commutativity** ($`\max(a, b) = \max(b, a)`) ensure that
  the iterated application via {name}`Finset.fold` produces the
  same result regardless of the order in which the elements of
  $`s` are enumerated. This is necessary because
  {name}`Finset` does not fix an enumeration order.

* **Identity** ($`\max(a, 0) = a` for all $`a \in \mathbb{N}`):
  the initial value $`0` is neutral under $`\max`, so folding
  over a nonempty set returns $`\max_{a \in s} f(a)` without
  contamination from the seed; for the empty set it returns the
  seed $`0` itself, the only value consistent with an empty
  maximum over $`\mathbb{N}`.

The three theorems
{lit}`le_foldMaxNat_of_mem` (upper bound),
{lit}`foldMaxNat_le_of_forall_le` (least upper bound), and
{lit}`foldMaxNat_mem` (attainment)
jointly establish that this value is the genuine maximum,
not merely a bound but an actual element of the image set
$`f[s] = \{f(a) \mid a \in s\}`.
The construction does not depend on {name}`Classical.choice`.
-/
def foldMaxNat
    {α : Type*}
    [DecidableEq α]
    (s : Finset α)
    (f : α → Nat) : Nat :=
  s.fold max 0 f

/--
The **upper-bound** property: every element's image is
dominated by the finite maximum.

$$`a \in s \;\implies\; f(a) \le \operatorname{foldMaxNat}(s, f)`

Quantified over $`a`, this says
$`\operatorname{foldMaxNat}(s, f)` is an upper bound of the
image $`f[s] = \{f(a) \mid a \in s\}`.

Proved by {name}`Finset.induction_on`.
The base case is vacuous, since no element belongs to
$`\emptyset`.
In the inductive step the fold over
$`\operatorname{insert}\, b\, s'` reduces via
{lit}`Finset.fold_insert` to
$`\max\bigl(f(b),\, \operatorname{foldMaxNat}(s', f)\bigr)`.
A case split on membership in
$`\operatorname{insert}\, b\, s'`
({lit}`Finset.mem_insert`) then gives either
$`f(a) = f(b)`, dominated by {lit}`le_max_left`,
or $`a \in s'`, where the induction hypothesis
$`f(a) \le \operatorname{foldMaxNat}(s', f)` chains through
{lit}`le_max_right`.
-/
theorem le_foldMaxNat_of_mem
    {α : Type*}
    [DecidableEq α]
    {s : Finset α}
    {f : α → Nat}
    {a : α}
    (ha : a ∈ s) :
    f a ≤ foldMaxNat s f :=
  Finset.induction_on s
    (fun hmem => False.elim ((Finset.notMem_empty a) hmem))
    (fun b s' hb ih hmem =>
      show f a ≤ (insert b s').fold max 0 f from
        Eq.subst (motive := fun x => f a ≤ x)
          (Finset.fold_insert (op := max) (b := (0 : Nat)) (f := f) hb).symm
          ((Finset.mem_insert.mp hmem).elim
            (fun h => Eq.subst (motive := fun x => f x ≤ max (f b) (s'.fold max 0 f))
              h.symm (le_max_left _ _))
            (fun has => le_trans (ih has) (le_max_right _ _))))
    ha

/--
The **least-upper-bound** half: any common upper bound $`H` of
the image dominates the finite maximum.

$$`\bigl(\forall\, a \in s,\; f(a) \le H\bigr) \;\implies\; \operatorname{foldMaxNat}(s, f) \le H`

This is the minimality-among-upper-bounds direction:
together with {name}`le_foldMaxNat_of_mem`
(which shows $`\operatorname{foldMaxNat}(s, f)` is *itself*
an upper bound), it characterizes the value as the least
upper bound, i.e. the supremum, of $`f[s]` in
$`(\mathbb{N}, \le)`. The supremum of a subset of a partial
order is unique when it exists.

Proved by {name}`Finset.induction_on`.
The empty fold is $`0`, which is bounded by any $`H`
through {lit}`Nat.zero_le`.
In the insertion step, {lit}`Finset.fold_insert` reduces the
goal to $`\max(f(b),\, \operatorname{foldMaxNat}(s', f)) \le H`,
and {lit}`max_le` combines the hypothesis $`f(b) \le H` with
the induction hypothesis
$`\operatorname{foldMaxNat}(s', f) \le H`.
For $`s = \emptyset`, every $`H` vacuously bounds
$`f[\emptyset]`, and $`0` is the least such bound.
-/
theorem foldMaxNat_le_of_forall_le
    {α : Type*}
    [DecidableEq α]
    {s : Finset α}
    {f : α → Nat}
    {H : Nat}
    (hH : ∀ a ∈ s, f a ≤ H) :
    foldMaxNat s f ≤ H :=
  Finset.induction_on s
    (fun _ => Nat.zero_le _)
    (fun a s' ha ih hH =>
      show (insert a s').fold max 0 f ≤ H from
        Eq.subst (motive := fun x => x ≤ H)
          (Finset.fold_insert (op := max) (b := (0 : Nat)) (f := f) ha).symm
          (max_le
            (hH a (Finset.mem_insert_self a s'))
            (ih fun x hx => hH x (Finset.mem_insert_of_mem hx))))
    hH

/--
The **attainment** property: over a nonempty finite set, the
maximum computed by {name}`foldMaxNat` equals $`f(a)` for some
$`a \in s`.

$$`s \ne \emptyset \;\implies\; \exists\, a \in s,\;\; \operatorname{foldMaxNat}(s, f) = f(a)`

This depends on $`\le` on $`\mathbb{N}` being a *total*
order; it would fail for a general partial order.
In the powerset of a set ordered by inclusion, for instance,
the least upper bound of $`\{A, B\}` is $`A \cup B`,
typically distinct from both $`A` and $`B`,
so the supremum of a finite family need not be one of its
members. Totality closes this gap.

Because $`\le` is total, $`\max` is *selective*:
for any two values, $`\max(a, b)` equals either $`a` or
$`b` ({lit}`Nat.le_total` decides which,
and {lit}`max_eq_left` / {lit}`max_eq_right` produce the
equality).
This selectivity propagates through the fold:
each insertion step either keeps the old maximizer or
replaces it with the new element, so the fold result is
always the value of $`f` at some element of $`s`.
(When $`s'` is empty, the fold returns
$`\max(f(b), 0) = f(b)` by {lit}`Nat.max_zero`.)

Nonemptiness is required because the fold over $`\emptyset`
returns $`0`, which need not be a value of $`f`.

Together with {name}`le_foldMaxNat_of_mem` (upper bound) and
{name}`foldMaxNat_le_of_forall_le` (least upper bound), this
completes the characterization of $`\operatorname{foldMaxNat}`
as the genuine maximum of $`f` over $`s`.

The proof proceeds by induction on a strengthened statement:
for every finite set, either the set is empty or its maximum
is attained. The nonemptiness hypothesis then selects the
attained case.

The result is the fold-based counterpart of
Mathlib's {lit}`Finset.max'_mem`, which states the same
attainment fact for {lit}`Finset.max'`,
the maximum of a nonempty finset over a linear order.
-/
theorem foldMaxNat_mem
    {α : Type*}
    [DecidableEq α]
    {f : α → Nat}
    {s : Finset α}
    (hne : s.Nonempty) :
    ∃ a, a ∈ s ∧ foldMaxNat s f = f a :=
  have helper : ∀ s : Finset α,
      s = ∅ ∨ (∃ a, a ∈ s ∧ foldMaxNat s f = f a) :=
    fun s => Finset.induction_on s (Or.inl rfl)
      (fun b s' hb ih =>
        Or.inr (show ∃ a, a ∈ insert b s' ∧ (insert b s').fold max 0 f = f a from
          have hfold_ins : (insert b s').fold max 0 f = max (f b) (s'.fold max 0 f) :=
            Finset.fold_insert (op := max) (b := (0 : Nat)) (f := f) hb
          match ih with
          | Or.inl hs_empty =>
            have hfold_zero : s'.fold max 0 f = 0 :=
              Eq.subst (motive := fun s => s.fold max 0 f = 0) hs_empty.symm rfl
            ⟨b, Finset.mem_insert_self b s',
              hfold_ins.trans ((congrArg (max (f b)) hfold_zero).trans (Nat.max_zero (f b)))⟩
          | Or.inr ⟨c, hc_mem, hc_eq⟩ =>
            (Nat.le_total (f b) (f c)).elim
              (fun hbc => ⟨c, Finset.mem_insert.mpr (Or.inr hc_mem),
                hfold_ins.trans ((congrArg (max (f b)) hc_eq).trans (max_eq_right hbc))⟩)
              (fun hcb => ⟨b, Finset.mem_insert_self b s',
                hfold_ins.trans ((congrArg (max (f b)) hc_eq).trans (max_eq_left hcb))⟩)))
  match helper s, hne with
  | Or.inl hs_empty, ⟨a, ha⟩ =>
      False.elim ((Finset.notMem_empty a)
        (Eq.subst (motive := fun s => a ∈ s) hs_empty ha))
  | Or.inr result, _ => result

/--
The greatest element of a finite set of natural numbers, or
$`0` for the empty set. This is the special case
$`f = \operatorname{id}` of {name}`foldMaxNat`:

$$`\operatorname{highest}(A) \;\;\coloneqq\;\; \operatorname{foldMaxNat}(A, \operatorname{id}) \;=\; \begin{cases} \max_{x \in A} x & A \ne \emptyset \\ 0 & A = \emptyset \end{cases}`

The two facts {lit}`highest_ub` and {lit}`highest_mem`
specialize the characterizing lemmas of {name}`foldMaxNat`
to $`f = \operatorname{id}`: the former is the upper-bound
property, the latter attainment.
The value $`0` on $`\emptyset` matches Coq's {lit}`\max_`
big-operator over an empty index.
-/
def highest (A : Finset Nat) : Nat :=
  foldMaxNat A id

/--
Every element of $`A` is at most $`\operatorname{highest}(A)`:

$$`x \in A \;\implies\; x \le \operatorname{highest}(A)`

The upper-bound property of {name}`highest`, obtained from
{name}`le_foldMaxNat_of_mem` at $`f = \operatorname{id}`.
-/
theorem highest_ub
    {A : Finset Nat}
    {x : Nat}
    (hx : x ∈ A) :
    x ≤ highest A :=
  show id x ≤ foldMaxNat A id from le_foldMaxNat_of_mem hx

/--
For a nonempty set, $`\operatorname{highest}(A)` is achieved, i.e. it belongs
to $`A`:

$$`A \ne \emptyset \;\implies\; \operatorname{highest}(A) \in A`

The attainment property of {name}`highest`: it is genuinely
the maximum value, an actual element of $`A` and not merely
an upper bound.
Obtained from {name}`foldMaxNat_mem` at
$`f = \operatorname{id}`. Replaces {lit}`Finset.max'_mem`.
-/
theorem highest_mem
    {A : Finset Nat}
    (hne : A.Nonempty) :
    highest A ∈ A :=
  show foldMaxNat A id ∈ A from
    match foldMaxNat_mem (f := id) hne with
    | ⟨_, ha_mem, ha_eq⟩ =>
        Eq.subst (motive := fun x => x ∈ A) ha_eq.symm ha_mem

/--
The **finite maximizer theorem**: any $`\mathbb{N}`-valued
function on a nonempty finite set attains a global maximum at
some point of its domain.

$$`s \ne \emptyset \;\implies\; \exists\, a \in s,\; \forall\, b \in s,\; f(b) \le f(a)`

This is the order-theoretic, finite counterpart of the
extreme value theorem: where the classical statement needs
a compact domain and a continuous function, finiteness of
$`s` alone suffices.
The totality of $`\le` on $`\mathbb{N}`
(through {name}`foldMaxNat_mem`) ensures the maximum equals
some $`f(a)` with $`a \in s`, rather than lying strictly
above every image value.

The witness is constructed explicitly:
{name}`foldMaxNat_mem` provides a point $`a \in s` at which
the fold is attained, and {name}`le_foldMaxNat_of_mem` shows
that value dominates $`f(b)` for every $`b \in s`,
so $`a` is a global maximizer.
The maximum value is computed by a single fold over $`s`,
so the family of values $`\{f(a) \mid a \in s\}` is never
formed as a set in its own right.
It is the fold-based counterpart of
Mathlib's {lit}`Finset.exists_max_image`,
which instead maximizes over that family once it has been
built as a finite set.
-/
theorem exists_mem_maximal_by_nat
    {α : Type*}
    [DecidableEq α]
    (s : Finset α)
    (f : α → Nat)
    (hne : s.Nonempty) :
    ∃ a, a ∈ s ∧ ∀ b ∈ s, f b ≤ f a :=
  match foldMaxNat_mem (f := f) hne with
  | ⟨a, ha_mem, ha_eq⟩ =>
    ⟨a, ha_mem, fun b hb =>
      Eq.subst (motive := fun x => f b ≤ x) ha_eq (le_foldMaxNat_of_mem hb)⟩


-- § 2. Arithmetic lemmas (Coq NatExt.v)


/--
Every natural number is at most its successor:

$$`\neg\,(n + 1 < n)`

Equivalently $`n \le n + 1`, i.e. the successor map is
inflationary ($`x \le \operatorname{succ}(x)` for every $`x`).
The proof applies {lit}`Nat.not_lt`
($`\neg(a < b) \iff b \le a`) to convert the goal to
$`n \le n + 1`, then discharges it with {lit}`Nat.le_succ`.
Prop-valued counterpart of Coq's
{lit}`(n.+1 < n) = false`.
-/
theorem ltSnn (n : Nat) :
    ¬ Nat.succ n < n :=
  Nat.not_lt.mpr (Nat.le_succ n)

/--
The initial segment $`\{n \in \mathbb{N} \mid n \le 1\}` has
exactly two elements:

$$`n \le 1 \;\implies\; n = 0 \;\lor\; n = 1`

Proved by pattern-matching on $`n`: the bound $`n \le 1`
restricts the match to the two constructors $`0` and $`1`.
Used in the $`k = 1` case of
{lit}`finalized_means_one_finalized`, where it splits the
universal quantifier over $`n \le 1` into two concrete cases.
-/
theorem leq_one_means_zero_or_one
    {n : Nat}
    (h : n ≤ 1) :
    n = 0 ∨ n = 1 :=
  match n, h with
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl

/--
Self-subtraction annihilates to $`0`:

$$`n - n = 0`

This is the cancellation law for truncated subtraction on
$`\mathbb{N}` — the analogue of $`a - a = 0` in $`\mathbb{Z}`,
which holds here because $`n \le n`. Wrapper for
{lit}`Nat.sub_self`.
-/
theorem sub_eq (n : Nat) :
    n - n = 0 :=
  Nat.sub_self n

/--
Successor minus self equals $`1`:

$$`(n + 1) - n = 1`

The companion of {name}`sub_eq`: where $`n - n = 0`, here
$`(n + 1) - n = 1`. It needs an explicit proof because truncated
subtraction recurses on its second argument, so $`n + 1 - n` does
not reduce while $`n` is an abstract variable — the equation is
not definitional. Wraps {lit}`Nat.add_sub_cancel_left`.
-/
theorem add_one_sub_self (n : Nat) :
    n + 1 - n = 1 :=
  Nat.add_sub_cancel_left n 1


-- § 2A. Height lemmas for H, H+1, H+2
--
-- These lemmas eliminate impossible orderings among the three
-- consecutive heights H, H+1, H+2. They are consumed by the
-- Plausible Liveness case analysis
-- (no_new_surround_vote_two_link_extension and
-- no_new_double_vote_two_link_extension), which must show that
-- extending a state with two new supermajority links (at target
-- heights H+1 and H+2) introduces no new slashing. The case
-- split produces sub-goals whose hypotheses place a vote's target
-- height in one of the three slots; these lemmas discharge the
-- contradictory combinations.


/--
$$`\neg\,(H + 2 \le H)`

If $`H + 2 \le H` held, then by $`H + 1 \le H + 2`
(inflationary property of successor) and transitivity we would
get $`H + 1 \le H`, contradicting
{lit}`Nat.not_add_one_le_self`.
-/
theorem not_add_two_le_self (H : Nat) :
    ¬ H + 2 ≤ H :=
  fun h => Nat.not_add_one_le_self H
    (Nat.le_trans (Nat.le_add_right (H + 1) 1) h)

/--
$$`x \le H \;\implies\; \neg\,(H + 1 < x)`

Assuming $`H + 1 < x`, {lit}`Nat.le_of_lt` gives
$`H + 1 \le x`, and the hypothesis $`x \le H` yields
$`H + 1 \le H` by transitivity — contradicting
{lit}`Nat.not_add_one_le_self`.
-/
theorem not_add_one_lt_of_le {H x : Nat} (hx : x ≤ H) :
    ¬ H + 1 < x :=
  fun h => Nat.not_add_one_le_self H (Nat.le_trans (Nat.le_of_lt h) hx)

/--
$$`x \le H \;\implies\; \neg\,(H + 2 < x)`

Assuming $`H + 2 < x`, {lit}`Nat.le_of_lt` gives
$`H + 2 \le x`, and the hypothesis $`x \le H` yields
$`H + 2 \le H` by transitivity — contradicting
{name}`not_add_two_le_self`.
-/
theorem not_add_two_lt_of_le {H x : Nat} (hx : x ≤ H) :
    ¬ H + 2 < x :=
  fun h => not_add_two_le_self H (Nat.le_trans (Nat.le_of_lt h) hx)

/--
$$`\neg\,(H + 2 < H + 1)`

Since $`H + 1 \le (H + 1) + 1 = H + 2`
({lit}`Nat.le_add_right`), the strict reverse $`H + 2 < H + 1`
is impossible. Proved via {lit}`Nat.not_lt_of_ge`.
-/
theorem not_add_two_lt_add_one (H : Nat) :
    ¬ H + 2 < H + 1 :=
  Nat.not_lt_of_ge (Nat.le_add_right (H + 1) 1)

/--
$$`H + 1 \ne H + 2`

Strict inequality $`H + 1 < H + 2` (from $`0 < 1`) implies
distinctness. Proved via {lit}`Nat.ne_of_lt`.
-/
theorem add_one_ne_add_two (H : Nat) :
    H + 1 ≠ H + 2 :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_right Nat.one_pos)

/--
$$`H + 2 \ne H + 1`

Symmetric form of {name}`add_one_ne_add_two`.
-/
theorem add_two_ne_add_one (H : Nat) :
    H + 2 ≠ H + 1 :=
  (add_one_ne_add_two H).symm


-- § 2B. Truncated-subtraction transposition


/--
A **transposition lemma** for truncated subtraction on
$`\mathbb{N}`:

$$`A - I \le E + L \;\implies\; A - L - E \le I`

Over $`\mathbb{N}` both the premise and the conclusion are
equivalent to the single additive bound
$`A \le I + E + L`:
the two directions of $`a - b \le c \iff a \le b + c`
are {lit}`Nat.le_add_of_sub_le` and
{lit}`Nat.sub_le_of_le_add`, mutually inverse.
So this is one direction of a transposition,
not a strengthening.
Despite its shape it is *not* an instance of the
(reverse) triangle inequality
$`\bigl|\,|x| - |y|\,\bigr| \le |x \pm y|`,
which is a metric statement of a different kind.

In {lit}`validator_intersection_lower_bound` (a lemma of the
{lit}`slashable_bound` development), $`A` is the total weight of
a validator set, $`I` the intersection weight of two validator
sets, and $`E`, $`L` the weights of validators activated or
exited between two checkpoints. The premise $`A - I \le E + L`
bounds the non-intersecting portion $`A - I` of $`A` by the
churn $`E + L`; the conclusion $`A - L - E \le I` re-expresses
the same fact as a lower bound on the intersection weight $`I`,
the form the quorum-intersection argument consumes. The proof
turns the premise into $`A \le I + (E + L)`
({lit}`Nat.le_add_of_sub_le`, with {lit}`Nat.add_comm`), peels
off $`E + L` by {lit}`Nat.sub_le_of_le_add`, and rewrites
$`A - L - E = A - (L + E)` ({lit}`Nat.sub_sub`) after reordering
$`E + L` to $`L + E` ({lit}`Nat.add_comm`).
-/
theorem nat_sub_sub_le_of_sub_le_add
    {A I E L : Nat}
    (h : A - I ≤ E + L) :
    A - L - E ≤ I :=
  have hA : A ≤ I + (E + L) :=
    (Nat.le_add_of_sub_le h).trans (Nat.le_of_eq (Nat.add_comm (E + L) I))
  Eq.subst (motive := fun x => x ≤ I) (Nat.sub_sub A L E).symm
    (Eq.subst (motive := fun x => A - x ≤ I) (Nat.add_comm L E).symm
      (Nat.sub_le_of_le_add hA))


-- § 2C. Quorum-intersection arithmetic kernel


/--
Pre-subtraction form of the **quorum-intersection arithmetic
kernel**, the purely arithmetic skeleton of
{lit}`quorum_intersection_weight_lower` (the quorum-overlap step
of the {lit}`slashable_bound` theorem):

$$`\begin{gathered} A + B = U + I \;\;\wedge\;\; A = O_L + T_L \;\;\wedge\;\; B = O_R + T_R \;\;\wedge\;\; T_L + T_R \le Q + U \\ \implies\;\; I \le Q + (O_L + O_R) \end{gathered}`

Its intended instantiation, from
{lit}`quorum_intersection_weight_lower`, reads as follows.
$`A` and $`B` are the total weights of two validator sets, and
$`U`, $`I` are the weights of their union and intersection — so
$`A + B = U + I` is inclusion–exclusion. Each set weight splits
through the threshold as $`A = O_L + T_L` with $`O_L = f_{1/3}(A)`
(the one-third part) and $`T_L = f_{2/3}(A)` (the two-thirds
part), and likewise for $`B` (see
{lit}`threshold_decomposition`). $`Q` is the weight of the
intersection of two quorums — the set ultimately shown to be
slashed. The premise $`T_L + T_R \le Q + U` records that the two
quorum thresholds, each met by an actual quorum, together fit
within the quorum intersection plus the set union (again
inclusion–exclusion, now on the quorums, since each quorum lies
in its set). The conclusion $`I \le Q + (O_L + O_R)` then
lower-bounds the slashed weight $`Q` by the set-intersection
weight minus the two one-thirds.

The derivation rewrites the left-hand side:

1. $`(T_L + T_R) + (O_L + O_R) = (O_L + T_L) + (O_R + T_R) = A + B = U + I`
2. from $`T_L + T_R \le Q + U`, $`U + I \le U + (Q + (O_L + O_R))`
3. cancel $`U`: $`I \le Q + (O_L + O_R)`
-/
theorem nat_quorum_intersection_arith_prebound
    {A B I U Q TL TR OL OR : Nat}
    (hAB : A + B = U + I)
    (hA : A = OL + TL)
    (hB : B = OR + TR)
    (hT : TL + TR ≤ Q + U) :
    I ≤ Q + (OL + OR) :=
  have hSO : (TL + TR) + (OL + OR) = U + I :=
    calc (TL + TR) + (OL + OR)
        = TL + (TR + (OL + OR)) := Nat.add_assoc TL TR (OL + OR)
      _ = TL + (OL + (TR + OR)) :=
          congrArg (TL + ·) (Nat.add_left_comm TR OL OR)
      _ = (TL + OL) + (TR + OR) := (Nat.add_assoc TL OL (TR + OR)).symm
      _ = (OL + TL) + (TR + OR) :=
          congrArg (· + (TR + OR)) (Nat.add_comm TL OL)
      _ = (OL + TL) + (OR + TR) :=
          congrArg ((OL + TL) + ·) (Nat.add_comm TR OR)
      _ = A + B := congrArg₂ (· + ·) hA.symm hB.symm
      _ = U + I := hAB
  Nat.le_of_add_le_add_left
    (calc U + I
        = (TL + TR) + (OL + OR) := hSO.symm
      _ ≤ (Q + U) + (OL + OR) := Nat.add_le_add_right hT _
      _ = Q + (U + (OL + OR)) := Nat.add_assoc Q U (OL + OR)
      _ = U + (Q + (OL + OR)) := Nat.add_left_comm Q U (OL + OR))

/--
Joined-subtraction form of the quorum-intersection arithmetic:

$$`I - (O_L + O_R) \le Q`

Derived from {name}`nat_quorum_intersection_arith_prebound` by
{lit}`Nat.sub_le_of_le_add`.
-/
theorem nat_quorum_intersection_arith_joined
    {A B I U Q TL TR OL OR : Nat}
    (hAB : A + B = U + I)
    (hA : A = OL + TL)
    (hB : B = OR + TR)
    (hT : TL + TR ≤ Q + U) :
    I - (OL + OR) ≤ Q :=
  Nat.sub_le_of_le_add (nat_quorum_intersection_arith_prebound hAB hA hB hT)

/--
Iterated-subtraction form of the quorum-intersection lower
bound:

$$`I - O_L - O_R \le Q`

The kernel has three logically equivalent renderings —
{name}`nat_quorum_intersection_arith_prebound` (purely additive:
$`I \le Q + (O_L + O_R)`),
{name}`nat_quorum_intersection_arith_joined` (one truncated
subtraction: $`I - (O_L + O_R) \le Q`), and this iterated form
($`I - O_L - O_R \le Q`). They form a derivation chain: the
additive prebound is proved first, the joined form repackages it
with one truncated subtraction via {lit}`Nat.sub_le_of_le_add`,
and this iterated form follows by the identity
$`a - (b + c) = a - b - c` ({lit}`Nat.sub_sub`); the additive
and subtractive shapes are linked by the mutually inverse pair
{lit}`Nat.sub_le_of_le_add` / {lit}`Nat.le_add_of_sub_le`. This
iterated form is the one applied in
{lit}`quorum_intersection_weight_lower`, which concludes that
the slashed quorum-intersection weight $`Q` is at least
$`I - O_L - O_R` — the set-intersection weight less the two
one-third parts.
-/
theorem nat_quorum_intersection_arith
    {A B I U Q TL TR OL OR : Nat}
    (hAB : A + B = U + I)
    (hA : A = OL + TL)
    (hB : B = OR + TR)
    (hT : TL + TR ≤ Q + U) :
    I - OL - OR ≤ Q :=
  Eq.subst (motive := fun x => x ≤ Q) (Nat.sub_sub I OL OR).symm
    (nat_quorum_intersection_arith_joined hAB hA hB hT)


-- § 2D. Conditional subtraction associativity (Coq NatExt.v)


/--
Conditional associativity of addition and truncated subtraction
over the naturals:

$$`p \le m \;\implies\; (n + m) - p = n + (m - p)`

Over $`\mathbb{Z}` this identity is unconditional; over
$`\mathbb{N}` the side condition $`p \le m` is exactly what
prevents the inner difference $`m - p` from being truncated to
$`0`, which would otherwise discard the part of $`p` that ought
to borrow from $`n`. Wrapper for {lit}`Nat.add_sub_assoc`.
Coq: {lit}`addnDAr`.
-/
theorem addnDAr
    (n m p : Nat)
    (h : p ≤ m) :
    (n + m) - p = n + (m - p) :=
  Nat.add_sub_assoc h n


-- § 3. Threshold specification (abstract)


/--
{lit}`Threshold` packages a minimal arithmetic interface for the
quorum-intersection arguments — a pair of functions
$`f_{1/3}, f_{2/3} : \mathbb{N} \to \mathbb{N}` constrained by two
laws.

# Data

Two functions $`f_{1/3}` ({lit}`one_third`) and $`f_{2/3}`
({lit}`two_third`), both of type $`\mathbb{N} \to \mathbb{N}`.

# Laws

$$`\begin{aligned} \forall n,\quad n - f_{2/3}(n) &= f_{1/3}(n) & \text{(complementarity)} \\ \forall n,\quad f_{2/3}(n) &\le n & \text{(boundedness)} \end{aligned}`

These are carried by the fields {lit}`thirds_def` and
{lit}`leq_two_thirds` respectively. The subtraction is the
truncated subtraction of $`\mathbb{N}`, which is why boundedness
is an independent assumption rather than a consequence.

# Intended semantics

In the BFT reading, $`f_{2/3}(n)` is *intended to represent* a
quorum threshold for a validator set of total weight $`n` (a
subset whose aggregate weight reaches $`f_{2/3}(n)` is meant to
count as a $`\frac{2}{3}`-quorum), and $`f_{1/3}(n)` its
complementary residual — the weight notionally available to
Byzantine participants. These readings are the *purpose* of the
interface, not facts the two laws by themselves establish (see
**Non-assumptions**).

# Derived consequences

From the two laws alone one derives the additive decomposition

$$`n = f_{1/3}(n) + f_{2/3}(n)`

(see {lit}`threshold_decomposition`); this is the only threshold
fact the arithmetic lemmas in this file require. It is the
algebraic basis of the quorum-intersection argument: two
$`\frac{2}{3}`-quorums $`A, B` of a validator set of weight $`n`
satisfy, by inclusion–exclusion,

$$`\operatorname{wt}(A \cap B) \;=\; \operatorname{wt}(A) + \operatorname{wt}(B) - \operatorname{wt}(A \cup B) \;\ge\; 2\,f_{2/3}(n) - n \;=\; f_{2/3}(n) - f_{1/3}(n)`

lower-bounding the intersection weight. This bound is non-trivial
only when $`f_{2/3}(n) > f_{1/3}(n)`, a property of *specific
instances* (it holds for {lit}`canonicalThreshold` at $`n > 0`),
not of the bare interface. The {lit}`slashable_bound` theorem
establishes the corresponding bound for dynamic validator sets,
where $`A` and $`B` are drawn from sets that may differ.

# Non-assumptions

The two laws do *not* by themselves assert:

* monotonicity of either $`f_{1/3}` or $`f_{2/3}`;
* any exact floor/ceiling formula, e.g.
  $`f_{2/3}(n) = \lceil 2n/3 \rceil`;
* minimality of $`f_{2/3}(n)` among quorum thresholds, or that the
  intended quorum/Byzantine reading is *forced* rather than merely
  consistent;
* positivity or strict overlap $`f_{2/3}(n) > f_{1/3}(n)`, which
  already fails at $`n = 0`.

Such stronger facts must be proved separately for concrete
implementations such as {lit}`canonicalThreshold`.

# Provenance

This first-class value replaces Coq's global axioms for
{lit}`one_third` and {lit}`two_third`.
-/
structure Threshold where
  one_third : Nat → Nat
  two_third : Nat → Nat
  thirds_def : ∀ n, n - two_third n = one_third n
  leq_two_thirds : ∀ n, two_third n ≤ n


-- § 4. Canonical threshold implementation


/--
The standard BFT two-thirds threshold, expressing the minimum
quorum size as a function of total validator weight:

$$`\operatorname{canonical\_two\_third}(n) \;\;\coloneqq\;\; n - \lfloor n / 3 \rfloor \;=\; \lceil 2n/3 \rceil`

The identity $`n - \lfloor n/3 \rfloor = \lceil 2n/3 \rceil`
follows from the division algorithm: writing $`n = 3q + r`
with $`r \in \{0, 1, 2\}`, both sides equal $`2q + r` when
$`r \le 1` and $`2q + 2` when $`r = 2`.
-/
def canonical_two_third (n : Nat) : Nat :=
  n - n / 3

/--
The one-third complement of {name}`canonical_two_third`,
giving the maximum tolerable Byzantine weight:

$$`\operatorname{canonical\_one\_third}(n) \;\;\coloneqq\;\; n - (n - \lfloor n/3 \rfloor) \;=\; \lfloor n/3 \rfloor`

The simplification $`n - (n - \lfloor n/3 \rfloor) = \lfloor n/3 \rfloor`
holds because $`\lfloor n/3 \rfloor \le n` for all
$`n \in \mathbb{N}`.
-/
def canonical_one_third (n : Nat) : Nat :=
  n - canonical_two_third n

/--
The canonical {name}`Threshold` instance with
$`f_{2/3}(n) = n - \lfloor n/3 \rfloor` and
$`f_{1/3}(n) = \lfloor n/3 \rfloor`.

Both laws are proved, not assumed. {lit}`thirds_def` holds by
definitional reduction ({lit}`rfl`): with this choice of
$`f_{2/3}`, the field $`f_{1/3}` is *defined* as
$`n - f_{2/3}(n)`, so $`n - f_{2/3}(n) = f_{1/3}(n)` is true by
unfolding. {lit}`leq_two_thirds` holds because truncated
subtraction never exceeds its minuend — $`n - \lfloor n/3 \rfloor \le n`,
i.e. {lit}`Nat.sub_le` — independently of the value of
$`\lfloor n/3 \rfloor`.
-/
def canonicalThreshold : Threshold where
  one_third := canonical_one_third
  two_third := canonical_two_third
  thirds_def := fun _ => rfl
  leq_two_thirds := fun n => Nat.sub_le n (n / 3)


-- § 5. Derived threshold lemmas


/--
**Additive decomposition** of the total weight by the threshold
functions:

$$`n = f_{1/3}(n) + f_{2/3}(n)`

The total weight of any validator set splits exactly into the
Byzantine tolerance $`f_{1/3}(n)` and the quorum threshold
$`f_{2/3}(n)`. This is the additive rearrangement of the
defining law $`n - f_{2/3}(n) = f_{1/3}(n)` (the
{lit}`thirds_def` field of {name}`Threshold`), using the bound
$`f_{2/3}(n) \le n` ({lit}`leq_two_thirds`) to convert the
truncated subtraction into a genuine equality.
-/
theorem threshold_decomposition
    (τ : Threshold)
    (n : Nat) :
    n = τ.one_third n + τ.two_third n :=
  Nat.eq_add_of_sub_eq (τ.leq_two_thirds n) (τ.thirds_def n)

/--
The combined two-thirds threshold of two validator sets, of
weights $`n` and $`m`, never exceeds their combined weight:

$$`f_{2/3}(n) + f_{2/3}(m) \le n + m`

This is the two-set form of {lit}`leq_two_thirds`: it bounds the
sum of two quorum thresholds by the combined total weight of the
two validator sets.

Obtained by adding the two instances $`f_{2/3}(n) \le n` and
$`f_{2/3}(m) \le m` of {lit}`leq_two_thirds` (monotonicity of
$`+` with respect to $`\le`, {lit}`Nat.add_le_add`). Coq:
{lit}`wt_two_thirds_sum`.
-/
theorem wt_two_thirds_sum
    (τ : Threshold)
    (n m : Nat) :
    τ.two_third n + τ.two_third m ≤ n + m :=
  Nat.add_le_add (τ.leq_two_thirds n) (τ.leq_two_thirds m)

end GasperBeaconChain.Core
