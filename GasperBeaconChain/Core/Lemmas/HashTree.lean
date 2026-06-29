import GasperBeaconChain.Core.AtomicDef.HashTree

universe u

namespace GasperBeaconChain.Core

/-!
# Structural lemmas for ancestry

This file collects the closure properties of the two ancestry
relations defined in {lit}`AtomicDef/HashTree.lean`:
the ungraded {name}`hash_ancestor` ($`\xrightarrow{*}`) and
the distance-indexed {name}`nth_ancestor` ($`\xrightarrow{n}`).

## Closure properties of $`\xrightarrow{*}`

The relation {name}`hash_ancestor` satisfies:

* **Reflexivity** — {lit}`hash_self_ancestor`:
  $`h \xrightarrow{*} h`
* **Transitivity** — {lit}`hash_ancestor_concat`:
  $`h_1 \xrightarrow{*} h_2 \xrightarrow{*} h_3 \implies h_1 \xrightarrow{*} h_3`
* **One-step extension** on either end —
  {lit}`hash_ancestor_stepL` (prepend a parent edge) and
  {lit}`hash_ancestor_stepR` (append; the {lit}`step` constructor
  itself)
* **Proper embedding of a parent edge** —
  {lit}`hash_parent_ancestor`:
  a single parent edge $`h_1 \to h_2` gives both ancestry and
  distinctness $`h_1 \ne h_2` (from irreflexivity of
  {name}`hash_parent_irreflexive`)

## Conflict propagation

{lit}`hash_ancestor_conflict` is the *contrapositive of
transitivity*: if $`h_1 \xrightarrow{*} h_2` and $`p` is *not*
an ancestor of $`h_2`, then $`p` is not an ancestor of $`h_1`
either. Together with {lit}`hash_nonancestor_nonequal`
(non-ancestry implies distinctness), this lets the safety proofs
rule out branch configurations by propagating non-ancestry upward
along justification chains.

## Graded–ungraded interface

* {lit}`nth_ancestor_ancestor` — forgets the distance index:
  $`\xrightarrow{n}` implies $`\xrightarrow{*}`
* {lit}`nth_ancestor_0_refl` — distance $`0` forces equality
* {lit}`parent_ancestor` — a parent edge is exactly distance-$`1`
  ancestry ($`\leftrightarrow`)
* {lit}`nth_ancestor_succ_inv` — successor inversion: a
  distance-$`(n+1)` chain decomposes as a distance-$`n` chain
  followed by one parent edge, extracting the penultimate block

## Downstream use

The conflict lemmas feed the safety case analysis in
{lit}`Theories/AccountableSafety.lean`
({lit}`k_safety'`, {lit}`k_non_equal_height_case_ind`);
{lit}`parent_ancestor` and {lit}`nth_ancestor_succ_inv` feed
the finalization bridge {lit}`finalized_means_one_finalized` and
the block-existence extraction
{lit}`blocks_exist_extract_new_final_pair_from_bound`.
-/

variable {Hash : Type u}
variable {parent : HashParent Hash}

/--
# Every block is its own ancestor

Reflexivity of the ancestry relation $`\xrightarrow{*}`:

$$`\forall\, h,\; h \xrightarrow{*} h`

Every block is its own ancestor — the zero-length path. This is
the {lit}`refl` constructor of {name}`hash_ancestor`, exposed as a
lemma. It is the base case for any ancestry argument: in
particular, it supplies the starting path in
{lit}`hash_ancestor_stepL` and {lit}`hash_parent_ancestor`.
-/
theorem hash_self_ancestor (h : Hash) :
    hash_ancestor parent h h :=
  hash_ancestor.refl h

/--
# A parent edge is a proper ancestry step

A parent edge gives ancestry *and* distinctness: from $`h_1 \to h_2`
together with the irreflexivity hypothesis on the parent relation,

$$`h_1 \xrightarrow{*} h_2 \;\wedge\; h_1 \ne h_2`

The ancestry half comes from one {lit}`step` over {lit}`refl`;
the distinctness half is exactly {name}`hash_parent_irreflexive`
applied to the edge.
-/
theorem hash_parent_ancestor
    (hirr : hash_parent_irreflexive parent)
    {h₁ h₂ : Hash}
    (hp : parent h₁ h₂) :
    hash_ancestor parent h₁ h₂ ∧ h₁ ≠ h₂ :=
  ⟨hash_ancestor.step (hash_ancestor.refl h₁) hp, hirr hp⟩

/--
# Ancestry paths compose by transitivity

Transitivity of $`\xrightarrow{*}`:

$$`h_1 \xrightarrow{*} h_2 \;\wedge\; h_2 \xrightarrow{*} h_3 \;\implies\; h_1 \xrightarrow{*} h_3`

Proved by induction on the second path $`h_2 \xrightarrow{*} h_3`,
extending $`h_1 \xrightarrow{*} h_2` one edge at a time via the
{lit}`step` constructor. The base case ({lit}`refl`) returns the
first path unchanged.
-/
theorem hash_ancestor_concat
    {h₁ h₂ h₃ : Hash}
    (h12 : hash_ancestor parent h₁ h₂)
    (h23 : hash_ancestor parent h₂ h₃) :
    hash_ancestor parent h₁ h₃ :=
  match h23 with
  | .refl _ => h12
  | .step h23' hp => hash_ancestor.step (hash_ancestor_concat h12 h23') hp

/--
# Prepending a parent edge extends ancestry

Prepend a parent edge on the **left**: $`h_1 \to h_2` and
$`h_2 \xrightarrow{*} h_3` give $`h_1 \xrightarrow{*} h_3`.
Obtained by concatenating the single-step path
$`h_1 \xrightarrow{*} h_2` (from {lit}`step` over {lit}`refl`)
with the given path via {lit}`hash_ancestor_concat`.
-/
theorem hash_ancestor_stepL
    {h₁ h₂ h₃ : Hash}
    (hp : parent h₁ h₂)
    (ha : hash_ancestor parent h₂ h₃) :
    hash_ancestor parent h₁ h₃ :=
  hash_ancestor_concat (hash_ancestor.step (hash_ancestor.refl h₁) hp) ha

/--
# Appending a parent edge extends ancestry

Append a parent edge on the **right**: $`h_1 \xrightarrow{*} h_2`
and $`h_2 \to h_3` give $`h_1 \xrightarrow{*} h_3`. This is
the {lit}`step` constructor of {name}`hash_ancestor` exposed as a
lemma.
-/
theorem hash_ancestor_stepR
    {h₁ h₂ h₃ : Hash}
    (ha : hash_ancestor parent h₁ h₂)
    (hp : parent h₂ h₃) :
    hash_ancestor parent h₁ h₃ :=
  hash_ancestor.step ha hp

/--
# Non-ancestors are distinct blocks

Non-ancestry implies distinctness:

$$`\neg\,(h_1 \xrightarrow{*} h_2) \;\implies\; h_1 \ne h_2`

The contrapositive of reflexivity: if $`h_1 = h_2` held, then
$`h_1 \xrightarrow{*} h_1` (by {lit}`hash_self_ancestor`)
would be transported via {lit}`Eq.subst` to
$`h_1 \xrightarrow{*} h_2`, contradicting the non-ancestry
hypothesis. Used in {lit}`k_safety'` to derive $`b_1 \ne b_2`
from mutual non-ancestry of two $`k`-finalized blocks.
-/
theorem hash_nonancestor_nonequal
    {h₁ h₂ : Hash}
    (hna : ¬ hash_ancestor parent h₁ h₂) :
    h₁ ≠ h₂ :=
  fun heq => False.elim (hna
    (Eq.subst (motive := fun x => hash_ancestor parent h₁ x) heq (hash_ancestor.refl h₁)))

/--
# Non-ancestry propagates upward along paths

Conflict propagation — the contrapositive of transitivity:

$$`h_1 \xrightarrow{*} h_2 \;\wedge\; \neg\,(p \xrightarrow{*} h_2) \;\implies\; \neg\,(p \xrightarrow{*} h_1)`

If $`p` cannot reach $`h_2`, and $`h_1` can, then $`p` cannot
reach $`h_1` either — because if it could, composing the two paths
via {lit}`hash_ancestor_concat` would give
$`p \xrightarrow{*} h_2`, contradicting the second hypothesis.

This is the key lemma that propagates non-ancestry upward along
justification chains in {lit}`k_non_equal_height_case_ind`: as the
induction descends from a justified block toward the finalized
checkpoint, the non-ancestry hypothesis is carried to each
predecessor source.
-/
theorem hash_ancestor_conflict
    {h₁ h₂ p : Hash}
    (h12 : hash_ancestor parent h₁ h₂)
    (hp2 : ¬ hash_ancestor parent p h₂) :
    ¬ hash_ancestor parent p h₁ :=
  fun hp1 => hp2 (hash_ancestor_concat hp1 h12)

/-!
## Graded–ungraded interface

The following lemmas connect the distance-indexed
{name}`nth_ancestor` ($`\xrightarrow{n}`) with the ungraded
{name}`hash_ancestor` ($`\xrightarrow{*}`). The key facts are:

: Forgetting the index

  {lit}`nth_ancestor_ancestor`: $`\xrightarrow{n}` implies
  $`\xrightarrow{*}`

: Base cases

  {lit}`nth_ancestor_0_refl` ($`n = 0 \implies` equality) and
  {lit}`parent_ancestor` ($`n = 1 \iff` parent edge)

: Inversion

  {lit}`nth_ancestor_succ_inv`: a distance-$`(n+1)` chain splits
  as a distance-$`n` chain plus one parent edge
-/

/--
# Distance-indexed ancestry implies ungraded ancestry

A distance-$`n` chain gives an ungraded ancestry path,
forgetting the step count:

$$`s \xrightarrow{n} t \;\implies\; s \xrightarrow{*} t`

Proved by induction on the {name}`nth_ancestor` derivation:
the base case ({lit}`nth_ancestor_0`) gives {lit}`refl`, the step
case ({lit}`nth_ancestor_nth`) extends by {lit}`step`.
-/
theorem nth_ancestor_ancestor
    {n : Nat}
    {s t : Hash}
    (h : nth_ancestor parent n s t) :
    hash_ancestor parent s t :=
  match h with
  | .nth_ancestor_0 h => hash_ancestor.refl h
  | .nth_ancestor_nth h' hp => hash_ancestor.step (nth_ancestor_ancestor h') hp

/--
# Zero-step ancestry forces equality

$`h_1 \xrightarrow{0} h_2` implies $`h_1 = h_2`. The only
constructor producing distance $`0` is {lit}`nth_ancestor_0`,
which requires $`h_1 = h_2`.
-/
theorem nth_ancestor_0_refl
    {h₁ h₂ : Hash}
    (h : nth_ancestor parent 0 h₁ h₂) :
    h₁ = h₂ :=
  match h with
  | .nth_ancestor_0 _ => rfl

/--
# A parent edge is exactly one-step graded ancestry

A parent edge is exactly a
graded ancestry step of length one:

$$`h_1 \to h_2 \;\iff\; h_1 \xrightarrow{1} h_2`

The forward direction builds
{lit}`nth_ancestor_nth` over {lit}`nth_ancestor_0`; the reverse
matches on the single-step chain and extracts the parent edge.
Used in {lit}`finalized_means_one_finalized` and
{lit}`finalized_means_justified_child` to convert between the
parent edge in {lit}`finalized` and the graded ancestry in
{lit}`k_finalized`.
-/
theorem parent_ancestor
    {h₁ h₂ : Hash} :
    parent h₁ h₂ ↔ nth_ancestor parent 1 h₁ h₂ :=
  ⟨fun hp => nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 h₁) hp,
   fun h => match h with
    | .nth_ancestor_nth (.nth_ancestor_0 _) hp => hp⟩

/--
# A distance-$`(n+1)` chain splits into a chain plus one edge

Successor inversion: a distance-$`(n+1)` chain decomposes as a
distance-$`n` chain followed by one parent edge:

$$`a \xrightarrow{n+1} c \;\implies\; \exists\, b,\; a \xrightarrow{n} b \;\wedge\; b \to c`

The proof matches on the {lit}`nth_ancestor_nth` constructor, which
is the only one producing $`\mathrm{succ}\,n`, and extracts the
intermediate block $`b` together with the two halves of the chain.
Used in {lit}`blocks_exist_extract_new_final_pair_from_bound` to
peel the last parent edge off a block-existence witness.
-/
theorem nth_ancestor_succ_inv
    {n : Nat}
    {a c : Hash}
    (h : nth_ancestor parent (Nat.succ n) a c) :
    ∃ b : Hash, nth_ancestor parent n a b ∧ parent b c :=
  match h with
  | .nth_ancestor_nth hprev hp => ⟨_, hprev, hp⟩

end GasperBeaconChain.Core
