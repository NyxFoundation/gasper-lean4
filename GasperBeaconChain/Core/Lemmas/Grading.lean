import GasperBeaconChain.Core.AtomicDef.Grading
import GasperBeaconChain.Core.AtomicDef.Justification
import GasperBeaconChain.Core.Lemmas.HashTree

universe u v

namespace GasperBeaconChain.Core

/-!
# Grading lemmas: heights are depths

This file proves, inside the abstract model and without touching any
existing definition, that the graded ancestry condition of
{name}`justification_link` is the *right* condition under the
checkpoint-tree interpretation of {lit}`HashTree.lean`.

## The question being answered

{name}`justification_link` requires the target to be reached from the
source by *exactly* $`h_t - h_s` parent edges
($`s \xrightarrow{h_t - h_s} t`). Read as a statement about a
slot-level block tree this would be wrong: the number of blocks
between two checkpoints is unrelated to their epoch difference, and
across empty epochs the same block is both checkpoints. Read as a
statement about Gasper's *checkpoint tree* — nodes are epoch boundary
pairs $`(B, j)`, one parent edge per epoch — it is exactly "the source
checkpoint lies on the target's checkpoint chain", because the tree is
graded by the epoch. The lemmas below make this precise.

## Depth without any hypothesis (§ 1)

* {lit}`nth_ancestor_trans` — graded paths compose, adding their
  lengths.
* {lit}`justified_depth` — **every justified checkpoint sits at depth
  equal to its height**: $`\operatorname{justified}(\sigma, b, h)`
  implies $`g \xrightarrow{h} b`. This needs no grading hypothesis at
  all: it follows from the inductive shape of {name}`justified`.

## Grading (§ 2)

Under {name}`height_graded` (genesis at height $`0`, each parent edge
adds $`1`):

* {lit}`height_le_of_ancestor` (G1) — heights are monotone along
  ancestry;
* {lit}`height_eq_of_nth_ancestor` (G2) — the length of a graded
  path equals the height difference;
* {lit}`nth_ancestor_of_ancestor` (G3) — plain ancestry already
  yields the graded path of length $`\mathrm{ht}(t) - \mathrm{ht}(s)`;
* {lit}`justification_link_iff_ancestor` (G4) — **the graded condition
  of {name}`justification_link` is equivalent to plain checkpoint
  ancestry** when the heights are the true depths;
* {lit}`justified_height_eq` (G5) — the height field carried by a
  {name}`justified` derivation is forced to be the true depth, even
  though votes may carry arbitrary height fields.

## Downstream use

{lit}`Refinement/CheckpointTree.lean` instantiates the grading with
the epoch of a concrete $`(\mathsf{block}, \mathsf{epoch})`
checkpoint ({lit}`cp_graded`) and combines G4 with the ancestry
correspondence {lit}`cp_link_correspondence` into
{lit}`cp_justification_link_iff`, the statement that on the concrete
checkpoint tree a justification link is a supermajority link from a
checkpoint on the target's checkpoint chain.
-/

variable {Validator : Type u}
variable {Hash : Type v}

/-!
## § 1 Depth of justified checkpoints
-/

/--
# Graded paths compose

Concatenating a path of length $`m` with a path of length $`n` gives
a path of length $`m + n`:

$$`a \xrightarrow{m} b \;\wedge\; b \xrightarrow{n} c \;\implies\; a \xrightarrow{m+n} c`

By induction on the second path, mirroring {lit}`hash_ancestor_concat`
for the ungraded relation.
-/
theorem nth_ancestor_trans
    {parent : HashParent Hash}
    {m n : Nat}
    {a b c : Hash}
    (h₁ : nth_ancestor parent m a b)
    (h₂ : nth_ancestor parent n b c) :
    nth_ancestor parent (m + n) a c :=
  match h₂ with
  | .nth_ancestor_0 _ => h₁
  | .nth_ancestor_nth h₂' hp =>
      nth_ancestor.nth_ancestor_nth (nth_ancestor_trans h₁ h₂') hp

/--
# A justified checkpoint is reached from genesis in exactly its height many steps

**Justification heights are tree depths.** If $`b` is justified at
height $`h` then $`b` is reached from genesis by *exactly* $`h`
parent edges:

$$`\operatorname{justified}(\sigma, b, h) \;\implies\; g \xrightarrow{h} b`

# Proof idea

Induction on the {name}`justified` derivation. Genesis is at
distance $`0` from itself. For a link from $`(s, h_s)` to
$`(t, h_t)`, the induction hypothesis gives $`g \xrightarrow{h_s} s`,
the link gives $`s \xrightarrow{h_t - h_s} t`, and
{lit}`nth_ancestor_trans` composes them into
$`g \xrightarrow{h_s + (h_t - h_s)} t`, where
$`h_s + (h_t - h_s) = h_t` because the link guarantees $`h_s < h_t`
({name}`Nat.add_sub_of_le`).

# Interpretation

This is the first half of the answer to "are the heights in
{lit}`Vote` just arbitrary numbers?": whatever height fields the
votes carry, the {name}`justified` predicate only ever certifies a
pair $`(b, h)` whose $`h` is the genuine depth of $`b` in the tree.
No grading hypothesis is needed — the graded ancestry condition of
{name}`justification_link` enforces it link by link.
-/
theorem justified_depth
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Hash → Finset Validator}
    {parent : HashParent Hash}
    {genesis : Hash}
    {st : State Validator Hash}
    {b : Hash} {h : Nat}
    (hj : justified τ stake vset parent genesis st b h) :
    nth_ancestor parent h genesis b :=
  match hj with
  | .justified_genesis => nth_ancestor.nth_ancestor_0 genesis
  | .justified_link hsrc hlink =>
      Eq.subst (motive := fun k => nth_ancestor parent k genesis _)
        (Nat.add_sub_of_le (Nat.le_of_lt hlink.1))
        (nth_ancestor_trans (justified_depth hsrc) hlink.2.1)

/-!
## § 2 Consequences of a height grading
-/

/--
# (G1) Heights are monotone along ancestry

Under a height grading, an ancestor is never higher than its
descendant:

$$`s \xrightarrow{*} t \;\implies\; \mathrm{ht}(s) \le \mathrm{ht}(t)`

Induction on the ancestry path: each parent edge raises the height
by one.
-/
theorem height_le_of_ancestor
    {parent : HashParent Hash}
    {genesis : Hash}
    {ht : Hash → Nat}
    (hg : height_graded parent genesis ht)
    {s t : Hash}
    (ha : hash_ancestor parent s t) :
    ht s ≤ ht t :=
  match ha with
  | .refl _ => Nat.le_refl _
  | .step ha' hp =>
      Eq.subst (motive := fun x => ht s ≤ x) (hg.2 hp).symm
        (Nat.le_succ_of_le (height_le_of_ancestor hg ha'))

/--
# (G2) The length of a graded path is the height difference

Under a height grading, the step count of a graded path is
determined by the endpoints:

$$`s \xrightarrow{n} t \;\implies\; \mathrm{ht}(t) = \mathrm{ht}(s) + n`

Induction on the path; each step adds one to both sides.
-/
theorem height_eq_of_nth_ancestor
    {parent : HashParent Hash}
    {genesis : Hash}
    {ht : Hash → Nat}
    (hg : height_graded parent genesis ht)
    {n : Nat}
    {s t : Hash}
    (ha : nth_ancestor parent n s t) :
    ht t = ht s + n :=
  match ha with
  | .nth_ancestor_0 _ => rfl
  | .nth_ancestor_nth ha' hp =>
      (hg.2 hp).trans (congrArg (· + 1) (height_eq_of_nth_ancestor hg ha'))

/--
# (G3) Plain ancestry yields the graded path of length $`\mathrm{ht}(t) - \mathrm{ht}(s)`

Under a height grading, an ungraded ancestry path is automatically a
graded path whose length is the height difference:

$$`s \xrightarrow{*} t \;\implies\; s \xrightarrow{\mathrm{ht}(t) - \mathrm{ht}(s)} t`

# Proof idea

Induction on the path. In the step case
$`s \xrightarrow{*} h_2 \to h_3` the induction hypothesis gives
$`s \xrightarrow{\mathrm{ht}(h_2) - \mathrm{ht}(s)} h_2`; the grading
gives $`\mathrm{ht}(h_3) = \mathrm{ht}(h_2) + 1`, and
{lit}`height_le_of_ancestor` gives $`\mathrm{ht}(s) \le \mathrm{ht}(h_2)`,
so the truncated subtraction is well behaved:
$`\mathrm{ht}(h_3) - \mathrm{ht}(s) = (\mathrm{ht}(h_2) - \mathrm{ht}(s)) + 1`
({name}`Nat.succ_sub`).
-/
theorem nth_ancestor_of_ancestor
    {parent : HashParent Hash}
    {genesis : Hash}
    {ht : Hash → Nat}
    (hg : height_graded parent genesis ht)
    {s t : Hash}
    (ha : hash_ancestor parent s t) :
    nth_ancestor parent (ht t - ht s) s t :=
  match ha with
  | .refl _ =>
      Eq.subst (motive := fun k => nth_ancestor parent k s s)
        (Nat.sub_self (ht s)).symm
        (nth_ancestor.nth_ancestor_0 s)
  | .step ha' hp =>
      have hle := height_le_of_ancestor hg ha'
      have heq := (congrArg (· - ht s) (hg.2 hp)).trans (Nat.succ_sub hle)
      Eq.subst (motive := fun k => nth_ancestor parent k s _)
        heq.symm
        (nth_ancestor.nth_ancestor_nth (nth_ancestor_of_ancestor hg ha') hp)

/--
# (G4) The graded link condition is plain checkpoint ancestry

**Main equivalence.** When the heights attached to a link are the
true depths of its endpoints, the graded ancestry condition of
{name}`justification_link` is equivalent to plain ancestry:

$$`\operatorname{justification\_link}(\sigma, s, t, \mathrm{ht}(s), \mathrm{ht}(t)) \;\iff\; \mathrm{ht}(s) < \mathrm{ht}(t) \;\wedge\; s \xrightarrow{*} t \;\wedge\; \operatorname{supermajority\_link}(\sigma, s, t, \mathrm{ht}(s), \mathrm{ht}(t))`

# Interpretation

This is the theorem behind the checkpoint-tree reading of the model.
Gasper's justification condition is "the source checkpoint lies on
the target's checkpoint chain" (plus a supermajority link and a
forward epoch). On the checkpoint tree, "lies on the chain" is
$`s \xrightarrow{*} t`. Because the checkpoint tree is graded by the
epoch, this is the same as $`s \xrightarrow{h_t - h_s} t`, which is
what {name}`justification_link` requires. The forward direction
forgets the step count ({lit}`nth_ancestor_ancestor`); the reverse
direction recovers it from the grading
({lit}`nth_ancestor_of_ancestor`).

# Non-assumptions

The supermajority conjunct is untouched: the equivalence is purely
about the structural conjuncts.
-/
theorem justification_link_iff_ancestor
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Hash → Finset Validator}
    {parent : HashParent Hash}
    {genesis : Hash}
    {ht : Hash → Nat}
    (hg : height_graded parent genesis ht)
    {st : State Validator Hash}
    {s t : Hash} :
    justification_link τ stake vset parent st s t (ht s) (ht t)
      ↔
    (ht s < ht t ∧
     hash_ancestor parent s t ∧
     supermajority_link τ stake vset st s t (ht s) (ht t)) :=
  ⟨fun ⟨hlt, hnth, hsm⟩ => ⟨hlt, nth_ancestor_ancestor hnth, hsm⟩,
   fun ⟨hlt, hanc, hsm⟩ => ⟨hlt, nth_ancestor_of_ancestor hg hanc, hsm⟩⟩

/--
# (G5) Justification heights are forced to be the true depths

Under a height grading, the height field certified by a
{name}`justified` derivation equals the height function:

$$`\operatorname{justified}(\sigma, b, h) \;\implies\; h = \mathrm{ht}(b)`

# Proof idea

{lit}`justified_depth` gives $`g \xrightarrow{h} b`, so by
{lit}`height_eq_of_nth_ancestor` $`\mathrm{ht}(b) = \mathrm{ht}(g) + h = 0 + h`.

# Interpretation

Votes ({lit}`Vote`) carry height fields that an adversary may fill in
arbitrarily, and the model deliberately admits such votes (they can
only enlarge the set of slashable behaviours, never weaken the safety
theorems). This lemma shows that the freedom is harmless for
justification: any $`(b, h)` that becomes justified has $`h` equal to
the depth of $`b`, i.e. to its attestation epoch under the
checkpoint-tree interpretation.
-/
theorem justified_height_eq
    [DecidableEq Validator]
    [DecidableEq Hash]
    [Fintype Validator]
    {τ : Threshold}
    {stake : Validator → Nat}
    {vset : Hash → Finset Validator}
    {parent : HashParent Hash}
    {genesis : Hash}
    {ht : Hash → Nat}
    (hg : height_graded parent genesis ht)
    {st : State Validator Hash}
    {b : Hash} {h : Nat}
    (hj : justified τ stake vset parent genesis st b h) :
    h = ht b :=
  have e₁ : ht b = ht genesis + h := height_eq_of_nth_ancestor hg (justified_depth hj)
  have e₂ : ht genesis + h = 0 + h := congrArg (· + h) hg.1
  (e₁.trans (e₂.trans (Nat.zero_add h))).symm

end GasperBeaconChain.Core
