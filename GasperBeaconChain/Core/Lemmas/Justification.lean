import GasperBeaconChain.Core.AtomicDef.Justification
import GasperBeaconChain.Core.Lemmas.HashTree
import GasperBeaconChain.Core.Lemmas.Quorums
import GasperBeaconChain.Core.Lemmas.ListExt
import GasperBeaconChain.Core.AtomicDef.NatExt

universe u v

namespace GasperBeaconChain.Core

/-!
# Justification and finalization: structural lemmas

Lemmas connecting the definitional layer
({lit}`AtomicDef/Justification.lean`) to the safety and liveness
theories. Two groups:

## Monotonicity under state extension

* {lit}`supermajority_weaken` — a supermajority link in $`\sigma`
  survives in any extension $`\sigma' \supseteq \sigma` (provided
  the extension satisfies the vote well-formedness property).
* {lit}`justified_weaken` — justification is likewise monotone under
  state extension: every justified block in $`\sigma` remains
  justified in $`\sigma'`. Proved by induction on the
  {name}`justified` derivation, applying
  {lit}`supermajority_weaken` at each link.

These two lemmas are the mechanism by which the plausible-liveness
construction ({lit}`plausible_liveness_construct_extension`) carries
justification from the old state into the extended state.

## The finalized ↔ $`k`-finalized bridge

* {lit}`k_finalized_means_justified` — every $`k`-finalized block
  is justified (extract the $`n = 0` component of the chain).
* {lit}`finalized_means_justified_child` — a finalized block has a
  justified child at height $`h + 1`.
* {lit}`finalized_means_one_finalized` — the equivalence
  $`\operatorname{finalized} \iff \operatorname{k\_finalized}\,1`.
* {lit}`k_finalized_last_justified` — the last block in a
  $`k`-finalization chain is justified and reachable by exactly
  $`k` parent steps.
* {lit}`justified_cases` — case analysis on a {name}`justified`
  derivation: either genesis or a link from a justified source.
-/

variable {Validator : Type u}
variable {Hash : Type v}
variable [DecidableEq Validator]
variable [DecidableEq Hash]
variable [Fintype Validator]

/--
# Supermajority links survive state extension

**Supermajority links are monotone under state extension**:

$$`\sigma \subseteq \sigma' \;\wedge\; \operatorname{wf}(\sigma') \;\wedge\; \operatorname{supermajority\_link}(\sigma, s, t, h_s, h_t) \;\implies\; \operatorname{supermajority\_link}(\sigma', s, t, h_s, h_t)`

where $`\sigma \subseteq \sigma'` means every vote in $`\sigma` is
in $`\sigma'`, and $`\operatorname{wf}(\sigma')` abbreviates
{lit}`votes_from_target_vset_property`.

# Proof idea

The supporter set $`\operatorname{link\_supporters}(\sigma, s, t, h_s, h_t)`
is a subset of
$`\operatorname{link\_supporters}(\sigma', s, t, h_s, h_t)`
(since every old vote persists in $`\sigma'`). The larger
supporter set still lies in $`V(t)` by the well-formedness
hypothesis on $`\sigma'`. {lit}`quorum_2_upclosed` then transfers
the quorum property from the smaller to the larger set.

# Assumptions

* $`\sigma \subseteq \sigma'` — vote-level inclusion {lit}`HSub`;
* $`\operatorname{wf}(\sigma')` — well-formedness of the target
  state {lit}`hwf`;
* $`\operatorname{supermajority\_link}(\sigma, s, t, h_s, h_t)` — the
  link is already a supermajority link in $`\sigma` {lit}`hsm`.

# Non-assumptions

* the well-formedness of $`\sigma` is *not* needed — only that of
  $`\sigma'`, since it is the *grown* supporter set whose eligibility
  must be checked;
* nothing about the height pair $`(h_s, h_t)` or the block-tree
  relation between $`s` and $`t` is used: this lemma concerns *only*
  the weight/eligibility of the supporters, treating the link's
  graph data as opaque.

# Role in the development

The mechanism by which {lit}`justified_weaken` carries each
justification link across the state extension, and by which
{lit}`supermajority_link_of_quorum_votes` constructs new links
in the extended state. It is the single point where the
quorum up-closure {lit}`quorum_2_upclosed` meets the protocol's
monotone vote accumulation.
-/
theorem supermajority_weaken
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    {st st' : State Validator Hash}
    {s t : Hash}
    {s_h t_h : Nat}
    (HSub : ∀ vote : Vote Validator Hash, vote ∈ st → vote ∈ st')
    (hwf : votes_from_target_vset_property vset st')
    (hsm : supermajority_link τ stake vset st s t s_h t_h) :
    supermajority_link τ stake vset st' s t s_h t_h :=
  show quorum_2 τ stake vset (link_supporters st' s t s_h t_h) t from
    @quorum_2_upclosed Validator Hash _ τ stake vset t
      (link_supporters st s t s_h t_h) (link_supporters st' s t s_h t_h)
      (fun v hv => mem_link_supporters.mpr
        (HSub ⟨v, s, t, s_h, t_h⟩ (mem_link_supporters.mp hv)))
      (fun _ hv => hwf hv)
      hsm

/--
# Justified blocks remain justified in any extension

**Justification is monotone under state extension**:

$$`\sigma \subseteq \sigma' \;\wedge\; \operatorname{wf}(\sigma') \;\wedge\; \operatorname{justified}(\sigma, t, h_t) \;\implies\; \operatorname{justified}(\sigma', t, h_t)`

Every block justified in $`\sigma` remains justified in any
well-formed extension $`\sigma'`.

# Proof idea

Induction on the {name}`justified` derivation ({lit}`.rec`).
The genesis case is immediate (genesis is justified in every
state). In the link case, the induction hypothesis gives
$`\operatorname{justified}(\sigma', s, h_s)` for the source;
the three conjuncts of the justification link are carried across
as follows: the height guard $`h_s < h_t` and the ancestry
$`s \xrightarrow{h_t - h_s} t` are state-independent (they depend
only on the block tree), and the supermajority link is transferred
by {lit}`supermajority_weaken`.

# Assumptions

* $`\sigma \subseteq \sigma'` — every vote of the old state persists
  {lit}`HSub` (this is a vote-level inclusion, *not* a
  supporter-set or weight inclusion — those are derived);
* $`\operatorname{wf}(\sigma')` — well-formedness of the *target*
  state {lit}`hwf` ({lit}`votes_from_target_vset_property`), needed
  by {lit}`supermajority_weaken` to keep the enlarged supporter set
  inside $`V(t)`;
* $`\operatorname{justified}(\sigma, t, h_t)` — the block is
  justified in the *old* state {lit}`hj`.

# Non-assumptions

* well-formedness of the *old* state $`\sigma` is *not* required —
  only $`\sigma'` must be well-formed, because the supporter set
  grows and it is the larger set that must stay within $`V(t)`;
* the new votes $`\sigma' \setminus \sigma` are entirely
  unconstrained beyond well-formedness — they may support arbitrary
  other links;
* monotonicity is one-directional: it says nothing about
  justification being *preserved under shrinking* (which is false in
  general).

# Role in the development

Used in {lit}`plausible_liveness_construct_extension` to carry the
highest justified block's justification from $`\sigma` into the
extended state $`\sigma'` — the guarantee that adding the two new
quorums' votes never *un*-justifies the existing frontier.
-/
theorem justified_weaken
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    {st st' : State Validator Hash}
    (HSub : ∀ vote : Vote Validator Hash, vote ∈ st → vote ∈ st')
    (hwf : votes_from_target_vset_property vset st')
    {t : Hash}
    {t_h : Nat}
    (hj : justified τ stake vset parent genesis st t t_h) :
    justified τ stake vset parent genesis st' t t_h :=
  hj.rec
    justified.justified_genesis
    (fun _ hlink ih =>
      match hlink with
      | ⟨hgt, hnth, hsm⟩ => justified.justified_link ih
          ⟨hgt, hnth, supermajority_weaken τ stake vset HSub hwf hsm⟩)

/-!
## The finalized ↔ $`k`-finalized bridge

The next five lemmas connect {lit}`finalized` (one-step, defined
in {lit}`AtomicDef/Justification.lean`) with {lit}`k_finalized`
(depth-$`k`). Their roles are:

: Justification extraction

  {lit}`k_finalized_means_justified` — the base block of any
  $`k`-finalization chain is justified.

: Child extraction

  {lit}`finalized_means_justified_child` — a finalized block has a
  justified child at height $`h + 1`.

: The equivalence

  {lit}`finalized_means_one_finalized` — finalized $`\iff`
  $`1`-finalized.

: Last-block extraction

  {lit}`k_finalized_last_justified` — the chain's last block is
  justified and reachable in exactly $`k` steps.

: Case analysis

  {lit}`justified_cases` — inversion on the {name}`justified`
  inductive, surfacing genesis vs link as a disjunction.
-/

/--
# The base block of a $`k`-finalization chain is justified

**$`k`-finalization implies justification**: the base block of a
$`k`-finalization chain is justified.

$$`\operatorname{k\_finalized}(\sigma, b, b_h, k) \;\implies\; \operatorname{justified}(\sigma, b, b_h)`

# Proof idea

The definition of {lit}`k_finalized` includes a universal
quantifier $`\forall n \le k`, asserting that each chain block
$`\operatorname{ls.getD}\,n\,b` is justified at height $`b_h + n`.
Instantiating at $`n = 0` (which satisfies $`0 \le k` by
{lit}`Nat.zero_le`) gives
$`\operatorname{justified}(\sigma, \operatorname{ls.getD}\,0\,b, b_h + 0)`.
The list accessor at index $`0` agrees with the head
($`\operatorname{ls.getD}\,0\,b = \operatorname{ls.headD}\,b = b$
by {lit}`list_getD_zero_eq_headD` and the chain's head condition),
and $`b_h + 0 = b_h$ by {lit}`Nat.add_zero`, so two
{lit}`Eq.subst` transports yield the result.

# Role in the development

Used wherever a $`k`-finalized block's justification is needed:
{lit}`k_equal_height_case`,
{lit}`k_non_equal_height_case`, and
{lit}`no_k_finalized_justified_same_height` in the safety
development.
-/
theorem k_finalized_means_justified
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b : Hash}
    {b_h k : Nat}
    (hk : k_finalized τ stake vset parent genesis st b b_h k) :
    justified τ stake vset parent genesis st b b_h :=
  match hk with
  | ⟨_, ls, _, hhead, hrel, _⟩ =>
    match hrel 0 (Nat.zero_le k) with
    | ⟨hj0, _⟩ =>
      have hget0 : ls.getD 0 b = b :=
        (match ls with | [] => rfl | _ :: _ => rfl : ls.getD 0 b = ls.headD b).trans hhead
      Eq.subst (motive := fun h => justified τ stake vset parent genesis st h b_h)
        hget0
        (Eq.subst (motive := fun n => justified τ stake vset parent genesis st
            (ls.getD 0 b) n)
          (Nat.add_zero b_h) hj0)

/--
# A finalized block has a justified child at the next height

**A finalized block has a justified child**:

$$`\operatorname{finalized}(\sigma, p, p_h) \;\implies\; \exists\, c,\; p \to c \;\wedge\; \operatorname{justified}(\sigma, c, p_h + 1)`

# Proof idea

From the finalization data $`(p, c, p_h)` — where $`p` is
justified at $`p_h`, $`p \to c`, and there is a supermajority
link from $`(p, p_h)` to $`(c, p_h + 1)` — the child's
justification is constructed by applying the {lit}`justified_link`
rule. This requires assembling the justification-link triple:
* forward direction $`p_h < p_h + 1` (by {lit}`Nat.lt_succ_self`),
* graded ancestry $`p \xrightarrow{1} c` (by {lit}`parent_ancestor`
  applied to $`p \to c`, with the distance rewritten from
  $`(p_h + 1) - p_h = 1` via {lit}`add_one_sub_self`),
* the supermajority link (given directly).

# Role in the development

Not directly consumed by the safety or liveness theorems, but
provides a useful derived fact: finalization at $`p_h` gives a
justified block one level higher, bridging finalization to the
next height layer.
-/
theorem finalized_means_justified_child
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {p : Hash}
    {p_h : Nat}
    (hfin : finalized τ stake vset parent genesis st p p_h) :
    ∃ c : Hash,
      parent p c ∧
      justified τ stake vset parent genesis st c (p_h + 1) :=
  match hfin with
  | ⟨hj_p, c, hp, hsm⟩ =>
    ⟨c, hp, justified.justified_link hj_p
      ⟨Nat.lt_succ_self p_h,
       Eq.subst (motive := fun n => nth_ancestor parent n p c)
         (add_one_sub_self p_h).symm (parent_ancestor.mp hp),
       hsm⟩⟩

/--
# One-step finalization is equivalent to $`1`-finalization

**Finalized $`\iff` $`1`-finalized**: the one-step finalization
definition {lit}`finalized` is equivalent to
$`\operatorname{k\_finalized}` with $`k = 1`:

$$`\operatorname{finalized}(\sigma, b, b_h) \;\iff\; \operatorname{k\_finalized}(\sigma, b, b_h, 1)`

# Forward direction

Given finalized data $`(b, c, b_h)` with $`b \to c` and
supermajority link from $`(b, b_h)` to $`(c, b_h + 1)`,
constructs the chain $`[b, c]` of length $`2 = 1 + 1`. The
quantifier $`\forall n \le 1` is split into $`n = 0` and $`n = 1`
by {lit}`leq_one_means_zero_or_one`; the $`n = 0` case gives
$`b`'s justification, the $`n = 1` case gives $`c`'s
justification and the parent-as-graded-ancestry fact via
{lit}`parent_ancestor`.

# Reverse direction

Extracts $`b`'s justification from the $`n = 0` component,
recovers the parent edge from the $`n = 1` ancestry via
{lit}`parent_ancestor`, and reads the supermajority link from the
chain's last-block component (converting via
{lit}`list_getLastD_eq_getD_one_of_length_two`).
-/
theorem finalized_means_one_finalized
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    (b : Hash)
    (b_h : Nat) :
    finalized τ stake vset parent genesis st b b_h
      ↔
    k_finalized τ stake vset parent genesis st b b_h 1 :=
  ⟨fun ⟨hj_b, c, hp, hsm⟩ =>
    ⟨le_refl 1, [b, c], rfl, rfl,
     fun _n hn => (leq_one_means_zero_or_one hn).elim
       (fun hn0 =>
         Eq.subst (motive := fun n =>
             justified τ stake vset parent genesis st ([b, c].getD n b) (b_h + n)
             ∧ nth_ancestor parent n b ([b, c].getD n b))
           hn0.symm
           ⟨Eq.subst (motive := fun h =>
               justified τ stake vset parent genesis st b h)
             (Nat.add_zero b_h).symm hj_b,
            nth_ancestor.nth_ancestor_0 b⟩)
       (fun hn1 =>
         Eq.subst (motive := fun n =>
             justified τ stake vset parent genesis st ([b, c].getD n b) (b_h + n)
             ∧ nth_ancestor parent n b ([b, c].getD n b))
           hn1.symm
           ⟨justified.justified_link hj_b
             ⟨Nat.lt_succ_self b_h,
              Eq.subst (motive := fun n => nth_ancestor parent n b c)
                (add_one_sub_self b_h).symm (parent_ancestor.mp hp),
              hsm⟩,
            parent_ancestor.mp hp⟩),
     hsm⟩,
   fun ⟨_, ls, hlen, hhead, hrel, hlink⟩ =>
    have hget0 : ls.getD 0 b = b :=
      (match ls with | [] => rfl | _ :: _ => rfl : ls.getD 0 b = ls.headD b).trans hhead
    have hj_b : justified τ stake vset parent genesis st b b_h :=
      match hrel 0 (Nat.zero_le 1) with
      | ⟨hj0, _⟩ =>
        Eq.subst (motive := fun h => justified τ stake vset parent genesis st h b_h)
          hget0
          (Eq.subst (motive := fun n => justified τ stake vset parent genesis st
              (ls.getD 0 b) n)
            (Nat.add_zero b_h) hj0)
    have hp : parent b (ls.getD 1 b) :=
      match hrel 1 (le_refl 1) with
      | ⟨_, ha1⟩ => parent_ancestor.mpr ha1
    ⟨hj_b, ls.getD 1 b, hp,
      Eq.subst (motive := fun c =>
          supermajority_link τ stake vset st b c b_h (b_h + 1))
        (list_getLastD_eq_getD_one_of_length_two ls b hlen) hlink⟩⟩

/--
# The last block of a $`k`-finalization chain is justified and reachable

**Last block of a $`k`-finalization chain**: the chain's endpoint
is justified, reachable by exactly $`k` parent steps, and carries
the closing supermajority link.

$$`\operatorname{k\_finalized}(\sigma, b, b_h, k) \;\implies\; \exists\, \mathit{last},\; \operatorname{justified}(\sigma, \mathit{last}, b_h + k) \;\wedge\; b \xrightarrow{k} \mathit{last} \;\wedge\; \operatorname{supermajority\_link}(\sigma, b, \mathit{last}, b_h, b_h + k)`

The witness is $`\operatorname{ls.getLastD}\,b`, converted to the
positional accessor $`\operatorname{ls.getD}\,k\,b` via
{lit}`list_getLastD_eq_getD_of_length_eq_succ`, so that the chain's
universal quantifier at $`n = k` supplies the justification and
ancestry components.

Used in {lit}`k_slash_surround_case_general` to extract the last
justified block of the finalization chain for comparison with a
conflicting justification link target.
-/
theorem k_finalized_last_justified
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b : Hash}
    {b_h k : Nat}
    (hk : k_finalized τ stake vset parent genesis st b b_h k) :
    ∃ last : Hash,
      justified τ stake vset parent genesis st last (b_h + k)
      ∧
      nth_ancestor parent k b last
      ∧
      supermajority_link τ stake vset st b last b_h (b_h + k) :=
  match hk with
  | ⟨_, ls, hlen, _, hrel, hlink⟩ =>
    have hlast_eq : ls.getLastD b = ls.getD k b :=
      list_getLastD_eq_getD_of_length_eq_succ ls b hlen
    match hrel k (le_refl k) with
    | ⟨hj_last_getD, ha_last_getD⟩ =>
      ⟨ls.getLastD b,
        Eq.subst (motive := fun h => justified τ stake vset parent genesis st h (b_h + k))
          hlast_eq.symm hj_last_getD,
        Eq.subst (motive := fun h => nth_ancestor parent k b h)
          hlast_eq.symm ha_last_getD,
        hlink⟩

/--
# A justified block is either genesis or reached by a link

**Case analysis on justification**: a justified block is either
genesis at height $`0`, or it was reached via a justification link
from a justified source:

$$`\operatorname{justified}(\sigma, b, b_h) \;\implies\; (b = g \;\wedge\; b_h = 0) \;\lor\; \exists\, s\, s_h,\; \operatorname{justified}(\sigma, s, s_h) \;\wedge\; \operatorname{justification\_link}(\sigma, s, b, s_h, b_h)`

# Interpretation

This is a direct match on the two constructors of {name}`justified`
({lit}`justified_genesis` and {lit}`justified_link`), surfacing
the inductive structure as a proposition-level disjunction. The
genesis case identifies the block as $`g` at height $`0`; the
link case provides the predecessor $`s` at height $`s_h`, its
justification proof, and the full justification link from $`s`
to $`b`.

# Role in the development

The standard entry point for case-splitting on justification in
every branch of the safety argument:
* {lit}`two_justified_same_height_slashed` — the same-height
  slashing kernel uses it on both blocks;
* {lit}`k_non_equal_height_case_ind` — the strong-induction step
  uses it to extract the predecessor link;
* {lit}`maximal_link_highest_block` — uses it to show that a
  justified block above the maximal-link target would produce a
  higher link, contradicting maximality.
-/
theorem justified_cases
    (τ : Threshold) (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash) (genesis : Hash)
    (st : State Validator Hash)
    {b : Hash} {b_h : Nat}
    (hj : justified τ stake vset parent genesis st b b_h) :
    (b = genesis ∧ b_h = 0) ∨
    ∃ s : Hash, ∃ s_h : Nat,
      justified τ stake vset parent genesis st s s_h ∧
      justification_link τ stake vset parent st s b s_h b_h :=
  match hj with
  | .justified_genesis => Or.inl ⟨rfl, rfl⟩
  | .justified_link hsrc hlink => Or.inr ⟨_, _, hsrc, hlink⟩

end GasperBeaconChain.Core
