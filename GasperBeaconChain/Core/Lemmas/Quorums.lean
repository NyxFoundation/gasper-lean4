import GasperBeaconChain.Core.AtomicDef.Quorums
import GasperBeaconChain.Core.Lemmas.Weight

universe u v

namespace GasperBeaconChain.Core

/-!
# Quorum lemmas

Three structural facts about $`\frac{2}{3}`-quorums
({name}`quorum_2`): up-closure under superset, nonemptiness under
positive thresholds, and the derived {name}`QuorumContext`
construction.

## Up-closure

{lit}`quorum_2_upclosed` says that if $`q` is a
$`\frac{2}{3}`-quorum and $`q \subseteq q' \subseteq V(b)`, then
$`q'` is also a $`\frac{2}{3}`-quorum. The weight condition is
inherited from $`q` via {lit}`wt_inc_leq` (monotonicity of weight).
This is the mechanism by which {lit}`supermajority_weaken` and
{lit}`supermajority_link_of_quorum_votes` promote a known quorum
to a larger supporter set.

## Nonemptiness

{lit}`quorum_2_nonempty_of_threshold_pos` derives
$`q.\mathrm{Nonempty}` from $`0 < f_{2/3}(\operatorname{wt}(V(b)))`:
a positive threshold forces the quorum to contain at least one
element (the empty set has weight $`0`).
{lit}`quorum_context_of_threshold_pos` wraps this into a
{name}`QuorumContext` value.

## Downstream use

{lit}`quorum_2_upclosed` is consumed in
{lit}`Lemmas/Justification.lean` ({lit}`supermajority_weaken`) and
{lit}`Lemmas/PlausibleLiveness.lean`
({lit}`supermajority_link_of_quorum_votes`).
{lit}`quorum_context_of_threshold_pos` provides a concrete
{name}`QuorumContext` whenever the threshold is known to be positive.
-/

variable {Validator : Type u}
variable {Hash : Type v}
variable [DecidableEq Validator]

/--
# Enlarging a quorum preserves the quorum property

**Up-closure** of $`\frac{2}{3}`-quorum status: enlarging a quorum
$`q` to a superset $`q'` that still lies within $`V(b)` preserves
the quorum property.

$$`q \subseteq q' \;\wedge\; q' \subseteq V(b) \;\wedge\; \operatorname{quorum\_2}(q, b) \;\implies\; \operatorname{quorum\_2}(q', b)`

# Proof idea

The two conjuncts of {name}`quorum_2` for $`q'` are discharged
separately:

* *Subset*: $`q' \subseteq V(b)` is the explicit hypothesis
  {lit}`hsub_vset`.
* *Weight*: the chain
  $`f_{2/3}(\operatorname{wt}(V(b))) \le \operatorname{wt}(q) \le \operatorname{wt}(q')`
  uses the quorum weight bound from $`q` (the second conjunct of
  {name}`quorum_2` for $`q`) and monotonicity of weight
  ({lit}`wt_inc_leq`) applied to $`q \subseteq q'`.

# Assumptions

* $`q \subseteq q'` — the enlargement {lit}`hsub`;
* $`q' \subseteq V(b)` — the new set still consists of validators
  *eligible* at $`b` {lit}`hsub_vset` (this keeps $`q'` a legitimate
  quorum and is *not* automatic from $`q \subseteq q'`);
* $`\operatorname{quorum\_2}(q, b)` — $`q` is already a quorum
  {lit}`hq`.

$`[\mathsf{DecidableEq}\ \mathsf{Validator}]` is in scope as a
section variable.

# Non-assumptions

* the threshold $`f_{2/3}` need not be positive — up-closure holds
  even at a degenerate zero threshold;
* nonemptiness of $`q` is not assumed (it follows separately, under
  a positive threshold, in
  {lit}`quorum_2_nonempty_of_threshold_pos`).

# Role in the development

The mechanism by which {lit}`supermajority_weaken` and
{lit}`supermajority_link_of_quorum_votes` promote a known quorum
to a larger supporter set in an extended state — the monotonicity
that lets a quorum's witnesses survive when more votes are added.
-/
theorem quorum_2_upclosed
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    {b : Hash}
    {q q' : Finset Validator}
    (hsub : q ⊆ q')
    (hsub_vset : q' ⊆ vset b)
    (hq : quorum_2 τ stake vset q b) :
    quorum_2 τ stake vset q' b :=
  match hq with
  | ⟨_, hq_wt⟩ => ⟨hsub_vset, le_trans hq_wt (wt_inc_leq stake hsub)⟩

/--
# A positive threshold forces quorums to be nonempty

**Nonemptiness from a positive threshold**: if the two-thirds
threshold $`f_{2/3}(\operatorname{wt}(V(b)))` is strictly positive,
then any $`\frac{2}{3}`-quorum $`q` at $`b` is nonempty.

$$`0 < f_{2/3}(\operatorname{wt}(V(b))) \;\wedge\; \operatorname{quorum\_2}(q, b) \;\implies\; q.\mathrm{Nonempty}`

# Proof idea

The quorum weight bound gives
$`0 < f_{2/3}(\operatorname{wt}(V(b))) \le \operatorname{wt}(q)`,
so $`\operatorname{wt}(q) > 0`. The proof then proceeds by
{name}`Finset.induction_on` on $`q` with the motive
$`0 < \operatorname{wt}(s) \implies s.\mathrm{Nonempty}`:

* _Empty case_: $`\operatorname{wt}(\emptyset) = 0`, so
  $`0 < 0` is absurd ({lit}`Nat.not_lt_of_ge` +
  {lit}`Nat.zero_le`).
* _Insert case_: the inserted element $`a` witnesses
  nonemptiness of $`\{a\} \cup s'`.

# Role in the development

This is the nonemptiness witness that
{name}`QuorumContext` carries. It is consumed everywhere a
validator must be extracted from a quorum — most critically in
{lit}`good_votes_mean_source_justified` and
{lit}`maximal_link_exists`.
-/
theorem quorum_2_nonempty_of_threshold_pos
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    {b : Hash}
    {q : Finset Validator}
    (hpos : 0 < τ.two_third (wt stake (vset b)))
    (hq : quorum_2 τ stake vset q b) :
    q.Nonempty :=
  match hq with
  | ⟨_, hq_weight⟩ =>
    Finset.induction_on q
      (motive := fun s => 0 < wt stake s → s.Nonempty)
      (fun h0 => False.elim ((Nat.not_lt_of_ge (Nat.zero_le _)) h0))
      (fun a _ _ _ _ => ⟨a, Finset.mem_insert_self a _⟩)
      (Nat.lt_of_lt_of_le hpos hq_weight)

/--
# Constructing a {name}`QuorumContext` from universally positive thresholds

**Concrete {name}`QuorumContext`**: if
$`f_{2/3}(\operatorname{wt}(V(b))) > 0` for every block $`b`, then
the {name}`quorum_2_nonempty_property` holds and can be bundled into
a {name}`QuorumContext`:

$$`\bigl(\forall b,\; 0 < f_{2/3}(\operatorname{wt}(V(b)))\bigr) \;\implies\; \operatorname{QuorumContext}(\tau, \mathsf{stake}, \mathsf{vset})`

# Proof idea

The single field {lit}`quorum_2_nonempty` of {name}`QuorumContext`
is discharged by applying
{lit}`quorum_2_nonempty_of_threshold_pos` at each block $`b`,
using the universally quantified positivity hypothesis to supply
the $`0 < f_{2/3}(\operatorname{wt}(V(b)))` premise.

# Role in the development

This provides the concrete {name}`QuorumContext` that
{lit}`Theories/PlausibleLiveness.lean` and
{lit}`Theories/AccountableSafety.lean` thread as a standing
parameter. The alternative is to assume a {name}`QuorumContext`
directly — this theorem shows that positive thresholds suffice.
-/
theorem quorum_context_of_threshold_pos
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (hpos : ∀ b : Hash, 0 < τ.two_third (wt stake (vset b))) :
    QuorumContext (Hash := Hash) τ stake vset :=
  ⟨fun b _ hq => quorum_2_nonempty_of_threshold_pos τ stake vset (hpos b) hq⟩

end GasperBeaconChain.Core
