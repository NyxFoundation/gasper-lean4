import GasperBeaconChain.Core.Lemmas.Justification

universe u v

namespace GasperBeaconChain.Core

/-!
# Same-height slashing kernel

The two lemmas in this file establish the **structural** half of the
accountable-safety mechanism: if two distinct blocks are justified at
one height, then *every* validator in the intersection of the two
supporting quorums has cast two conflicting same-height votes — an
equivocation (Casper slashing condition (S1),
{lit}`slashed_double_vote`).

## The two lemmas

* {lit}`two_justified_same_height_slashed` — the **constructive**
  direction: given two *distinct* justified blocks $`b_1 \ne b_2` at
  a common height $`h`, *produces* an explicit
  {lit}`q_intersection_slashed` witness. This is the atomic
  conflict detector invoked by every branch of the safety case
  analysis in {lit}`Theories/AccountableSafety.lean`:
  the equal-height case ({lit}`k_equal_height_case`), the surround
  case ({lit}`k_slash_surround_case_general`), and the inductive
  non-equal-height case ({lit}`k_non_equal_height_case_ind`).

* {lit}`no_two_justified_same_height` — the **contrapositive**: under
  the standing assumption
  $`\neg\,\operatorname{q\_intersection\_slashed}`, two distinct
  justified blocks *cannot* share a height ($`h_1 \ne h_2`). Used
  in the plausible-liveness argument
  ({lit}`maximal_link_highest_block`) to rule out a justified block
  above the maximal link target.

## Scope of this file

This file establishes the *structural* half of the same-height
conflict: if two distinct blocks are justified at one height, then
*every* validator in the intersection of their two supporting
quorums has equivocated ({lit}`slashed_double_vote`). It does **not**
prove that the intersection is nonempty — that quantitative fact
(two $`\frac{2}{3}`-quorums overlap in $`\ge \frac{1}{3}` of the
total weight) is a weight argument carried out separately in
{lit}`Theories/SlashableBound.lean`. The broader pigeonhole /
inclusion–exclusion picture that unifies the two halves is recorded,
as a non-load-bearing aside, in the appendix at the end of this file.
-/

variable {Validator : Type u}
variable {Hash : Type v}
variable [DecidableEq Validator]
variable [DecidableEq Hash]
variable [Fintype Validator]

/--
# Two distinct blocks justified at the same height produce a slashing witness

Two *distinct* blocks justified at a common height produce a
{lit}`q_intersection_slashed` witness — the same-height
equivocation kernel of accountable safety.

# Statement

$$`\operatorname{justified}(\sigma, b_1, h) \;\wedge\; \operatorname{justified}(\sigma, b_2, h) \;\wedge\; b_1 \ne b_2 \;\implies\; \operatorname{q\_intersection\_slashed}(\sigma)`

# Proof idea

Case-split each justified block via {lit}`justified_cases` (four
cases from the two blocks):

* *genesis × genesis*: $`b_1 = b_2 = \mathsf{genesis}` contradicts
  $`b_1 \ne b_2`.
* *genesis × link* (or *link × genesis*): the link's forward guard
  $`h_s < h` becomes $`h_s < 0` (since genesis has height $`0`),
  contradicting {lit}`Nat.not_lt_zero`.
* *link × link*: both $`b_1` and $`b_2` have incoming justification
  links at target height $`h`. Each link carries a supermajority
  ({name}`supermajority_link`) from which we extract the subset
  condition ({lit}`hlink_sm_sub`). The two
  {name}`link_supporters` sets — $`q_L` for the link
  $`(s_1, b_1, h_{s_1}, h)` and $`q_R` for the link
  $`(s_2, b_2, h_{s_2}, h)` — become the two quorums in the
  {lit}`q_intersection_slashed` witness, with
  $`q_L \subseteq V(b_1)` and $`q_R \subseteq V(b_2)` (note: these
  are in general *different* validator sets, matching the
  dynamic-validator-set definition). For every validator $`v` in
  $`q_L \cap q_R`, the two membership proofs
  ({name}`mem_link_supporters`) yield two {name}`vote_msg` entries:
  $`\sigma \ni (v, s_1, b_1, h_{s_1}, h)` and
  $`\sigma \ni (v, s_2, b_2, h_{s_2}, h)` — two votes to distinct
  targets $`b_1 \ne b_2` at the same target height $`h`, which is
  exactly {lit}`slashed_double_vote`, wrapped in {lit}`Or.inl` to
  inhabit {name}`slashed`.

# Assumptions

* $`\operatorname{justified}(\sigma, b_1, h)` and
  $`\operatorname{justified}(\sigma, b_2, h)` — two blocks justified
  in the *same* state $`\sigma` at the *same* height $`h`;
* $`b_1 \ne b_2` — the two blocks are distinct.

The ambient $`[\mathsf{Fintype}\ \mathsf{Validator}]`,
$`[\mathsf{DecidableEq}\ \mathsf{Validator}]`, and
$`[\mathsf{DecidableEq}\ \mathsf{Hash}]` are in scope as section
variables (needed to form the quorum intersection and weigh it).

# Non-assumptions

This is the *constructive* direction, so it assumes **no**
non-slashing hypothesis — on the contrary, it *produces* a slashing
witness. In particular it does *not* assume:

* $`\neg\,\operatorname{q\_intersection\_slashed}(\sigma)` (that is
  the hypothesis of the contrapositive
  {lit}`no_two_justified_same_height`, not of this lemma);
* {lit}`good_votes` or any forward-link well-formedness — the bare
  justification of each block already carries its supermajority
  link, which is all that is used;
* any relation between $`b_1` and $`b_2` in the block tree (they
  need not be siblings, ancestors, or comparable). Distinctness at a
  common height is the *only* structural input.
* no quorum-overlap weight bound — the conclusion
  {lit}`q_intersection_slashed` quantifies over the intersection
  without asserting it is inhabited (see `## Scope of this file`
  above).

# Role in the development

The atomic conflict detector used in every branch of the
accountable-safety case analysis. It supplies the *structural* half
of accountable safety (shared voters are slashed); the
*quantitative* half (the shared set is nonempty) is supplied
separately by the weight bounds of
{lit}`Theories/SlashableBound.lean`.
-/
theorem two_justified_same_height_slashed
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b1 b2 : Hash}
    {h : Nat}
    (hj1 : justified τ stake vset parent genesis st b1 h)
    (hj2 : justified τ stake vset parent genesis st b2 h)
    (hneq : b1 ≠ b2) :
    q_intersection_slashed τ stake vset st :=
  (justified_cases τ stake vset parent genesis st hj1).elim
    (fun ⟨hb1_gen, hh_zero⟩ =>
      (justified_cases τ stake vset parent genesis st hj2).elim
        (fun ⟨hb2_gen, _⟩ =>
          False.elim (hneq (match hb1_gen with | rfl => match hb2_gen with | rfl => rfl)))
        (fun ⟨_, _, _, hgt2, _, _⟩ =>
          False.elim ((Nat.not_lt_zero _) (match hh_zero with | rfl => hgt2))))
    (fun ⟨s1, sh1, _, hlink1⟩ =>
      match hlink1 with
      | ⟨hlink1_lt, _, hlink1_sm⟩ =>
      (justified_cases τ stake vset parent genesis st hj2).elim
        (fun ⟨_, hh_zero⟩ =>
          False.elim ((Nat.not_lt_zero _) (match hh_zero with | rfl => hlink1_lt)))
        (fun ⟨s2, sh2, _, hlink2⟩ =>
          match hlink2 with
          | ⟨_, _, hlink2_sm⟩ =>
          match hlink1_sm, hlink2_sm with
          | ⟨hlink1_sm_sub, _⟩, ⟨hlink2_sm_sub, _⟩ =>
          ⟨b1, b2,
            link_supporters st s1 b1 sh1 h,
            link_supporters st s2 b2 sh2 h,
            hlink1_sm_sub, hlink2_sm_sub, hlink1_sm, hlink2_sm,
            fun _ hvL hvR => Or.inl ⟨b1, b2, hneq, s1, sh1, s2, sh2, h,
              mem_link_supporters.mp hvL,
              mem_link_supporters.mp hvR⟩⟩))

/--
# Without slashing, distinct justified blocks have different heights

Contrapositive of same-height slashing: under the assumption
that no quorum intersection is fully slashed, two distinct justified
blocks must have *different* heights.

$$`\operatorname{justified}(\sigma, b_1, h_1) \;\wedge\; \operatorname{justified}(\sigma, b_2, h_2) \;\wedge\; \neg\,\operatorname{q\_intersection\_slashed}(\sigma) \;\wedge\; b_1 \ne b_2 \;\implies\; h_1 \ne h_2`

The proof assumes $`h_1 = h_2` for contradiction, transports
$`\operatorname{justified}(\sigma, b_2, h_2)` to height $`h_1` via
{lit}`Eq.subst`, applies {lit}`two_justified_same_height_slashed` to
obtain $`\operatorname{q\_intersection\_slashed}(\sigma)`, and
contradicts the non-slashing hypothesis.

# Assumptions

* two justified blocks $`(b_1, h_1)`, $`(b_2, h_2)` in $`\sigma`
  (heights now *independent*, unlike the forward direction);
* $`\neg\,\operatorname{q\_intersection\_slashed}(\sigma)` — the
  standing no-slashing hypothesis {lit}`hno`;
* $`b_1 \ne b_2` — distinctness {lit}`hneq`.

# Non-assumptions

* no ancestry, ordering, or comparability between $`b_1` and $`b_2`;
* no {lit}`good_votes` hypothesis — only the no-slashing assumption
  and the two justifications are used.

# Role in the development

Used in {lit}`Lemmas/PlausibleLiveness.lean`
({lit}`maximal_link_highest_block`) to show that a justified block
at height $`\ge h_t` must *equal* the maximal-link target (not
merely share its height) — the uniqueness half of "highest justified
block".
-/
theorem no_two_justified_same_height
    (τ : Threshold)
    (stake : Validator → Nat)
    (vset : Hash → Finset Validator)
    (parent : HashParent Hash)
    (genesis : Hash)
    (st : State Validator Hash)
    {b1 b2 : Hash}
    {b1_h b2_h : Nat}
    (hj1 : justified τ stake vset parent genesis st b1 b1_h)
    (hj2 : justified τ stake vset parent genesis st b2 b2_h)
    (hno : ¬ q_intersection_slashed τ stake vset st)
    (hneq : b1 ≠ b2) :
    b1_h ≠ b2_h :=
  fun hheight =>
    False.elim (hno (two_justified_same_height_slashed
      τ stake vset parent genesis st hj1
      (Eq.subst (motive := fun h => justified τ stake vset parent genesis st b2 h)
        hheight.symm hj2) hneq))

/-!
# Appendix: the pigeonhole picture behind accountable safety

*This appendix is a non-load-bearing aside. The two lemmas above do
not depend on the perspective recorded here; it is collected at the
file's end as added context and may be skipped without affecting any
proof.*

Accountable safety, in the Casper-FFG sense, rests on a classical
pigeonhole / inclusion–exclusion idea that the development splits
into two independent halves living in two different layers:

* **Structural half (this file).** If two distinct blocks are
  justified at one height, then *whichever* validators lie in the
  intersection of their two supporting $`\frac{2}{3}`-quorums have
  each cast two conflicting same-height votes, hence are slashed
  ({lit}`slashed_double_vote`). This is a purely logical
  construction: it quantifies over the intersection without
  asserting that intersection is inhabited. It uses no weight
  arithmetic at all — only the membership logic of
  {lit}`link_supporters`.

* **Quantitative half** ({lit}`Theories/SlashableBound.lean`). That the
  intersection is in fact heavy is a weight argument, carried out
  separately in {lit}`quorum_intersection_weight_lower`, built on
  the inclusion–exclusion identity {lit}`wt_add_inter_fUnion` of
  {lit}`Lemmas/Weight.lean`. The exact bound it proves, for two
  $`\frac{2}{3}`-quorums $`q_L \subseteq V_L`, $`q_R \subseteq V_R`,
  is

  $$`\operatorname{wt}(V_L \cap V_R) - f_{1/3}(\operatorname{wt}(V_L)) - f_{1/3}(\operatorname{wt}(V_R)) \;\le\; \operatorname{wt}(q_L \cap q_R),`

  with $`f_{1/3} = \tau.\mathsf{one\_third}`. The two validator sets
  $`V_L, V_R` are kept distinct — matching the
  dynamic-validator-set definition of {lit}`q_intersection_slashed`
  ({lit}`AtomicDef/Quorums.lean`), where the two quorums may belong
  to different blocks $`b_L, b_R` with different sets
  $`V(b_L), V(b_R)`. When $`V_L = V_R`, the bound specialises but the
  general statement is the one actually proved.

A caveat keeps this appendix honest. The abstract {name}`Threshold`
interface assumes only complementarity
$`n = f_{1/3}(n) + f_{2/3}(n)` and boundedness $`f_{2/3}(n) \le n`
({lit}`AtomicDef/NatExt.lean`). Whether the displayed lower bound is
*strictly positive* — i.e. whether the slashed overlap is forced to
be nonempty rather than merely lower-bounded — depends on the size
of $`V_L \cap V_R` relative to the two one-third residuals, which is
the role of the further validator-set bound
{lit}`validator_intersection_lower_bound` and of the concrete
threshold instance, not of the abstract interface.

The two halves are not composed into one theorem in the
development: {lit}`Theories/AccountableSafety.lean` proves
{lit}`accountable_safety` (finalization fork ⟹
{lit}`q_intersection_slashed`) using *only* the structural half, and
{lit}`Theories/SlashableBound.lean` proves {lit}`slashable_bound`
(quorum pair ⟹ intersection weight bound) independently. The
reader who combines both conclusions obtains "a nonempty set of
actually slashed validators", but the development leaves that
composition implicit rather than packaging it as a single theorem.

The separation is intentional: the structural construction in this
file needs none of the weight arithmetic, which is isolated in
{lit}`Theories/SlashableBound.lean` where it belongs.
-/

end GasperBeaconChain.Core
