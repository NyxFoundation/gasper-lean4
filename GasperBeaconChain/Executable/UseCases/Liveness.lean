import GasperBeaconChain.Executable.UseCases.Model
import GasperBeaconChain.Core.Theories.PlausibleLiveness
import GasperBeaconChain.Core.Theories.SlashableBound

/-!
# Use case — plausible liveness (Gasper Thm 6.1 / Casper FFG Thm 2)

**Scenario.** *No deadlock.* Regardless of history — even starting from the
**empty** state, with nothing justified beyond genesis — if the honest validators
form a 2/3 quorum, it is always *possible* to extend the state so that a new block
becomes justified and its child supermajority-linked (hence finalizable), **without
any honest validator slashing itself**. This is the liveness half of Casper FFG.

Unlike safety, liveness requires an *unbounded supply of blocks*: the finite
checkpoint tree of `Model` cannot satisfy `blocks_exist_high_over` (there is no
block above height 5). So this use case takes the block space to be `Hash = ℕ`
with the linear parent chain `parent a b ↔ b = a + 1`, where a block exists at
every height. The validator universe is still the choice-free `V = Fin 99`.

We discharge the hypotheses of Core's `plausible_liveness_construct_extension` for
the empty state `∅` — most are *vacuous* there (no votes ⇒ no slashing, every
quorum is "good", every link supporter trivially lies in the universal set) — and
the only genuine content is:

* the 2/3-quorum overlap pigeonhole, used to show `∅` is **not** `q_intersection_slashed`
  (two 2/3 quorums of the same 99-validator set intersect in weight `≥ 33 > 0`, but
  no validator is slashed in `∅`); and
* `blocks_exist_high_over` for the linear chain (a block sits at every height).

The conclusion is the constructive extension `st'` finalizing a fresh block.
`Classical.choice`-free throughout.
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

/-- The liveness block space: genesis `0`. -/
def genesisL : Nat := 0

/-- The linear parent chain: `b` is the child of `a` iff `b = a + 1`. A block
exists at every height, so finality can always make progress. -/
def parentL : Nat → Nat → Prop := fun a b => b = a + 1

instance : DecidableRel parentL := fun a b => by unfold parentL; infer_instance

/-- Static universal validator set (over the `ℕ`-indexed blocks). -/
def vsetL : Nat → Finset V := fun _ => Finset.univ


/-! ### 1. The empty state slashes no one; quorum context -/

/-- In the empty state no validator is slashable (no votes to violate a
condition). Kernel-decided over the whole committee. -/
theorem empty_not_slashed : ∀ v : V, ¬ slashed (∅ : State V Nat) v := by decide

/-- Two-thirds quorums are nonempty here (`two_third 99 = 66 > 0`). -/
theorem qctxL : QuorumContext τ stake vsetL :=
  quorum_context_of_threshold_pos τ stake vsetL
    (fun _ => (by decide : 0 < τ.two_third (wt stake (Finset.univ : Finset V))))


/-! ### 2. The (mostly vacuous) hypotheses at the empty state -/

/-- Every block has a good quorum: take the whole committee; it is a 2/3 quorum
and none of its members is slashed in `∅`. -/
theorem two_thirds_good_empty : two_thirds_good τ stake vsetL (∅ : State V Nat) :=
  fun _ => ⟨Finset.univ,
    ⟨Finset.subset_univ _,
     (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake Finset.univ)⟩,
    fun v _ => empty_not_slashed v⟩

/-- Every quorum member's (nonexistent) votes are vacuously well-formed. -/
theorem good_votes_empty : good_votes τ stake vsetL parentL genesisL (∅ : State V Nat) := by
  intro _ _ _ _ _
  refine ⟨fun _ _ _ _ hvm => absurd hvm (Finset.notMem_empty _),
          fun _ _ _ _ hvm => absurd hvm (Finset.notMem_empty _)⟩

/-- Link supporters of `∅` (there are none) lie in any target set. -/
theorem wf_empty : votes_from_target_vset_property vsetL (∅ : State V Nat) := by
  intro x s t s_h t_h hx
  exact absurd (mem_link_supporters.mp hx) (Finset.notMem_empty _)

/-- The empty state is **not** `q_intersection_slashed`: any two 2/3 quorums of the
99-validator set overlap in weight `≥ 99 - 33 - 33 = 33 > 0`, yet `∅` slashes no
one — contradiction. (The 2/3-overlap pigeonhole, made concrete.) -/
theorem unslashed_empty : ¬ q_intersection_slashed τ stake vsetL (∅ : State V Nat) := by
  rintro ⟨bL, bR, qL, qR, hqLsub, hqRsub, hqL, hqR, hsl⟩
  -- (i) On `∅` no validator is slashed, so the slashing clause forces the overlap
  -- to be **empty** (choice-free: every element of it would be slashed in `∅`).
  -- (i) The 2/3-overlap bound forces weight `≥ 99 - 33 - 33 = 33 > 0` on `qL ∩ qR`.
  -- `univ ∩ univ = univ` as a *term* (no kernel computation of the intersection).
  have key := quorum_intersection_weight_lower τ stake hqLsub hqRsub hqL.2 hqR.2
  have hself : wt stake (vsetL bL ∩ vsetL bR) = wt stake (Finset.univ : Finset V) :=
    congrArg (wt stake) (Finset.inter_self (Finset.univ : Finset V))
  have hfast : (33 : Nat) ≤ wt stake (Finset.univ : Finset V)
      - τ.one_third (wt stake Finset.univ) - τ.one_third (wt stake Finset.univ) := by decide
  have h33 : (33 : Nat) ≤ wt stake (qL ∩ qR) :=
    le_trans
      (le_of_le_of_eq hfast
        (congrArg
          (fun x => x - τ.one_third (wt stake Finset.univ)
                      - τ.one_third (wt stake Finset.univ)) hself.symm))
      key
  -- (ii) Yet every member of `qL ∩ qR` would be slashed in `∅` (impossible), so each
  -- summand `stake v` is *vacuously* `0`; hence the weight is `0` — choice-free, with
  -- no element extraction (`Finset.exists_ne_zero_of_sum_ne_zero` would pull choice).
  have hz : wt stake (qL ∩ qR) = 0 :=
    Finset.sum_eq_zero (fun v hv =>
      absurd (hsl v (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)
             (empty_not_slashed v))
  -- (iii) `33 ≤ wt (qL ∩ qR) = 0` is a contradiction.
  exact absurd (le_of_le_of_eq h33 hz) (by decide)


/-! ### 3. Blocks exist at every height (the linear chain) -/

/-- In the linear chain, `b + n` is the `n`-th descendant of `b`. -/
theorem nth_anc_chain : ∀ (b n : Nat), nth_ancestor parentL n b (b + n)
  | b, 0 => nth_ancestor.nth_ancestor_0 b
  | b, n + 1 => nth_ancestor.nth_ancestor_nth (nth_anc_chain b n) rfl

/-- Above any block, blocks exist at all heights `> 1`. -/
theorem blocks_high : ∀ b : Nat, blocks_exist_high_over parentL b :=
  fun b n _ => ⟨b + n, nth_anc_chain b n⟩


/-! ### 4. Plausible liveness: a finalizing extension always exists

`Core.plausible_liveness_construct_extension`, applied to `∅`: there is an
extension `st'` that adds only unslashed votes, slashes no one new, and in which a
fresh block `nf` is justified with a supermajority-linked child `nc` — i.e. the
gadget can always make finality progress. -/

theorem plausible_liveness_from_empty :
    ∃ st' : State V Nat,
      unslashed_can_extend (∅ : State V Nat) st' ∧
      no_new_slashed (∅ : State V Nat) st' ∧
      ∃ nf nc : Nat, ∃ nh : Nat,
        justified τ stake vsetL parentL genesisL st' nf nh ∧
        parentL nf nc ∧
        supermajority_link τ stake vsetL st' nf nc nh (nh + 1) :=
  plausible_liveness_construct_extension τ stake vsetL parentL genesisL ∅
    qctxL two_thirds_good_empty unslashed_empty good_votes_empty wf_empty
    (fun b _ _ => blocks_high b)


/-! ### 5. The executable liveness-side checkers (concrete utilization)

The liveness hypothesis `two_thirds_good` asks, at every block, for a *good
quorum*: a 2/3 quorum all of whose members are unslashed. `Executable.goodQuorumAtB`
decides this from finite data and `Executable.notSlashedB` decides un-slashability,
so the gadget can *select* a good quorum that **avoids** any slashed validator.

We show the checkers discriminate on a state where validator `0` double-votes: the
whole committee is **not** a good quorum (it contains the slashed `0`), but the
committee with `0` removed **is** — and still has weight `98 ≥ two_third 99 = 66`. -/

/-- A state where validator `0` double-votes (targets `1 ≠ 2` at height `5`). -/
def stLive : State V Nat :=
  { { validator := 0, source := 0, target := 1, sourceHeight := 0, targetHeight := 5 },
    { validator := 0, source := 0, target := 2, sourceHeight := 0, targetHeight := 5 } }

#eval notSlashedB stLive 0                                        -- false  (0 double-voted)
#eval notSlashedB stLive 1                                        -- true
#eval goodQuorumAtB τ stake vsetL stLive 0 Finset.univ           -- false  (univ ∋ slashed 0)
#eval goodQuorumAtB τ stake vsetL stLive 0 (Finset.univ.filter (fun v => v ≠ (0 : V)))
                                                                 -- true   (avoids 0; weight 98)

/-- Validator `0` is slashed in `stLive` (explicit double-vote witness: targets
`1 ≠ 2` at the common target height `5`). -/
theorem slashed_0 : slashed stLive 0 :=
  Or.inl ⟨1, 2, by decide, 0, 0, 0, 0, 5, by decide, by decide⟩

/-- Every vote in `stLive` is cast by validator `0` — it is the only voter. -/
theorem mem_stLive_val {w : Vote V Nat} (hw : w ∈ stLive) : w.validator = 0 :=
  (Finset.mem_insert.mp hw).elim
    (fun h => congrArg Vote.validator h)
    (fun h => congrArg Vote.validator (Finset.mem_singleton.mp h))

/-- Hence only validator `0` can be slashed in `stLive` (no other validator votes). -/
theorem only_0_slashed {v : V} (hsl : slashed stLive v) : v = 0 := by
  rcases hsl with ⟨_, _, _, _, _, _, _, _, hv, _⟩ | ⟨_, _, _, _, _, _, _, _, hv, _, _, _⟩
  · exact mem_stLive_val hv
  · exact mem_stLive_val hv

/-- The whole committee is *not* a good quorum at block `0` of `stLive` — it
contains the slashed validator `0`. (Constructive: `0 ∈ univ` and `slashed_0`.) -/
theorem univ_not_good : ¬ IsGoodQuorumAt τ stake vsetL stLive 0 Finset.univ :=
  fun ⟨_, hall⟩ => hall 0 (Finset.mem_univ 0) slashed_0

/-- The committee with `0` removed *is* a good quorum at block `0`: a 2/3 quorum
(weight `98 ≥ two_third 99 = 66`) all of whose members are unslashed — because `0`
is the only voter in `stLive`. We use `filter (· ≠ 0)` (choice-free) rather than
`Finset.erase` (which pulls `Classical.choice` in this Mathlib). -/
theorem erase0_good :
    IsGoodQuorumAt τ stake vsetL stLive 0 (Finset.univ.filter (fun v => v ≠ (0 : V))) :=
  ⟨⟨Finset.filter_subset _ _,
     (by decide : τ.two_third (wt stake (Finset.univ : Finset V))
        ≤ wt stake (Finset.univ.filter (fun v => v ≠ (0 : V))))⟩,
   fun v hv hsl => (Finset.mem_filter.mp hv).2 (only_0_slashed hsl)⟩

/-- `two_thirds_good` is exactly "a checkable good quorum exists at every block"
(`Executable.two_thirds_good_iff_forall_exists_goodQuorum`) — the bridge from the
Core liveness hypothesis to the executable checker. -/
theorem two_thirds_good_as_checker (st : State V Nat) :
    two_thirds_good τ stake vsetL st ↔
    ∀ b : Nat, ∃ q2 : Finset V, IsGoodQuorumAt τ stake vsetL st b q2 :=
  two_thirds_good_iff_forall_exists_goodQuorum τ stake vsetL st

end GasperBeaconChain.Executable.UseCases
