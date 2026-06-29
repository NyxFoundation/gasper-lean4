import GasperBeaconChain.Executable.UseCases.ModelN
import GasperBeaconChain.Core.Theories.PlausibleLiveness
import GasperBeaconChain.Core.Theories.SlashableBound

/-!
# Use case — plausible liveness, size-parametric (Gasper Thm 6.1 / Casper FFG Thm 2)

*No deadlock.* From the **empty** state (nothing justified beyond genesis), if the honest
validators form a 2/3 quorum it is always *possible* to extend the state so that a fresh
block becomes justified with a supermajority-linked child — **without any honest validator
slashing itself**.  Its `no_new_slashed` conclusion is precisely the statement that the
honest extension creates **no new S1 *or* S2 violation** (Gasper Prop. 4.12: honest
validators never surround-vote).

Liveness needs an *unbounded* supply of blocks, so the block space is `Hash = ℕ` with the
linear chain `parent a b ↔ b = a+1`.  The committee is the choice-free `Fin N` for **any**
`N ≥ 3` (the legacy `Liveness` fixed `N = 99` and discharged threshold positivity by
`decide`; here it is proved by **explicit, constructive Nat lemmas** — no `omega`).

The single quantitative fact is the 2/3-overlap pigeonhole: two 2/3 quorums of an
`N`-committee intersect in weight `≥ N - 2·one_third N > 0`, yet the empty state slashes no
one — so `∅` is not `q_intersection_slashed`.  `Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

/- The explicit threshold arithmetic (`one_third_eq`, `two_third_pos`, `two_div_three_lt`,
`overlap_pos`) now lives in `ModelN` as the shared foundation; it is in scope here. -/


/-! ## 1. The liveness block space (`Hash = ℕ`, linear chain) -/

/-- Genesis of the liveness block space. -/
def genesisL : Nat := 0

/-- Linear parent chain: `b` is the child of `a` iff `b = a + 1` — a block at every height. -/
def parentL : Nat → Nat → Prop := fun a b => b = a + 1

instance : DecidableRel parentL := fun a b => by unfold parentL; infer_instance

/-- In the linear chain, `b + n` is the `n`-th descendant of `b`. -/
theorem nth_anc_chain : ∀ (b n : Nat), nth_ancestor parentL n b (b + n)
  | b, 0 => nth_ancestor.nth_ancestor_0 b
  | b, n + 1 => nth_ancestor.nth_ancestor_nth (nth_anc_chain b n) rfl

/-- Above any block, blocks exist at all heights `> 1`. -/
theorem blocks_high (b : Nat) : blocks_exist_high_over parentL b :=
  fun n _ => ⟨b + n, nth_anc_chain b n⟩


/-! ## 2. Committee, and the (mostly vacuous) empty-state hypotheses -/

section
variable (N : Nat)

/-- Static universal validator set over the `ℕ`-indexed blocks. -/
def vsetL : Nat → Finset (Fin N) := fun _ => Finset.univ

/-- The committee weight at every block is `N`. -/
theorem wt_vsetL (b : Nat) : wt (stake N) (vsetL N b) = N := wt_one_univ N

/-- No validator is slashable in the empty state (no votes ⇒ no condition violated). -/
theorem empty_not_slashed (v : Fin N) : ¬ slashed (∅ : State (Fin N) Nat) v := by
  rintro (⟨_, _, _, _, _, _, _, _, hv, _⟩ | ⟨_, _, _, _, _, _, _, _, hv, _, _, _⟩)
  · exact absurd hv (Finset.notMem_empty _)
  · exact absurd hv (Finset.notMem_empty _)

/-- Every block has a good quorum: the whole committee (a 2/3 quorum, none slashed in `∅`). -/
theorem two_thirds_good_empty :
    two_thirds_good τ (stake N) (vsetL N) (∅ : State (Fin N) Nat) :=
  fun b => ⟨Finset.univ,
    ⟨Finset.subset_univ _,
     le_of_eq_of_le (congrArg τ.two_third (wt_vsetL N b))
       (le_of_le_of_eq (τ.leq_two_thirds N) (wt_one_univ N).symm)⟩,
    fun v _ => empty_not_slashed N v⟩

/-- Vacuous: the empty state's (nonexistent) link supporters lie in any target set. -/
theorem wf_empty : votes_from_target_vset_property (vsetL N) (∅ : State (Fin N) Nat) :=
  fun {_} {_} {_} {_} {_} hx => absurd (mem_link_supporters.mp hx) (Finset.notMem_empty _)

/-- Vacuous: the empty state's (nonexistent) votes are well-formed. -/
theorem good_votes_empty :
    good_votes τ (stake N) (vsetL N) parentL genesisL (∅ : State (Fin N) Nat) :=
  fun _ _ _ _ _ =>
    ⟨fun _ _ _ _ hvm => absurd hvm (Finset.notMem_empty _),
     fun _ _ _ _ hvm => absurd hvm (Finset.notMem_empty _)⟩

/-- Two-thirds quorums are nonempty (`two_third N > 0`). -/
theorem qctxL (hN : 3 ≤ N) : QuorumContext τ (stake N) (vsetL N) :=
  quorum_context_of_threshold_pos τ (stake N) (vsetL N)
    (fun b => Eq.subst (motive := fun x => 0 < τ.two_third x) (wt_vsetL N b).symm
      (two_third_pos hN))

/-- The empty state is **not** `q_intersection_slashed`: any two 2/3 quorums of the
`N`-committee overlap in weight `≥ N - 2·one_third N > 0`, yet `∅` slashes no one. -/
theorem unslashed_empty (hN : 3 ≤ N) :
    ¬ q_intersection_slashed τ (stake N) (vsetL N) (∅ : State (Fin N) Nat) := by
  rintro ⟨bL, bR, qL, qR, hqLsub, hqRsub, hqL, hqR, hsl⟩
  have key := quorum_intersection_weight_lower τ (stake N) hqLsub hqRsub hqL.2 hqR.2
  have hinter : wt (stake N) (vsetL N bL ∩ vsetL N bR) = N :=
    (congrArg (wt (stake N)) (Finset.inter_self (Finset.univ : Finset (Fin N)))).trans
      (wt_one_univ N)
  have heq :
      wt (stake N) (vsetL N bL ∩ vsetL N bR)
        - τ.one_third (wt (stake N) (vsetL N bL))
        - τ.one_third (wt (stake N) (vsetL N bR))
        = N - τ.one_third N - τ.one_third N :=
    congrArg₂ (· - ·)
      (congrArg₂ (· - ·) hinter (congrArg τ.one_third (wt_vsetL N bL)))
      (congrArg τ.one_third (wt_vsetL N bR))
  have hpos : 0 < wt (stake N) (qL ∩ qR) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_eq (overlap_pos hN) heq.symm) key
  have hz : wt (stake N) (qL ∩ qR) = 0 :=
    Finset.sum_eq_zero (fun v hv =>
      absurd (hsl v (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)
             (empty_not_slashed N v))
  exact absurd (Nat.lt_of_lt_of_eq hpos hz) (Nat.lt_irrefl 0)


/-! ## 3. Plausible liveness: a finalizing, slash-free extension always exists -/

/-- **Plausible liveness** (the real Core theorem `plausible_liveness_construct_extension`):
from `∅` there is an extension adding only unslashed votes, slashing **no one new** (no new
S1 or S2 — Prop. 4.12), in which a fresh block `nf` is justified with a supermajority-linked
child `nc`. -/
theorem plausible_liveness_from_empty (hN : 3 ≤ N) :
    ∃ st' : State (Fin N) Nat,
      unslashed_can_extend (∅ : State (Fin N) Nat) st' ∧
      no_new_slashed (∅ : State (Fin N) Nat) st' ∧
      ∃ nf nc : Nat, ∃ nh : Nat,
        justified τ (stake N) (vsetL N) parentL genesisL st' nf nh ∧
        parentL nf nc ∧
        supermajority_link τ (stake N) (vsetL N) st' nf nc nh (nh + 1) :=
  plausible_liveness_construct_extension τ (stake N) (vsetL N) parentL genesisL ∅
    (qctxL N hN) (two_thirds_good_empty N) (unslashed_empty N hN)
    (good_votes_empty N) (wf_empty N) (fun b _ _ => blocks_high b)

end

/-! ### Executable cross-check (`N = 111`): the empty state slashes no one. -/

#eval ((List.finRange 111).filter (fun v => slashedB (∅ : State (Fin 111) Nat) v)).length  -- 0

end GasperBeaconChain.Executable.UseCases.Parametric
