import GasperBeaconChain.Executable.UseCases.Model
import GasperBeaconChain.Core.Lemmas.PlausibleLiveness
import GasperBeaconChain.Audit.Meta.View.ViewCommandGroup

/-!
# Use case — Accountable safety at committee scale (the heart of Casper FFG)

**Scenario.** A safety violation on a 99-validator committee: two conflicting
checkpoints `1` (left branch) and `4` (right branch) **both get finalized**.
Casper FFG's accountable-safety theorem (Buterin–Griffith Thm 1; Gasper Thm 3.2)
says this is impossible unless validators of total weight `≥ N/3` provably
violated a slashing condition. Here we *build the violation* and *compute the
slashed quorum intersection*, on a paper-sized committee.

The attack (tree from `Model`): genesis `0` has two conflicting children `1`, `4`.

```text
            0  (genesis)
          /   \
   qL ⇊ /       \ ⇊ qR     qL = {0..65}  vote 0→1   (target height 1)
       1         4         qR = {33..98} vote 0→4   (target height 1)
       |         |
       2         5         qL ∩ qR = {33..65}  ·  double-vote (targets 1≠4, h=1)
```

Each link carries weight `66 = two_third 99`, so `1` and `4` are justified and
(via their children `2`, `5`) finalized. But `qL`, `qR` are 2/3 quorums of the
*same* 99-validator set, so they overlap in weight `66 + 66 - 99 = 33 = one_third
99`: validators `{33..65}` voted for **both** `1` and `4` at the same target
height — a double vote (condition I). Their weight is exactly the `N/3` bound.

**Construction.** At this scale we do not hand-list ~260 votes. The state is
assembled with Core's own `votes_for_link` / `fUnion`, and the four supermajority
links are discharged by `supermajority_link_of_quorum_votes` — the same lemma the
Core plausible-liveness proof uses to certify the links of its extension. The
oracle facts (`slashedB`, `justifiedB`, `qIntersectionWitnessB`, weights) are
shown by **compiled `#eval`** (fast at any `N`), and the logical verdict comes
from the **actual Core theorem** `accountable_safety`. `Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

/-- Left quorum: the first `66` validators (`{0..65}`), weight `two_third 99`. -/
def qL : Finset V := Finset.univ.filter (fun v => v.val < 66)

/-- Right quorum: the last `66` validators (`{33..98}`), weight `two_third 99`.
Overlaps `qL` in `{33..65}` — the `one_third 99 = 33` double voters. -/
def qR : Finset V := Finset.univ.filter (fun v => 33 ≤ v.val)

/-- The forking vote set, assembled with Core's `votes_for_link` / `fUnion`:
four supermajority links — `0→1`, `0→4` (the conflicting justifications), `1→2`,
`4→5` (the finalizing children). -/
def stFork : State V H :=
  fUnion (fUnion (fUnion
    (votes_for_link qL 0 1 0 1)
    (votes_for_link qR 0 4 0 1))
    (votes_for_link qL 1 2 1 2))
    (votes_for_link qR 4 5 1 2)


/-! ### 1. Computation at committee scale (`#eval`, compiled)

These run natively on the 99-validator instance: the watchtower output is exactly
the `33` double voters, and the quorum-intersection checker confirms the slashing. -/

#eval slashedB stFork 33   -- true   (a double voter in qL ∩ qR)
#eval slashedB stFork 0    -- false  (qL only: votes 0→1 and 1→2, distinct target heights)
#eval ((List.finRange 99).filter (fun v => slashedB stFork v)).length  -- 33  (= one_third 99)
#eval justifiedB τ stake vset parent genesis stFork 1 1   -- true
#eval justifiedB τ stake vset parent genesis stFork 4 1   -- true
#eval justifiedB τ stake vset parent genesis stFork 3 3   -- false  (no votes for block 3)
#eval qIntersectionWitnessB τ stake vset stFork 1 4 qL qR -- true   (the intersection is slashed)
#eval wt stake (qL ∩ qR)                     -- 33
#eval τ.one_third (wt stake (vset 1))        -- 33   (= one_third 99 = N/3)
#eval τ.two_third (wt stake (vset 1))        -- 66   (= two_third 99)


/-! ### 2. Theorem layer: justify, finalize, fork, accountable safety

Every supermajority link is proved from its quorum via the Core lemma
`supermajority_link_of_quorum_votes` (no enumeration over the state); the only
`decide`s are the single quorum-weight check and concrete `Fin`/`Nat` facts. -/

/-- Well-formedness: every link supporter lies in the (universal) target set. -/
theorem wf_stFork : votes_from_target_vset_property vset stFork := by
  intro x s t s_h t_h _; exact Finset.mem_univ x

/-- `qL` is a 2/3 quorum at every block: it lies in the (universal) validator set
and its weight `66` meets `two_third 99 = 66`. The subset side is structural; only
the closed weight inequality is decided. -/
theorem q2_qL (t : H) : quorum_2 τ stake vset qL t :=
  ⟨Finset.subset_univ qL,
   (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake qL)⟩

/-- `qR` is a 2/3 quorum at every block. -/
theorem q2_qR (t : H) : quorum_2 τ stake vset qR t :=
  ⟨Finset.subset_univ qR,
   (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake qR)⟩

-- The four vote-blocks sit inside the fork state (structural, no computation):
theorem sub_L1 : votes_for_link qL 0 1 0 1 ⊆ stFork :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_left hv))
theorem sub_L2 : votes_for_link qR 0 4 0 1 ⊆ stFork :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_right hv))
theorem sub_L3 : votes_for_link qL 1 2 1 2 ⊆ stFork :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem sub_L4 : votes_for_link qR 4 5 1 2 ⊆ stFork :=
  fun _ hv => mem_fUnion_right hv

-- The four supermajority links, from quorum + membership + well-formedness:
theorem sm_L1 : supermajority_link τ stake vset stFork 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qL 1) sub_L1 wf_stFork
theorem sm_L2 : supermajority_link τ stake vset stFork 0 4 0 1 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qR 4) sub_L2 wf_stFork
theorem sm_L3 : supermajority_link τ stake vset stFork 1 2 1 2 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qL 2) sub_L3 wf_stFork
theorem sm_L4 : supermajority_link τ stake vset stFork 4 5 1 2 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qR 5) sub_L4 wf_stFork

/-- Block `1` is justified at height `1` (supermajority link `0 → 1`). -/
theorem justified_b1 : justified τ stake vset parent genesis stFork 1 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) (by decide), sm_L1⟩

/-- Block `4` is justified at height `1` (supermajority link `0 → 4`). -/
theorem justified_b4 : justified τ stake vset parent genesis stFork 4 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) (by decide), sm_L2⟩

/-- Block `1` is finalized (justified, finalizing child `2` via link `1 → 2`). -/
theorem finalized_b1 : finalized τ stake vset parent genesis stFork 1 1 :=
  ⟨justified_b1, 2, by decide, sm_L3⟩

/-- Block `4` is finalized (justified, finalizing child `5` via link `4 → 5`). -/
theorem finalized_b4 : finalized τ stake vset parent genesis stFork 4 1 :=
  ⟨justified_b4, 5, by decide, sm_L4⟩

/-- The two finalized conflicting checkpoints form a finalization fork. -/
theorem the_fork : finalization_fork τ stake vset parent genesis stFork :=
  ⟨1, 1, 4, 1, finalized_b1, finalized_b4,
   not_hash_ancestor_4_1, not_hash_ancestor_1_4⟩

/-- **Accountable safety**: the fork forces a slashable quorum intersection.
This is `Core.accountable_safety` applied to our concrete committee-scale fork. -/
theorem fork_is_slashable : q_intersection_slashed τ stake vset stFork :=
  accountable_safety τ stake vset parent genesis stFork the_fork

/-- The safety theorem's witness is certifiable by the executable checker. -/
theorem fork_witnessB_exists :
    ∃ bL bR : H, ∃ qL' qR' : Finset V,
      qIntersectionWitnessB τ stake vset stFork bL bR qL' qR' = true :=
  accountable_safety_witnessB τ stake vset parent genesis stFork the_fork


/-! ### 3. The slashing evidence, explicitly

Validator `33` (in `qL ∩ qR`) voted `0 → 1` and `0 → 4`, both at target height
`1` — the on-chain double-vote evidence. We build it structurally (membership in
`votes_for_link`), so no large kernel computation is incurred. -/

theorem mem33_qL : (33 : V) ∈ qL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩
theorem mem33_qR : (33 : V) ∈ qR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩

/-- Explicit double-vote witness for validator `33`. -/
theorem v33_double_vote : slashed_double_vote stFork 33 :=
  ⟨1, 4, by decide, 0, 0, 0, 0, 1,
   sub_L1 (mem_votes_for_link.mpr ⟨33, mem33_qL, rfl⟩),
   sub_L2 (mem_votes_for_link.mpr ⟨33, mem33_qR, rfl⟩)⟩

/-- Hence validator `33` is `Core.slashed`. -/
theorem v33_slashed : slashed stFork 33 := Or.inl v33_double_vote

end GasperBeaconChain.Executable.UseCases

/-! ## View data — regenerated automatically when this file is (re)built

A single no-argument trigger publishes *this* module's `types`-facet data to
`View/data/structures/types/Executable.UseCases.AccountableSafety.json`.  No argument is needed: the
proof terms here (e.g. `fork_is_slashable := accountable_safety … the_fork`) already reference the
Core theorems, so the abstract dependency is captured in-place. -/
#mr_view_types
