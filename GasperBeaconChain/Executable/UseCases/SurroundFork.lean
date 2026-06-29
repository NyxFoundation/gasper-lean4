import GasperBeaconChain.Executable.UseCases.ModelN

/-!
# Use case — the S2 (surround) slashing condition, forced by a skip-link fork

**Scenario (Buterin–Griffith Thm 1 / Fig. 3; Gasper Lemma 5.1 surround case).**
The first slashing condition S1 (double vote, same target height) is exercised by the
equal-height fork in `AccountableSafety`.  Here we exercise the *second* condition,

$$\textbf{S2 (surround):}\qquad h(s_1) < h(s_2) < h(t_2) < h(t_1),$$

which can only arise when a checkpoint is justified by a **skip link** spanning more
than one height.  On the deep tree of `ModelN` we finalize two conflicting blocks at
**different heights**:

```text
            0   (genesis)                  left finalizes block 1 (height 1):
          /   \                              0 ⇒ 1   (justify),  1 ⇒ 2  (finalize)
   1  ⇐⇒  ...  6                            right finalizes block 6 (height 3):
   |          |                               0 ⇒ 6   (SKIP, justify),  6 ⇒ 7 (finalize)
   2          7
```

The right justification is the **skip link** `0 ⇒ 6` over heights `0→3` (`nth_ancestor 3`
along `0⋖4⋖5⋖6`).  Its interval `[0,3]` strictly contains the left finalized interval
`[1,2]` (the link `1 ⇒ 2`):

$$h(0)=0 \;<\; h(1)=1 \;<\; h(2)=2 \;<\; h(6@\text{src }0)=3 .$$

So every validator supporting *both* the skip link `0⇒6` and the finalizing link `1⇒2`
has committed S2.  We feed the conflicting finalization to the **real** Core theorem
`accountable_safety` to obtain a slashable quorum intersection, and we *also* exhibit the
explicit surround witness for every quorum member.  Size-parametric in `N`,
`Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

/-- The forking vote set: four supermajority links, all supported by the canonical 2/3
quorum `qTT`.  Left: `0⇒1` (justify), `1⇒2` (finalize).  Right: `0⇒6` (SKIP justify),
`6⇒7` (finalize). -/
def stFork : State (Fin N) H :=
  fUnion (fUnion (fUnion
    (votes_for_link (qTT N) 0 1 0 1)
    (votes_for_link (qTT N) 1 2 1 2))
    (votes_for_link (qTT N) 0 6 0 3))
    (votes_for_link (qTT N) 6 7 3 4)

/-! ### 1. The four links sit inside the fork state (structural) -/

theorem sub_01 : votes_for_link (qTT N) 0 1 0 1 ⊆ stFork N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_left hv))
theorem sub_12 : votes_for_link (qTT N) 1 2 1 2 ⊆ stFork N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_right hv))
theorem sub_06 : votes_for_link (qTT N) 0 6 0 3 ⊆ stFork N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem sub_67 : votes_for_link (qTT N) 6 7 3 4 ⊆ stFork N :=
  fun _ hv => mem_fUnion_right hv

/-! ### 2. Supermajority links from the 2/3 quorum (Core lemma, no enumeration) -/

theorem sm_01 : supermajority_link τ (stake N) (vset N) (stFork N) 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 1) (sub_01 N) (wf_vset N _)
theorem sm_12 : supermajority_link τ (stake N) (vset N) (stFork N) 1 2 1 2 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 2) (sub_12 N) (wf_vset N _)
theorem sm_06 : supermajority_link τ (stake N) (vset N) (stFork N) 0 6 0 3 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 6) (sub_06 N) (wf_vset N _)
theorem sm_67 : supermajority_link τ (stake N) (vset N) (stFork N) 6 7 3 4 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 7) (sub_67 N) (wf_vset N _)

/-! ### 3. Justification and finalization of the two conflicting blocks -/

/-- Left block `1` is justified at height `1` (link `0 ⇒ 1`). -/
theorem just_1 : justified τ (stake N) (vset N) parent genesis (stFork N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, sm_01 N⟩

/-- Left block `1` is finalized at height `1` (finalizing child `2`, link `1 ⇒ 2`). -/
theorem fin_1 : finalized τ (stake N) (vset N) parent genesis (stFork N) 1 1 :=
  ⟨just_1 N, 2, pe_12, sm_12 N⟩

/-- Right block `6` is justified at height `3` via the **skip link** `0 ⇒ 6`. -/
theorem just_6 : justified τ (stake N) (vset N) parent genesis (stFork N) 6 3 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_6, sm_06 N⟩

/-- Right block `6` is finalized at height `3` (finalizing child `7`, link `6 ⇒ 7`). -/
theorem fin_6 : finalized τ (stake N) (vset N) parent genesis (stFork N) 6 3 :=
  ⟨just_6 N, 7, pe_67, sm_67 N⟩

/-! ### 4. The different-height finalization fork and accountable safety -/

/-- Blocks `1` (height 1, left) and `6` (height 3, right) are both finalized and
conflicting — a finalization fork at **different heights**. -/
theorem the_fork : finalization_fork τ (stake N) (vset N) parent genesis (stFork N) :=
  ⟨1, 1, 6, 3, fin_1 N, fin_6 N, not_anc_6_1, not_anc_1_6⟩

/-- **Accountable safety** (the real Core theorem): the fork forces a slashable quorum
intersection. -/
theorem fork_slashable : q_intersection_slashed τ (stake N) (vset N) (stFork N) :=
  accountable_safety τ (stake N) (vset N) parent genesis (stFork N) (the_fork N)

/-! ### 5. The explicit S2 evidence

Every quorum member supports both the skip link `0⇒6` (heights `0→3`, *outer*) and the
finalizing link `1⇒2` (heights `1→2`, *inner*); the inner interval is strictly nested in
the outer one, so each is provably slashed by **S2**. -/

/-- For every validator in the quorum, the surround condition holds explicitly:
outer `0⇒6 @[0,3]`, inner `1⇒2 @[1,2]`, with `0 < 1` and `2 < 3`. -/
theorem qTT_surround {v : Fin N} (hv : v ∈ qTT N) :
    slashed_surround_vote (stFork N) v :=
  ⟨0, 6, 0, 3, 1, 2, 1, 2,
   sub_06 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩),
   sub_12 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩),
   by decide, by decide⟩

/-- Hence every quorum member is `Core.slashed` — via condition S2 (not S1). -/
theorem qTT_slashed {v : Fin N} (hv : v ∈ qTT N) : slashed (stFork N) v :=
  Or.inr (qTT_surround N hv)

end

/-! ### 6. Executable cross-check at a sample committee size (`N = 111`, the Gasper paper's
heuristic) — the Boolean oracles agree with the proved facts. -/

#eval slashedB (stFork 111) ⟨0, by decide⟩          -- true  (validator 0 surround-slashed)
#eval (slashedB (stFork 111) ⟨0, by decide⟩
       && slashedB (stFork 111) ⟨65, by decide⟩)    -- true  (65 < 74 = two_third 111, in qTT)
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stFork 111) 1 1   -- true
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stFork 111) 6 3   -- true (skip link)
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stFork 111) 3 3   -- false (block 3 unvoted)

end GasperBeaconChain.Executable.UseCases.Parametric
