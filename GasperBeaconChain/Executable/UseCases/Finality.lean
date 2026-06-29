import GasperBeaconChain.Executable.UseCases.Model
import GasperBeaconChain.Core.Lemmas.PlausibleLiveness

/-!
# Use case — the finality gadget: justification & finalization (committee scale)

**Scenario.** A node computes the *finalized prefix* of the checkpoint tree: which
checkpoints are **justified** (reachable from genesis by a chain of 2/3
supermajority links) and which are **finalized** (justified, with a justified
direct child one height above). This is the heart of Casper FFG / Gasper.

On the 99-validator committee, the state casts three 2/3 supermajority links
`0→1→2→3` along the main chain, each supported by the quorum `{0..65}`
(`66 = two_third 99`), assembled with Core's `votes_for_link` / `fUnion`. We then:

1. **compute** which `(block, height)` pairs are justified (`#eval justifiedB`);
2. **prove** the justification chain `0 ⊢ 1 ⊢ 2 ⊢ 3` from the inductive
   constructors, each link discharged by `supermajority_link_of_quorum_votes`;
3. **construct finalization** of an interior checkpoint — the gadget's output.

`Classical.choice`-free throughout.
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

/-- The chain quorum: the first `66` validators (`two_third 99`). -/
def qF : Finset V := Finset.univ.filter (fun v => v.val < 66)

/-- The vote set: three 2/3 supermajority links along the main chain
`0→1 @[0,1]`, `1→2 @[1,2]`, `2→3 @[2,3]`, each supported by `qF`. -/
def stFinality : State V H :=
  fUnion (fUnion
    (votes_for_link qF 0 1 0 1)
    (votes_for_link qF 1 2 1 2))
    (votes_for_link qF 2 3 2 3)

/-- Shorthand for the justification oracle on this instance. -/
abbrev J : H → Nat → Bool :=
  justifiedB τ stake vset parent genesis stFinality


/-! ### 1. The justification oracle (`#eval`, committee scale) -/

#eval J 0 0   -- true   (genesis)
#eval J 1 1   -- true   (link 0→1)
#eval J 2 2   -- true   (link 1→2)
#eval J 3 3   -- true   (link 2→3 — the whole main chain is justified)
#eval J 4 1   -- false  (fork block 4 has no supermajority link)
#eval J 1 5   -- false  (block 1 is justified only at its own height 1)


/-! ### 2. Proving the justification chain

Each link is `supermajority_link_of_quorum_votes` of the quorum `qF`; the chain
grows by the `justified.justified_link` constructor. -/

theorem wf_stFinality : votes_from_target_vset_property vset stFinality := by
  intro x s t s_h t_h _; exact Finset.mem_univ x

theorem q2_qF (t : H) : quorum_2 τ stake vset qF t :=
  ⟨Finset.subset_univ qF,
   (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake qF)⟩

theorem sub_01 : votes_for_link qF 0 1 0 1 ⊆ stFinality :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left hv)
theorem sub_12 : votes_for_link qF 1 2 1 2 ⊆ stFinality :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem sub_23 : votes_for_link qF 2 3 2 3 ⊆ stFinality :=
  fun _ hv => mem_fUnion_right hv

theorem sm_01 : supermajority_link τ stake vset stFinality 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qF 1) sub_01 wf_stFinality
theorem sm_12 : supermajority_link τ stake vset stFinality 1 2 1 2 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qF 2) sub_12 wf_stFinality
theorem sm_23 : supermajority_link τ stake vset stFinality 2 3 2 3 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qF 3) sub_23 wf_stFinality

/-- Block `1` is justified at height `1`. -/
theorem block1_justified : justified τ stake vset parent genesis stFinality 1 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) (by decide), sm_01⟩

/-- Block `2` is justified at height `2`. -/
theorem block2_justified : justified τ stake vset parent genesis stFinality 2 2 :=
  justified.justified_link block1_justified
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 1) (by decide), sm_12⟩

/-- Block `3` is justified at height `3` — the whole main chain. -/
theorem block3_justified : justified τ stake vset parent genesis stFinality 3 3 :=
  justified.justified_link block2_justified
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 2) (by decide), sm_23⟩

/-- Completeness: the fork block `4` is **not** justified at height `1`. -/
theorem block4_not_justified : ¬ justified τ stake vset parent genesis stFinality 4 1 :=
  fun h => absurd ((justifiedB_iff τ stake vset parent genesis stFinality 4 1).mpr h) (by decide)


/-! ### 3. Finalization — the gadget's output

Block `1` is finalized: justified at height `1`, with finalizing child `2`
reached by the supermajority link `1 → 2`. -/

/-- Block `1` is finalized. -/
theorem block1_finalized : finalized τ stake vset parent genesis stFinality 1 1 :=
  ⟨block1_justified, 2, by decide, sm_12⟩

/-- Equivalently, block `1` is `1`-finalized (`k_finalized` at `k = 1`). -/
theorem block1_k_finalized :
    k_finalized τ stake vset parent genesis stFinality 1 1 1 :=
  (finalized_means_one_finalized τ stake vset parent genesis stFinality 1 1).mp block1_finalized

end GasperBeaconChain.Executable.UseCases
