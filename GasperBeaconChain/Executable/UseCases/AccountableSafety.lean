import GasperBeaconChain.Executable.UseCases.Model
import GasperBeaconChain.Core.Lemmas.PlausibleLiveness


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

def qL : Finset V := Finset.univ.filter (fun v => v.val < 66)

def qR : Finset V := Finset.univ.filter (fun v => 33 ≤ v.val)

def stFork : State V H :=
  fUnion (fUnion (fUnion
    (votes_for_link qL 0 1 0 1)
    (votes_for_link qR 0 4 0 1))
    (votes_for_link qL 1 2 1 2))
    (votes_for_link qR 4 5 1 2)



#eval slashedB stFork 33
#eval slashedB stFork 0
#eval ((List.finRange 99).filter (fun v => slashedB stFork v)).length
#eval justifiedB τ stake vset parent genesis stFork 1 1
#eval justifiedB τ stake vset parent genesis stFork 4 1
#eval justifiedB τ stake vset parent genesis stFork 3 3
#eval qIntersectionWitnessB τ stake vset stFork 1 4 qL qR
#eval wt stake (qL ∩ qR)
#eval τ.one_third (wt stake (vset 1))
#eval τ.two_third (wt stake (vset 1))



theorem wf_stFork : votes_from_target_vset_property vset stFork := by
  intro x s t s_h t_h _; exact Finset.mem_univ x

theorem q2_qL (t : H) : quorum_2 τ stake vset qL t :=
  ⟨Finset.subset_univ qL,
   (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake qL)⟩

theorem q2_qR (t : H) : quorum_2 τ stake vset qR t :=
  ⟨Finset.subset_univ qR,
   (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake qR)⟩

theorem sub_L1 : votes_for_link qL 0 1 0 1 ⊆ stFork :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_left hv))
theorem sub_L2 : votes_for_link qR 0 4 0 1 ⊆ stFork :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_right hv))
theorem sub_L3 : votes_for_link qL 1 2 1 2 ⊆ stFork :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem sub_L4 : votes_for_link qR 4 5 1 2 ⊆ stFork :=
  fun _ hv => mem_fUnion_right hv

theorem sm_L1 : supermajority_link τ stake vset stFork 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qL 1) sub_L1 wf_stFork
theorem sm_L2 : supermajority_link τ stake vset stFork 0 4 0 1 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qR 4) sub_L2 wf_stFork
theorem sm_L3 : supermajority_link τ stake vset stFork 1 2 1 2 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qL 2) sub_L3 wf_stFork
theorem sm_L4 : supermajority_link τ stake vset stFork 4 5 1 2 :=
  supermajority_link_of_quorum_votes τ stake vset (q2_qR 5) sub_L4 wf_stFork

theorem justified_b1 : justified τ stake vset parent genesis stFork 1 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) (by decide), sm_L1⟩

theorem justified_b4 : justified τ stake vset parent genesis stFork 4 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) (by decide), sm_L2⟩

theorem finalized_b1 : finalized τ stake vset parent genesis stFork 1 1 :=
  ⟨justified_b1, 2, by decide, sm_L3⟩

theorem finalized_b4 : finalized τ stake vset parent genesis stFork 4 1 :=
  ⟨justified_b4, 5, by decide, sm_L4⟩

theorem the_fork : finalization_fork τ stake vset parent genesis stFork :=
  ⟨1, 1, 4, 1, finalized_b1, finalized_b4,
   not_hash_ancestor_4_1, not_hash_ancestor_1_4⟩

theorem fork_is_slashable : q_intersection_slashed τ stake vset stFork :=
  accountable_safety τ stake vset parent genesis stFork the_fork

theorem fork_witnessB_exists :
    ∃ bL bR : H, ∃ qL' qR' : Finset V,
      qIntersectionWitnessB τ stake vset stFork bL bR qL' qR' = true :=
  accountable_safety_witnessB τ stake vset parent genesis stFork the_fork



theorem mem33_qL : (33 : V) ∈ qL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩
theorem mem33_qR : (33 : V) ∈ qR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩

theorem v33_double_vote : slashed_double_vote stFork 33 :=
  ⟨1, 4, by decide, 0, 0, 0, 0, 1,
   sub_L1 (mem_votes_for_link.mpr ⟨33, mem33_qL, rfl⟩),
   sub_L2 (mem_votes_for_link.mpr ⟨33, mem33_qR, rfl⟩)⟩

theorem v33_slashed : slashed stFork 33 := Or.inl v33_double_vote

end GasperBeaconChain.Executable.UseCases

