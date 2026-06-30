import GasperBeaconChain.Executable.UseCases.ModelN


namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

def stFork : State (Fin N) H :=
  fUnion (fUnion (fUnion
    (votes_for_link (qTT N) 0 1 0 1)
    (votes_for_link (qTT N) 1 2 1 2))
    (votes_for_link (qTT N) 0 6 0 3))
    (votes_for_link (qTT N) 6 7 3 4)


theorem sub_01 : votes_for_link (qTT N) 0 1 0 1 ⊆ stFork N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_left hv))
theorem sub_12 : votes_for_link (qTT N) 1 2 1 2 ⊆ stFork N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_right hv))
theorem sub_06 : votes_for_link (qTT N) 0 6 0 3 ⊆ stFork N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem sub_67 : votes_for_link (qTT N) 6 7 3 4 ⊆ stFork N :=
  fun _ hv => mem_fUnion_right hv


theorem sm_01 : supermajority_link τ (stake N) (vset N) (stFork N) 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 1) (sub_01 N) (wf_vset N _)
theorem sm_12 : supermajority_link τ (stake N) (vset N) (stFork N) 1 2 1 2 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 2) (sub_12 N) (wf_vset N _)
theorem sm_06 : supermajority_link τ (stake N) (vset N) (stFork N) 0 6 0 3 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 6) (sub_06 N) (wf_vset N _)
theorem sm_67 : supermajority_link τ (stake N) (vset N) (stFork N) 6 7 3 4 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 7) (sub_67 N) (wf_vset N _)


theorem just_1 : justified τ (stake N) (vset N) parent genesis (stFork N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, sm_01 N⟩

theorem fin_1 : finalized τ (stake N) (vset N) parent genesis (stFork N) 1 1 :=
  ⟨just_1 N, 2, pe_12, sm_12 N⟩

theorem just_6 : justified τ (stake N) (vset N) parent genesis (stFork N) 6 3 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_6, sm_06 N⟩

theorem fin_6 : finalized τ (stake N) (vset N) parent genesis (stFork N) 6 3 :=
  ⟨just_6 N, 7, pe_67, sm_67 N⟩


theorem the_fork : finalization_fork τ (stake N) (vset N) parent genesis (stFork N) :=
  ⟨1, 1, 6, 3, fin_1 N, fin_6 N, not_anc_6_1, not_anc_1_6⟩

theorem fork_slashable : q_intersection_slashed τ (stake N) (vset N) (stFork N) :=
  accountable_safety τ (stake N) (vset N) parent genesis (stFork N) (the_fork N)


theorem qTT_surround {v : Fin N} (hv : v ∈ qTT N) :
    slashed_surround_vote (stFork N) v :=
  ⟨0, 6, 0, 3, 1, 2, 1, 2,
   sub_06 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩),
   sub_12 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩),
   by decide, by decide⟩

theorem qTT_slashed {v : Fin N} (hv : v ∈ qTT N) : slashed (stFork N) v :=
  Or.inr (qTT_surround N hv)

end


#eval slashedB (stFork 111) ⟨0, by decide⟩
#eval (slashedB (stFork 111) ⟨0, by decide⟩
       && slashedB (stFork 111) ⟨65, by decide⟩)
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stFork 111) 1 1
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stFork 111) 6 3
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stFork 111) 3 3

end GasperBeaconChain.Executable.UseCases.Parametric
