import GasperBeaconChain.Executable.UseCases.Model
import GasperBeaconChain.Core.Lemmas.PlausibleLiveness


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

def qF : Finset V := Finset.univ.filter (fun v => v.val < 66)

def stFinality : State V H :=
  fUnion (fUnion
    (votes_for_link qF 0 1 0 1)
    (votes_for_link qF 1 2 1 2))
    (votes_for_link qF 2 3 2 3)

abbrev J : H → Nat → Bool :=
  justifiedB τ stake vset parent genesis stFinality



#eval J 0 0
#eval J 1 1
#eval J 2 2
#eval J 3 3
#eval J 4 1
#eval J 1 5



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

theorem block1_justified : justified τ stake vset parent genesis stFinality 1 1 :=
  justified.justified_link justified.justified_genesis
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 0) (by decide), sm_01⟩

theorem block2_justified : justified τ stake vset parent genesis stFinality 2 2 :=
  justified.justified_link block1_justified
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 1) (by decide), sm_12⟩

theorem block3_justified : justified τ stake vset parent genesis stFinality 3 3 :=
  justified.justified_link block2_justified
    ⟨by decide, nth_ancestor.nth_ancestor_nth (nth_ancestor.nth_ancestor_0 2) (by decide), sm_23⟩

theorem block4_not_justified : ¬ justified τ stake vset parent genesis stFinality 4 1 :=
  fun h => absurd ((justifiedB_iff τ stake vset parent genesis stFinality 4 1).mpr h) (by decide)



theorem block1_finalized : finalized τ stake vset parent genesis stFinality 1 1 :=
  ⟨block1_justified, 2, by decide, sm_12⟩

theorem block1_k_finalized :
    k_finalized τ stake vset parent genesis stFinality 1 1 1 :=
  (finalized_means_one_finalized τ stake vset parent genesis stFinality 1 1).mp block1_finalized

end GasperBeaconChain.Executable.UseCases
