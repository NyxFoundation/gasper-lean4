import GasperBeaconChain.Executable.UseCases.ModelN


namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

def stK2 : State (Fin N) H :=
  fUnion (fUnion (fUnion
    (votes_for_link (qTT N) 0 1 0 1)
    (votes_for_link (qTT N) 1 2 1 2))
    (votes_for_link (qTT N) 2 3 2 3))
    (votes_for_link (qTT N) 1 3 1 3)

theorem subK_01 : votes_for_link (qTT N) 0 1 0 1 ⊆ stK2 N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_left hv))
theorem subK_12 : votes_for_link (qTT N) 1 2 1 2 ⊆ stK2 N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_left (mem_fUnion_right hv))
theorem subK_23 : votes_for_link (qTT N) 2 3 2 3 ⊆ stK2 N :=
  fun _ hv => mem_fUnion_left (mem_fUnion_right hv)
theorem subK_13 : votes_for_link (qTT N) 1 3 1 3 ⊆ stK2 N :=
  fun _ hv => mem_fUnion_right hv

theorem smK_01 : supermajority_link τ (stake N) (vset N) (stK2 N) 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 1) (subK_01 N) (wf_vset N _)
theorem smK_12 : supermajority_link τ (stake N) (vset N) (stK2 N) 1 2 1 2 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 2) (subK_12 N) (wf_vset N _)
theorem smK_23 : supermajority_link τ (stake N) (vset N) (stK2 N) 2 3 2 3 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 3) (subK_23 N) (wf_vset N _)
theorem smK_13 : supermajority_link τ (stake N) (vset N) (stK2 N) 1 3 1 3 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 3) (subK_13 N) (wf_vset N _)

theorem jK_1 : justified τ (stake N) (vset N) parent genesis (stK2 N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, smK_01 N⟩
theorem jK_2 : justified τ (stake N) (vset N) parent genesis (stK2 N) 2 2 :=
  justified.justified_link (jK_1 N) ⟨by decide, anc_1_2, smK_12 N⟩
theorem jK_3 : justified τ (stake N) (vset N) parent genesis (stK2 N) 3 3 :=
  justified.justified_link (jK_2 N) ⟨by decide, anc_2_3, smK_23 N⟩

theorem block1_k2_finalized :
    k_finalized τ (stake N) (vset N) parent genesis (stK2 N) 1 1 2 :=
  ⟨by decide,
   [1, 2, 3], rfl, rfl,
   fun n hn => (leq_two_means hn).elim
     (fun h0 => Eq.subst
       (motive := fun m =>
         justified τ (stake N) (vset N) parent genesis (stK2 N) ([1, 2, 3].getD m 1) (1 + m)
         ∧ nth_ancestor parent m 1 ([1, 2, 3].getD m 1))
       h0.symm ⟨jK_1 N, nth_ancestor.nth_ancestor_0 1⟩)
     (fun h => h.elim
       (fun h1 => Eq.subst
         (motive := fun m =>
           justified τ (stake N) (vset N) parent genesis (stK2 N) ([1, 2, 3].getD m 1) (1 + m)
           ∧ nth_ancestor parent m 1 ([1, 2, 3].getD m 1))
         h1.symm ⟨jK_2 N, anc_1_2⟩)
       (fun h2 => Eq.subst
         (motive := fun m =>
           justified τ (stake N) (vset N) parent genesis (stK2 N) ([1, 2, 3].getD m 1) (1 + m)
           ∧ nth_ancestor parent m 1 ([1, 2, 3].getD m 1))
         h2.symm ⟨jK_3 N, anc_1_3⟩)),
   smK_13 N⟩

theorem block1_justified_via_k2 :
    justified τ (stake N) (vset N) parent genesis (stK2 N) 1 1 :=
  k_finalized_means_justified τ (stake N) (vset N) parent genesis (stK2 N) (block1_k2_finalized N)

theorem block1_k2_last :
    ∃ last : H,
      justified τ (stake N) (vset N) parent genesis (stK2 N) last 3
      ∧ nth_ancestor parent 2 1 last
      ∧ supermajority_link τ (stake N) (vset N) (stK2 N) 1 last 1 3 :=
  k_finalized_last_justified τ (stake N) (vset N) parent genesis (stK2 N) (block1_k2_finalized N)

end


#eval justifiedB τ (stake 111) (vset 111) parent genesis (stK2 111) 1 1
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stK2 111) 2 2
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stK2 111) 3 3

end GasperBeaconChain.Executable.UseCases.Parametric
