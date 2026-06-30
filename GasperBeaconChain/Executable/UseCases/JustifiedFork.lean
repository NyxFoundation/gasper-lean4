import GasperBeaconChain.Executable.UseCases.ModelN


namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

def stJust : State (Fin N) H :=
  fUnion (votes_for_link (qTT N) 0 1 0 1) (votes_for_link (qTT N) 0 4 0 1)

theorem subJ_01 : votes_for_link (qTT N) 0 1 0 1 ⊆ stJust N :=
  fun _ hv => mem_fUnion_left hv
theorem subJ_04 : votes_for_link (qTT N) 0 4 0 1 ⊆ stJust N :=
  fun _ hv => mem_fUnion_right hv

theorem smJ_01 : supermajority_link τ (stake N) (vset N) (stJust N) 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 1) (subJ_01 N) (wf_vset N _)
theorem smJ_04 : supermajority_link τ (stake N) (vset N) (stJust N) 0 4 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 4) (subJ_04 N) (wf_vset N _)

theorem justJ_1 : justified τ (stake N) (vset N) parent genesis (stJust N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, smJ_01 N⟩
theorem justJ_4 : justified τ (stake N) (vset N) parent genesis (stJust N) 4 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_4, smJ_04 N⟩

theorem same_height_slashable : q_intersection_slashed τ (stake N) (vset N) (stJust N) :=
  two_justified_same_height_slashed τ (stake N) (vset N) parent genesis (stJust N)
    (justJ_1 N) (justJ_4 N) (by decide)

theorem qTT_double {v : Fin N} (hv : v ∈ qTT N) :
    slashed_double_vote (stJust N) v :=
  ⟨1, 4, by decide, 0, 0, 0, 0, 1,
   subJ_01 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩),
   subJ_04 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩)⟩

theorem qTT_slashed_S1 {v : Fin N} (hv : v ∈ qTT N) : slashed (stJust N) v :=
  Or.inl (qTT_double N hv)

end


#eval slashedB (stJust 111) ⟨0, by decide⟩
#eval ((List.finRange 111).filter (fun v => slashedB (stJust 111) v)).length
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stJust 111) 1 1
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stJust 111) 4 1

end GasperBeaconChain.Executable.UseCases.Parametric
