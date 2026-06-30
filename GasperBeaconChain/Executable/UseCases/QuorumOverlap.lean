import GasperBeaconChain.Executable.UseCases.ModelN
import GasperBeaconChain.Core.Theories.SlashableBound


namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)


def qOff : Finset (Fin N) :=
  upperQuorum N (τ.one_third N) (τ.two_third N)
    (Nat.le_of_eq (threshold_decomposition τ N).symm)

theorem wt_qOff : wt (stake N) (qOff N) = τ.two_third N :=
  wt_upperQuorum N (τ.one_third N) (τ.two_third N)
    (Nat.le_of_eq (threshold_decomposition τ N).symm)

theorem quorum2_qOff (b : H) : quorum_2 τ (stake N) (vset N) (qOff N) b :=
  ⟨Finset.subset_univ _,
   le_of_eq ((congrArg τ.two_third (wt_vset N b)).trans (wt_qOff N).symm)⟩

def overlapWin : Finset (Fin N) :=
  upperQuorum N (τ.one_third N) (τ.two_third N - τ.one_third N)
    (le_of_eq_of_le (Nat.add_sub_cancel' (one_third_le_two_third N)) (τ.leq_two_thirds N))

theorem card_overlapWin : (overlapWin N).card = τ.two_third N - τ.one_third N :=
  card_upperQuorum N (τ.one_third N) (τ.two_third N - τ.one_third N)
    (le_of_eq_of_le (Nat.add_sub_cancel' (one_third_le_two_third N)) (τ.leq_two_thirds N))

theorem inter_eq_overlapWin : qTT N ∩ qOff N = overlapWin N :=
  Finset.ext fun i =>
    ⟨fun hi =>
       mem_upperQuorum.mpr
         ⟨(mem_upperQuorum.mp (Finset.mem_inter.mp hi).2).1,
          Nat.lt_of_lt_of_eq (mem_lowerQuorum.mp (Finset.mem_inter.mp hi).1)
            (Nat.add_sub_cancel' (one_third_le_two_third N)).symm⟩,
     fun hi =>
       have hlt : i.val < τ.two_third N :=
         Nat.lt_of_lt_of_eq (mem_upperQuorum.mp hi).2
           (Nat.add_sub_cancel' (one_third_le_two_third N))
       Finset.mem_inter.mpr
         ⟨mem_lowerQuorum.mpr hlt,
          mem_upperQuorum.mpr
            ⟨(mem_upperQuorum.mp hi).1,
             Nat.lt_of_lt_of_le hlt (Nat.le_add_left (τ.two_third N) (τ.one_third N))⟩⟩⟩



theorem overlap_lower_bound :
    N - τ.one_third N - τ.one_third N ≤ wt (stake N) (qTT N ∩ qOff N) :=
  have key := quorum_intersection_weight_lower τ (stake N)
    (quorum2_qTT N 1).1 (quorum2_qOff N 4).1 (quorum2_qTT N 1).2 (quorum2_qOff N 4).2
  have hinter : wt (stake N) (vset N 1 ∩ vset N 4) = N :=
    (congrArg (wt (stake N)) (Finset.inter_self (Finset.univ : Finset (Fin N)))).trans
      (wt_one_univ N)
  have heq :
      wt (stake N) (vset N 1 ∩ vset N 4)
        - τ.one_third (wt (stake N) (vset N 1))
        - τ.one_third (wt (stake N) (vset N 4))
        = N - τ.one_third N - τ.one_third N :=
    congrArg₂ (· - ·)
      (congrArg₂ (· - ·) hinter (congrArg τ.one_third (wt_vset N 1)))
      (congrArg τ.one_third (wt_vset N 4))
  le_of_eq_of_le heq.symm key

theorem overlap_weight_exact :
    wt (stake N) (qTT N ∩ qOff N) = N - τ.one_third N - τ.one_third N :=
  (congrArg (wt (stake N)) (inter_eq_overlapWin N)).trans
    ((wt_one_eq_card (overlapWin N)).trans
      ((card_overlapWin N).trans (overlap_card_eq_bound N)))

theorem overlap_weight_pos (hN : 3 ≤ N) : 0 < wt (stake N) (qTT N ∩ qOff N) :=
  Nat.lt_of_lt_of_eq (overlap_pos hN) (overlap_weight_exact N).symm



def stOverlap : State (Fin N) H :=
  fUnion (votes_for_link (qTT N) 0 1 0 1) (votes_for_link (qOff N) 0 4 0 1)

theorem subO_01 : votes_for_link (qTT N) 0 1 0 1 ⊆ stOverlap N :=
  fun _ hv => mem_fUnion_left hv
theorem subO_04 : votes_for_link (qOff N) 0 4 0 1 ⊆ stOverlap N :=
  fun _ hv => mem_fUnion_right hv

theorem smO_01 : supermajority_link τ (stake N) (vset N) (stOverlap N) 0 1 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 1) (subO_01 N) (wf_vset N _)
theorem smO_04 : supermajority_link τ (stake N) (vset N) (stOverlap N) 0 4 0 1 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qOff N 4) (subO_04 N) (wf_vset N _)

theorem justO_1 : justified τ (stake N) (vset N) parent genesis (stOverlap N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, smO_01 N⟩
theorem justO_4 : justified τ (stake N) (vset N) parent genesis (stOverlap N) 4 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_4, smO_04 N⟩

theorem overlap_same_height_slashable :
    q_intersection_slashed τ (stake N) (vset N) (stOverlap N) :=
  two_justified_same_height_slashed τ (stake N) (vset N) parent genesis (stOverlap N)
    (justO_1 N) (justO_4 N) (by decide)

theorem overlap_double {v : Fin N} (hv : v ∈ qTT N ∩ qOff N) :
    slashed_double_vote (stOverlap N) v :=
  ⟨1, 4, by decide, 0, 0, 0, 0, 1,
   subO_01 N (mem_votes_for_link.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩),
   subO_04 N (mem_votes_for_link.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩)⟩

theorem overlap_slashed {v : Fin N} (hv : v ∈ qTT N ∩ qOff N) : slashed (stOverlap N) v :=
  Or.inl (overlap_double N hv)

end


#eval ((List.finRange 120).filter (fun v => slashedB (stOverlap 120) v)).length
#eval (τ.two_third 120 - τ.one_third 120 : Nat)
#eval justifiedB τ (stake 120) (vset 120) parent genesis (stOverlap 120) 1 1
#eval justifiedB τ (stake 120) (vset 120) parent genesis (stOverlap 120) 4 1

end GasperBeaconChain.Executable.UseCases.Parametric
