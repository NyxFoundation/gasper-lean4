import GasperBeaconChain.Executable.UseCases.AccountableSafety
import GasperBeaconChain.Core.Theories.SlashableBound


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

def V0 : Finset V := Finset.univ
def VL : Finset V := Finset.univ
def VR : Finset V := Finset.univ.filter (fun v => 9 ≤ v.val)

def qR_d : Finset V := Finset.univ.filter (fun v => 9 ≤ v.val ∧ v.val < 69)



#eval wt stake VL
#eval wt stake VR
#eval actwt stake V0 VR
#eval extwt stake V0 VR

#eval max (wt stake VL - actwt stake V0 VL - extwt stake V0 VR)
          (wt stake VR - actwt stake V0 VR - extwt stake V0 VL)
        - τ.one_third (wt stake VL) - τ.one_third (wt stake VR)

#eval (99 : Nat) - τ.one_third 99 - τ.one_third 99

#eval wt stake (VL ∩ VR)
#eval wt stake (qL ∩ qR_d)



theorem dyn_validator_bound :
    max (wt stake VL - actwt stake V0 VL - extwt stake V0 VR)
        (wt stake VR - actwt stake V0 VR - extwt stake V0 VL)
      ≤ wt stake (VL ∩ VR) :=
  validator_intersection_lower_bound stake V0 VL VR

theorem qR_d_subset_VR : qR_d ⊆ VR :=
  fun _ hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.1⟩

theorem dyn_quorum_bound :
    wt stake (VL ∩ VR) - τ.one_third (wt stake VL) - τ.one_third (wt stake VR)
      ≤ wt stake (qL ∩ qR_d) :=
  quorum_intersection_weight_lower τ stake
    (Finset.subset_univ qL)
    qR_d_subset_VR
    (by decide)
    (by decide)



theorem k_fin_b1 : k_finalized τ stake vset parent genesis stFork 1 1 1 :=
  (finalized_means_one_finalized τ stake vset parent genesis stFork 1 1).mp finalized_b1

theorem k_fin_b4 : k_finalized τ stake vset parent genesis stFork 4 1 1 :=
  (finalized_means_one_finalized τ stake vset parent genesis stFork 4 1).mp finalized_b4

theorem static_slashable_bound :
    ∃ bL bR : H, ∃ qL' qR' : Finset V,
      qL' ⊆ vset bL ∧ qR' ⊆ vset bR ∧
      max
        (wt stake (vset bL) - actwt stake (vset genesis) (vset bL) - extwt stake (vset genesis) (vset bR))
        (wt stake (vset bR) - actwt stake (vset genesis) (vset bR) - extwt stake (vset genesis) (vset bL))
        - τ.one_third (wt stake (vset bL)) - τ.one_third (wt stake (vset bR))
        ≤ wt stake (qL' ∩ qR') :=
  slashable_bound τ stake vset parent genesis stFork genesis 1 4 1 1 1 1
    k_fin_b1 k_fin_b4 not_hash_ancestor_1_4 not_hash_ancestor_4_1

end GasperBeaconChain.Executable.UseCases
