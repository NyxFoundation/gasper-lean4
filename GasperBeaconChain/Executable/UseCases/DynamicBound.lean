import GasperBeaconChain.Executable.UseCases.ModelN
import GasperBeaconChain.Core.Theories.SlashableBound


namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases



def V0d (N : Nat) : Finset (Fin N) := Finset.univ

theorem wt_V0d (N : Nat) : wt (stake N) (V0d N) = N := wt_one_univ N

def VRd (N e : Nat) (he : e ≤ N) : Finset (Fin N) :=
  upperQuorum N e (N - e) (Nat.le_of_eq (Nat.add_sub_cancel' he))

theorem wt_VRd (N e : Nat) (he : e ≤ N) : wt (stake N) (VRd N e he) = N - e :=
  wt_upperQuorum N e (N - e) (Nat.le_of_eq (Nat.add_sub_cancel' he))

def qRd (N e : Nat) (he : e ≤ N) : Finset (Fin N) :=
  upperQuorum N e (τ.two_third (N - e))
    (Nat.le_trans (Nat.add_le_add_left (τ.leq_two_thirds (N - e)) e)
      (Nat.le_of_eq (Nat.add_sub_cancel' he)))

theorem wt_qRd (N e : Nat) (he : e ≤ N) :
    wt (stake N) (qRd N e he) = τ.two_third (N - e) :=
  wt_upperQuorum N e (τ.two_third (N - e))
    (Nat.le_trans (Nat.add_le_add_left (τ.leq_two_thirds (N - e)) e)
      (Nat.le_of_eq (Nat.add_sub_cancel' he)))

theorem qRd_subset_VRd (N e : Nat) (he : e ≤ N) : qRd N e he ⊆ VRd N e he :=
  fun i hi =>
    mem_upperQuorum.mpr
      ⟨(mem_upperQuorum.mp hi).1,
       Nat.lt_of_lt_of_le (mem_upperQuorum.mp hi).2
         (Nat.add_le_add_left (τ.leq_two_thirds (N - e)) e)⟩



theorem dyn_validator_bound (N e : Nat) (he : e ≤ N) :
    max (wt (stake N) (V0d N)
          - actwt (stake N) (V0d N) (V0d N) - extwt (stake N) (V0d N) (VRd N e he))
        (wt (stake N) (VRd N e he)
          - actwt (stake N) (V0d N) (VRd N e he) - extwt (stake N) (V0d N) (V0d N))
      ≤ wt (stake N) (V0d N ∩ VRd N e he) :=
  validator_intersection_lower_bound (stake N) (V0d N) (V0d N) (VRd N e he)

theorem dyn_quorum_bound (N e : Nat) (he : e ≤ N) :
    wt (stake N) (V0d N ∩ VRd N e he)
        - τ.one_third (wt (stake N) (V0d N))
        - τ.one_third (wt (stake N) (VRd N e he))
      ≤ wt (stake N) (qTT N ∩ qRd N e he) :=
  quorum_intersection_weight_lower τ (stake N)
    (Finset.subset_univ (qTT N))
    (qRd_subset_VRd N e he)
    (le_of_eq ((congrArg τ.two_third (wt_V0d N)).trans (wt_qTT N).symm))
    (le_of_eq ((congrArg τ.two_third (wt_VRd N e he)).trans (wt_qRd N e he).symm))



#eval wt (stake 120) (V0d 120)
#eval wt (stake 120) (VRd 120 12 (by decide))
#eval extwt (stake 120) (V0d 120) (VRd 120 12 (by decide))
#eval actwt (stake 120) (V0d 120) (VRd 120 12 (by decide))

#eval max (wt (stake 120) (V0d 120)
            - actwt (stake 120) (V0d 120) (V0d 120)
            - extwt (stake 120) (V0d 120) (VRd 120 12 (by decide)))
          (wt (stake 120) (VRd 120 12 (by decide))
            - actwt (stake 120) (V0d 120) (VRd 120 12 (by decide))
            - extwt (stake 120) (V0d 120) (V0d 120))
        - τ.one_third (wt (stake 120) (V0d 120))
        - τ.one_third (wt (stake 120) (VRd 120 12 (by decide)))
#eval (120 : Nat) - τ.one_third 120 - τ.one_third 120
#eval wt (stake 120) (qTT 120 ∩ qRd 120 12 (by decide))

end GasperBeaconChain.Executable.UseCases.Parametric
