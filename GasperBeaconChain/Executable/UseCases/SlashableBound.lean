import GasperBeaconChain.Executable.UseCases.AccountableSafety
import GasperBeaconChain.Core.Theories.SlashableBound

/-!
# Use case — the dynamic-validator-set slashable bound (Gasper §8.6, Thm 8.3)

The accountable-safety use case shows the **static** Casper FFG guarantee: a fork
forces a slashable quorum intersection of weight `≥ N/3`. Gasper's distinctive
refinement (§8.6) asks what survives when the validator set **changes** between
the reference point and the conflicting branches — validators may *activate*
(enter) or *exit* (leave), and an exited Byzantine validator can no longer be
slashed. The bound degrades accordingly:

$$
w(Q_L \cap Q_R)\;\ge\;
\max\bigl(w(V_L)-a_L-e_R,\; w(V_R)-a_R-e_L\bigr)
-\tfrac13 w(V_L)-\tfrac13 w(V_R),
$$

where `aL = w(A(V0,VL))` (activated), `eL = w(E(V0,VL))` (exited), etc. With no
churn (`aL=aR=eL=eR=0`, `VL=VR=V0`) this recovers the static `N/3`.

This file instantiates the **Core arithmetic that proves §8.6** — the Venn-diagram
lower bound `validator_intersection_lower_bound` (paper Fig. 9–10) and the quorum
bound `quorum_intersection_weight_lower` — on a concrete 99-validator committee
undergoing churn, and reads off the degradation by `#eval`. We also apply the full
`slashable_bound` theorem to the (static) accountable-safety fork to certify that
the static bound is exactly `N/3 = 33`, **tight** for that configuration.

## The churn

* Reference set `V0 = VL = ` all `99` validators (the left branch is stable).
* Right branch set `VR = {9..98}` (`90` validators): validators `{0..8}` **exited**
  before block `4`. So `extwt(V0,VR) = 9`, `actwt(V0,VR) = 0`.

The N/3 bound `33` degrades to `27` — the `9` exits cost `33 - 27 = 6` of slashable
weight (`9` lost, partially offset because `one_third` shrinks with `VR`).
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

/-- Reference validator set at genesis (all `99`). -/
def V0 : Finset V := Finset.univ
/-- Left-branch validator set: stable, no churn. -/
def VL : Finset V := Finset.univ
/-- Right-branch validator set: validators `{0..8}` have exited (`{9..98}`, `90`). -/
def VR : Finset V := Finset.univ.filter (fun v => 9 ≤ v.val)

/-- A right-branch 2/3 quorum: `{9..68}` (`60 = two_third 90`), inside `VR`. -/
def qR_d : Finset V := Finset.univ.filter (fun v => 9 ≤ v.val ∧ v.val < 69)


/-! ### 1. The §8.6 quantities, computed at committee scale (`#eval`) -/

#eval wt stake VL              -- 99
#eval wt stake VR              -- 90
#eval actwt stake V0 VR        -- 0    (no activations)
#eval extwt stake V0 VR        -- 9    (validators {0..8} exited)

-- The **dynamic accountable-safety bound** (Gasper Thm 8.3) for this churn:
#eval max (wt stake VL - actwt stake V0 VL - extwt stake V0 VR)
          (wt stake VR - actwt stake V0 VR - extwt stake V0 VL)
        - τ.one_third (wt stake VL) - τ.one_third (wt stake VR)     -- 27

-- The **static** bound (no churn): `N - 2·(N/3) = 33 = N/3`:
#eval (99 : Nat) - τ.one_third 99 - τ.one_third 99                  -- 33

-- The validator-set intersection and the actual slashed quorum intersection:
#eval wt stake (VL ∩ VR)       -- 90   (= |{9..98}|, the bound's `w(C)+w(F)`)
#eval wt stake (qL ∩ qR_d)     -- 57   (= |{9..65}|, the realised double voters)


/-! ### 2. The §8.6 arithmetic, instantiated as theorems (constructive)

`validator_intersection_lower_bound` is the Venn-diagram core of Thm 8.3: the
overlap of the two validator sets is at least the churn-adjusted maximum. We
instantiate it on `(V0, VL, VR)` — committee scale, with real exits. -/

/-- Gasper §8.6 Venn bound on the validator-set overlap. Here both sides equal
`90`, so the bound is **tight**. -/
theorem dyn_validator_bound :
    max (wt stake VL - actwt stake V0 VL - extwt stake V0 VR)
        (wt stake VR - actwt stake V0 VR - extwt stake V0 VL)
      ≤ wt stake (VL ∩ VR) :=
  validator_intersection_lower_bound stake V0 VL VR

/-- The right-branch quorum sits inside the (shrunk) right validator set. -/
theorem qR_d_subset_VR : qR_d ⊆ VR :=
  fun _ hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.1⟩

/-- `quorum_intersection_weight_lower` (Thm 8.3, quorum step): the slashable
quorum intersection is at least the validator overlap minus the two one-thirds.
With the `9` exits this yields `90 - 33 - 30 = 27 ≤ 57 = w(qL ∩ qR_d)`. -/
theorem dyn_quorum_bound :
    wt stake (VL ∩ VR) - τ.one_third (wt stake VL) - τ.one_third (wt stake VR)
      ≤ wt stake (qL ∩ qR_d) :=
  quorum_intersection_weight_lower τ stake
    (Finset.subset_univ qL)   -- qL ⊆ VL (= univ)
    qR_d_subset_VR            -- qR_d ⊆ VR
    (by decide)              -- two_third (wt VL) = 66 ≤ wt qL = 66
    (by decide)              -- two_third (wt VR) = 60 ≤ wt qR_d = 60


/-! ### 3. The full theorem on the (static) fork: the bound is exactly N/3

Reusing the committee-scale fork from `AccountableSafety` (blocks `1`, `4`
finalized, conflicting), `slashable_bound` certifies a slashable intersection.
Since that model has static `vset = univ`, all activations/exits vanish and the
bound is `max(99,99) - 33 - 33 = 33 = N/3` — and our config realises exactly `33`
(`#eval` above), so the static accountable-safety bound is **tight**. -/

/-- Block `1` is `1`-finalized (the `k`-finalization view of `finalized`). -/
theorem k_fin_b1 : k_finalized τ stake vset parent genesis stFork 1 1 1 :=
  (finalized_means_one_finalized τ stake vset parent genesis stFork 1 1).mp finalized_b1

/-- Block `4` is `1`-finalized. -/
theorem k_fin_b4 : k_finalized τ stake vset parent genesis stFork 4 1 1 :=
  (finalized_means_one_finalized τ stake vset parent genesis stFork 4 1).mp finalized_b4

/-- **Slashable bound** on the concrete fork (reference block = genesis). The
returned quorums have intersection weight at least the churn-adjusted bound,
which is `N/3 = 33` here. -/
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
