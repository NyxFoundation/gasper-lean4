import GasperBeaconChain.Executable.UseCases.ModelN
import GasperBeaconChain.Core.Theories.SlashableBound

/-!
# Use case — the dynamic-validator-set slashable bound, **size-parametric** (Gasper §8.6, Thm 8.3)

Casper FFG keeps a *static* validator set; Gasper's distinctive refinement (§8.6) asks what
accountable safety survives when the validator set **changes** between the reference point and
the two conflicting branches.  Validators may *activate* (enter) or *exit* (leave), and an
exited Byzantine validator can no longer be slashed, so the slashable bound **degrades**:

$$
w(q_L \cap q_R)\;\ge\;
\max\bigl(w(V_L)-a_L-e_R,\; w(V_R)-a_R-e_L\bigr)\;-\;\tfrac13 w(V_L)\;-\;\tfrac13 w(V_R),
$$

with `aX = actwt(V0,VX)` (activated), `eX = extwt(V0,VX)` (exited).

The legacy `SlashableBound` use case pinned this to a **single** committee (`Fin 99`, exactly
`9` exits).  Here it is proved for **every** committee size `N` and **every** number of exits
`e ≤ N`, on the choice-free `Fin N`:

```text
  V0 = VL = univ            (all N; the left branch is stable, no churn)
  VR = upperQuorum [e, N)   (the last N − e validators: indices {0,…,e−1} EXITED)
        ⇒  wt VR = N − e,   actwt(V0,VR) = 0,   extwt(V0,VR) = e,   extwt(V0,VL) = 0
  qL = qTT  = [0, 2N/3),    qR = upperQuorum [e, e + ⌈2(N−e)/3⌉)   (2/3 of the shrunk VR)
```

* `dyn_validator_bound` — the Venn-diagram core (paper Fig. 9–10),
  `validator_intersection_lower_bound`, holds for all `(N,e)`;
* `dyn_quorum_bound` — `quorum_intersection_weight_lower` on the *shrunk* right set, so the
  guarantee is `wt(VL∩VR) − ⌊N/3⌋ − ⌊(N−e)/3⌋ ≤ wt(qL∩qR)` — visibly degrading in `e`.

With `e = 0` (`VR = V0`) every churn term vanishes and we recover the static `N/3`.
`Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases


/-! ## 1. The dynamic validator sets (`e` exits) and the shrunk right quorum -/

/-- Stable reference / left-branch validator set: all `N`. -/
def V0d (N : Nat) : Finset (Fin N) := Finset.univ

theorem wt_V0d (N : Nat) : wt (stake N) (V0d N) = N := wt_one_univ N

/-- Right-branch validator set after `e` exits: the last `N − e` validators `{e,…,N-1}`
(validators `{0,…,e-1}` have left). -/
def VRd (N e : Nat) (he : e ≤ N) : Finset (Fin N) :=
  upperQuorum N e (N - e) (Nat.le_of_eq (Nat.add_sub_cancel' he))

theorem wt_VRd (N e : Nat) (he : e ≤ N) : wt (stake N) (VRd N e he) = N - e :=
  wt_upperQuorum N e (N - e) (Nat.le_of_eq (Nat.add_sub_cancel' he))

/-- A right-branch 2/3 quorum *inside the shrunk set* `VRd`: `{e,…,e + two_third(N-e) − 1}`,
weight exactly `two_third (N − e)`. -/
def qRd (N e : Nat) (he : e ≤ N) : Finset (Fin N) :=
  upperQuorum N e (τ.two_third (N - e))
    (Nat.le_trans (Nat.add_le_add_left (τ.leq_two_thirds (N - e)) e)
      (Nat.le_of_eq (Nat.add_sub_cancel' he)))

theorem wt_qRd (N e : Nat) (he : e ≤ N) :
    wt (stake N) (qRd N e he) = τ.two_third (N - e) :=
  wt_upperQuorum N e (τ.two_third (N - e))
    (Nat.le_trans (Nat.add_le_add_left (τ.leq_two_thirds (N - e)) e)
      (Nat.le_of_eq (Nat.add_sub_cancel' he)))

/-- The shrunk right quorum lies inside the shrunk right validator set
(`two_third (N−e) ≤ N−e`). -/
theorem qRd_subset_VRd (N e : Nat) (he : e ≤ N) : qRd N e he ⊆ VRd N e he :=
  fun i hi =>
    mem_upperQuorum.mpr
      ⟨(mem_upperQuorum.mp hi).1,
       Nat.lt_of_lt_of_le (mem_upperQuorum.mp hi).2
         (Nat.add_le_add_left (τ.leq_two_thirds (N - e)) e)⟩


/-! ## 2. The two halves of Gasper Thm 8.3, parametric in `(N, e)` -/

/-- **§8.6 Venn bound** (Thm 8.3, set step): the validator-set overlap dominates the
churn-adjusted maximum.  Immediate from the Core `validator_intersection_lower_bound`
(reference `V0`, left `V0`, right `VRd`). -/
theorem dyn_validator_bound (N e : Nat) (he : e ≤ N) :
    max (wt (stake N) (V0d N)
          - actwt (stake N) (V0d N) (V0d N) - extwt (stake N) (V0d N) (VRd N e he))
        (wt (stake N) (VRd N e he)
          - actwt (stake N) (V0d N) (VRd N e he) - extwt (stake N) (V0d N) (V0d N))
      ≤ wt (stake N) (V0d N ∩ VRd N e he) :=
  validator_intersection_lower_bound (stake N) (V0d N) (V0d N) (VRd N e he)

/-- **§8.6 quorum bound** (Thm 8.3, quorum step): the slashable quorum intersection is at
least the validator overlap minus the two one-thirds.  Because the right set is the shrunk
`VRd`, the second one-third is `⌊(N−e)/3⌋` — the bound degrades as `e` grows. -/
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


/-! ## 3. Executable read-out of the graceful degradation (`N = 120`)

`two_third 120 = 80`, `one_third 120 = 40`; static bound `= 40 = N/3`.
With `e = 12` exits: `wt VR = 108`, `extwt = 12`, the Venn max stays `108`, and the bound
degrades to `108 − 40 − ⌊108/3⌋ = 108 − 40 − 36 = 32` — the `12` exits cost `8` of slashable
weight.  The realised double-vote overlap is `wt(qTT ∩ qRd) = |[12,80)| = 68 ≥ 32`. -/

#eval wt (stake 120) (V0d 120)                                       -- 99→ here 120
#eval wt (stake 120) (VRd 120 12 (by decide))                       -- 108 (= 120 − 12)
#eval extwt (stake 120) (V0d 120) (VRd 120 12 (by decide))          -- 12  (exited {0..11})
#eval actwt (stake 120) (V0d 120) (VRd 120 12 (by decide))          -- 0   (no activations)

-- dynamic (Thm 8.3) bound with 12 exits  vs  static (e = 0) bound:
#eval max (wt (stake 120) (V0d 120)
            - actwt (stake 120) (V0d 120) (V0d 120)
            - extwt (stake 120) (V0d 120) (VRd 120 12 (by decide)))
          (wt (stake 120) (VRd 120 12 (by decide))
            - actwt (stake 120) (V0d 120) (VRd 120 12 (by decide))
            - extwt (stake 120) (V0d 120) (V0d 120))
        - τ.one_third (wt (stake 120) (V0d 120))
        - τ.one_third (wt (stake 120) (VRd 120 12 (by decide)))     -- 32 (degraded)
#eval (120 : Nat) - τ.one_third 120 - τ.one_third 120               -- 40 (static N/3)
#eval wt (stake 120) (qTT 120 ∩ qRd 120 12 (by decide))             -- 68 (realised overlap)

end GasperBeaconChain.Executable.UseCases.Parametric
