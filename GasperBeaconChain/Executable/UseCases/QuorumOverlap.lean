import GasperBeaconChain.Executable.UseCases.ModelN
import GasperBeaconChain.Core.Theories.SlashableBound

/-!
# Use case — Lemma 5.1: two *distinct* 2/3 quorums overlap in weight `≥ N/3`, and this
bound is **sharp** (Casper FFG, the pigeonhole engine of accountable safety)

Every earlier fork (`SurroundFork`, `JustifiedFork`) used the *same* quorum `qTT` on both
sides, so the overlap was the whole of `qTT`.  The mathematically essential content of
Casper's accountable-safety argument is, however, about **two genuinely different** 2/3
quorums `q_L ≠ q_R`: the theorem `quorum_intersection_weight_lower` guarantees

$$ w(q_L \cap q_R)\ \ge\ w(V) - \tfrac13 w(V) - \tfrac13 w(V)\ =\ N - \tfrac{N}{3} - \tfrac{N}{3}. $$

We realise this with the two *most spread-apart* 2/3 quorums of the `N`-committee:

```text
  q_L = lowerQuorum = [0 , 2N/3)         (the first  two_third N validators)
  q_R = upperQuorum = [N/3 , N)          (the last   two_third N validators, offset by N/3)
  q_L ∩ q_R          = [N/3 , 2N/3)      (exactly two_third N − one_third N validators)
```

and prove **two** facts about their overlap weight `w(q_L ∩ q_R)`:

* `overlap_lower_bound` — the *real Core theorem* yields `N − N/3 − N/3 ≤ w(q_L ∩ q_R)`;
* `overlap_weight_exact` — for *these* quorums the overlap is **exactly** the window,
  so `w(q_L ∩ q_R) = N − N/3 − N/3`.

Together: the Casper `1/3` lower bound is **attained with equality** — it cannot be
improved.  (`upperQuorum`, built in `Committee` but never yet used, is exactly the tool that
makes the two quorums distinct.)  We then light it up: the overlap validators are precisely
the ones forced to double-vote in a same-height fork, hence slashed.  `Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

/-! ## 1. The two distinct 2/3 quorums and the overlap window -/

/-- The *offset* 2/3 quorum `[N/3, N)`: the last `two_third N` validators (`base = one_third N`,
`one_third N + two_third N = N`).  Distinct from `qTT = [0, two_third N)`. -/
def qOff : Finset (Fin N) :=
  upperQuorum N (τ.one_third N) (τ.two_third N)
    (Nat.le_of_eq (threshold_decomposition τ N).symm)

theorem wt_qOff : wt (stake N) (qOff N) = τ.two_third N :=
  wt_upperQuorum N (τ.one_third N) (τ.two_third N)
    (Nat.le_of_eq (threshold_decomposition τ N).symm)

/-- `qOff` is a genuine 2/3 quorum at every block. -/
theorem quorum2_qOff (b : H) : quorum_2 τ (stake N) (vset N) (qOff N) b :=
  ⟨Finset.subset_univ _,
   le_of_eq ((congrArg τ.two_third (wt_vset N b)).trans (wt_qOff N).symm)⟩

/-- The overlap window `[N/3, 2N/3)`, realised as a quorum of `two_third N − one_third N`
validators (`base = one_third N`, `k = two_third N − one_third N`,
`one_third N + (two_third N − one_third N) = two_third N ≤ N`). -/
def overlapWin : Finset (Fin N) :=
  upperQuorum N (τ.one_third N) (τ.two_third N - τ.one_third N)
    (le_of_eq_of_le (Nat.add_sub_cancel' (one_third_le_two_third N)) (τ.leq_two_thirds N))

theorem card_overlapWin : (overlapWin N).card = τ.two_third N - τ.one_third N :=
  card_upperQuorum N (τ.one_third N) (τ.two_third N - τ.one_third N)
    (le_of_eq_of_le (Nat.add_sub_cancel' (one_third_le_two_third N)) (τ.leq_two_thirds N))

/-- **The intersection of the two distinct 2/3 quorums is exactly the window**:
`qTT ∩ qOff = [N/3, 2N/3)`, by extensionality on the index conditions
`(i < 2N/3) ∧ (N/3 ≤ i < N)  ↔  N/3 ≤ i < 2N/3`. -/
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


/-! ## 2. The Core lower bound, and its sharpness -/

/-- **The real Core theorem** `quorum_intersection_weight_lower`, instantiated at the two
distinct 2/3 quorums `qTT`, `qOff` (with `vL = vR = univ`): the overlap weighs at least
`N − N/3 − N/3`. -/
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

/-- **Sharpness of the Casper 1/3 bound.** For *these* two quorums the overlap is exactly
the window, so the Core lower bound is met with **equality**:
`w(qTT ∩ qOff) = N − N/3 − N/3`. -/
theorem overlap_weight_exact :
    wt (stake N) (qTT N ∩ qOff N) = N - τ.one_third N - τ.one_third N :=
  (congrArg (wt (stake N)) (inter_eq_overlapWin N)).trans
    ((wt_one_eq_card (overlapWin N)).trans
      ((card_overlapWin N).trans (overlap_card_eq_bound N)))

/-- Hence the overlap is strictly positive (`N ≥ 3`): the two distinct quorums must share
at least `N/3` validators — they cannot be disjoint. -/
theorem overlap_weight_pos (hN : 3 ≤ N) : 0 < wt (stake N) (qTT N ∩ qOff N) :=
  Nat.lt_of_lt_of_eq (overlap_pos hN) (overlap_weight_exact N).symm


/-! ## 3. Lighting it up: the overlap validators are the slashed ones -/

/-- A same-height fork in which `qTT` justifies `1` (link `0⇒1`) and `qOff` justifies `4`
(link `0⇒4`), both at height `1`.  Only the *overlap* `qTT ∩ qOff` double-votes. -/
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

/-- The two same-height justifications force a slashable quorum intersection (the real Core
engine `two_justified_same_height_slashed`). -/
theorem overlap_same_height_slashable :
    q_intersection_slashed τ (stake N) (vset N) (stOverlap N) :=
  two_justified_same_height_slashed τ (stake N) (vset N) parent genesis (stOverlap N)
    (justO_1 N) (justO_4 N) (by decide)

/-- The explicit S1 evidence for an overlap validator: `v ∈ qTT ∩ qOff` voted both `0⇒1`
(via `qTT`) and `0⇒4` (via `qOff`), both at target height `1` — a double vote. -/
theorem overlap_double {v : Fin N} (hv : v ∈ qTT N ∩ qOff N) :
    slashed_double_vote (stOverlap N) v :=
  ⟨1, 4, by decide, 0, 0, 0, 0, 1,
   subO_01 N (mem_votes_for_link.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩),
   subO_04 N (mem_votes_for_link.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩)⟩

theorem overlap_slashed {v : Fin N} (hv : v ∈ qTT N ∩ qOff N) : slashed (stOverlap N) v :=
  Or.inl (overlap_double N hv)

end

/-! ### Executable cross-check (`N = 120`): the slashed set is *exactly* the overlap window.

`qTT 120 = [0,80)`, `qOff 120 = [40,120)`, overlap `[40,80)` — `40` validators.
Contrast `JustifiedFork` (both links share `qTT`, so all `80` of `qTT` are slashed): here
the distinct quorums slash **only** their overlap, `80 − 40 = 40 = two_third 120 − one_third 120`. -/

#eval ((List.finRange 120).filter (fun v => slashedB (stOverlap 120) v)).length
  -- 40  =  two_third 120 - one_third 120  =  N - N/3 - N/3
#eval (τ.two_third 120 - τ.one_third 120 : Nat)                      -- 40 (exact overlap weight)
#eval justifiedB τ (stake 120) (vset 120) parent genesis (stOverlap 120) 1 1   -- true
#eval justifiedB τ (stake 120) (vset 120) parent genesis (stOverlap 120) 4 1   -- true (same height)

end GasperBeaconChain.Executable.UseCases.Parametric
