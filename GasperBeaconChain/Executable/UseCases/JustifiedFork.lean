import GasperBeaconChain.Executable.UseCases.ModelN

/-!
# Use case — Lemma 4.11: at most one justified pair per height (the S1 pigeonhole)

**Gasper Lemma 4.11 / Casper property (iv).** In any view, for every height there is at
most one justified checkpoint, *unless* the chain is (1/3)-slashable: two distinct
justified blocks at the **same** height force two 2/3 quorums whose intersection all
violate the double-vote condition S1.

We realise the slashable side concretely.  Genesis `0` has two conflicting children:
`1` (left) and `4` (right), each justified at height `1` by a supermajority link from `0`:

```text
        0          0 ⇒ 1   (target height 1)
       / \         0 ⇒ 4   (target height 1)
      1   4        →  the qTT voters double-voted at height 1  ⇒  S1
```

Feeding the two same-height justifications to the **real** Core theorem
`two_justified_same_height_slashed` (the engine of `no_two_justified_same_height`) yields
the slashable quorum intersection; we also exhibit the explicit S1 double-vote witness.
Size-parametric in `N`, `Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

/-- Two same-height justifications of conflicting blocks `1`, `4`, each by `qTT`. -/
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

/-- Block `1` is justified at height `1`. -/
theorem justJ_1 : justified τ (stake N) (vset N) parent genesis (stJust N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, smJ_01 N⟩
/-- Block `4` is justified at height `1` — the *same* height as block `1`. -/
theorem justJ_4 : justified τ (stake N) (vset N) parent genesis (stJust N) 4 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_4, smJ_04 N⟩

/-- **Lemma 4.11** (the real Core engine `two_justified_same_height_slashed`): two distinct
justified blocks at the same height force a slashable quorum intersection. -/
theorem same_height_slashable : q_intersection_slashed τ (stake N) (vset N) (stJust N) :=
  two_justified_same_height_slashed τ (stake N) (vset N) parent genesis (stJust N)
    (justJ_1 N) (justJ_4 N) (by decide)

/-- The explicit S1 evidence: every quorum member voted `0⇒1` and `0⇒4`, both with target
height `1` (distinct targets `1 ≠ 4`) — a double vote. -/
theorem qTT_double {v : Fin N} (hv : v ∈ qTT N) :
    slashed_double_vote (stJust N) v :=
  ⟨1, 4, by decide, 0, 0, 0, 0, 1,
   subJ_01 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩),
   subJ_04 N (mem_votes_for_link.mpr ⟨v, hv, rfl⟩)⟩

theorem qTT_slashed_S1 {v : Fin N} (hv : v ∈ qTT N) : slashed (stJust N) v :=
  Or.inl (qTT_double N hv)

end

/-! ### Executable cross-check (`N = 111`). -/

#eval slashedB (stJust 111) ⟨0, by decide⟩      -- true  (double voter at height 1)
#eval ((List.finRange 111).filter (fun v => slashedB (stJust 111) v)).length  -- 74 = two_third 111
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stJust 111) 1 1   -- true
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stJust 111) 4 1   -- true (same height!)

end GasperBeaconChain.Executable.UseCases.Parametric
