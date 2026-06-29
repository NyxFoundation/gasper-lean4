import GasperBeaconChain.Executable.UseCases.ModelN

/-!
# Use case — `k = 2` finalization (Gasper §8.5 four-case rule, Definition 4.9)

`1`-finalization (a justified pair justifying the next epoch-boundary pair) is the common
case and is demonstrated in the legacy `Finality` use case.  Gasper's Definition 4.9 also
admits **`k`-finalization** for `k ≥ 1`, the `k = 2` instances being Cases 3 and 4 of the
implemented four-case rule (§8.5), needed to absorb attestation-inclusion delay.

We realise a genuine `k = 2` finalization of block `1` (height 1) along the left chain
`1 ⋖ 2 ⋖ 3`:

```text
   1   (B0, height 1, justified)         0 ⇒ 1   (justify B0=1)
   |   ⇘ skip 1⇒3 finalizes              1 ⇒ 2   (justify B1=2)
   2   (B1, height 2, justified)         2 ⇒ 3   (justify B2=3)
   |                                     1 ⇒ 3   (SKIP, the k=2 finalizing supermajority link)
   3   (B2, height 3)
```

By Definition 4.9 with `k = 2`: the adjacent justified pairs `(1,1),(2,2)` and the
supermajority **skip link** `1 ⇒ 3` over heights `1→3` finalize `(1,1)`.  We construct the
witnessing list `[1,2,3]` and discharge the `∀ n ≤ 2` justification/ancestry obligations via
`leq_two_means`, then convert to `1`-... no: this is irreducibly `k = 2`.  Size-parametric
in `N`, `Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

section
variable (N : Nat)

/-- The chain state: justification links `0⇒1`, `1⇒2`, `2⇒3` plus the `k=2` finalizing
**skip link** `1⇒3` (heights `1→3`), all by `qTT`. -/
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
/-- The `k=2` finalizing **skip link** `1 ⇒ 3` over heights `1→3`. -/
theorem smK_13 : supermajority_link τ (stake N) (vset N) (stK2 N) 1 3 1 3 :=
  supermajority_link_of_quorum_votes τ (stake N) (vset N) (quorum2_qTT N 3) (subK_13 N) (wf_vset N _)

/-- The three adjacent justified pairs of the chain. -/
theorem jK_1 : justified τ (stake N) (vset N) parent genesis (stK2 N) 1 1 :=
  justified.justified_link justified.justified_genesis ⟨by decide, anc_0_1, smK_01 N⟩
theorem jK_2 : justified τ (stake N) (vset N) parent genesis (stK2 N) 2 2 :=
  justified.justified_link (jK_1 N) ⟨by decide, anc_1_2, smK_12 N⟩
theorem jK_3 : justified τ (stake N) (vset N) parent genesis (stK2 N) 3 3 :=
  justified.justified_link (jK_2 N) ⟨by decide, anc_2_3, smK_23 N⟩

/-- **`k = 2` finalization** of block `1` (Definition 4.9): the witnessing list is `[1,2,3]`,
the per-step justifications are `jK_1`/`jK_2`/`jK_3`, and the finalizing supermajority link is
the skip link `smK_13`. -/
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

/-- The `k = 2` finalization, like all finalizations, entails justification of the base
block (the real Core lemma `k_finalized_means_justified`). -/
theorem block1_justified_via_k2 :
    justified τ (stake N) (vset N) parent genesis (stK2 N) 1 1 :=
  k_finalized_means_justified τ (stake N) (vset N) parent genesis (stK2 N) (block1_k2_finalized N)

/-- The last pair of the `k = 2` finalization is justified at height `1 + 2 = 3` and is the
`2`-ancestor of `1` (the real Core lemma `k_finalized_last_justified`). -/
theorem block1_k2_last :
    ∃ last : H,
      justified τ (stake N) (vset N) parent genesis (stK2 N) last 3
      ∧ nth_ancestor parent 2 1 last
      ∧ supermajority_link τ (stake N) (vset N) (stK2 N) 1 last 1 3 :=
  k_finalized_last_justified τ (stake N) (vset N) parent genesis (stK2 N) (block1_k2_finalized N)

end

/-! ### Executable cross-check (`N = 111`): the whole left chain is justified. -/

#eval justifiedB τ (stake 111) (vset 111) parent genesis (stK2 111) 1 1   -- true
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stK2 111) 2 2   -- true
#eval justifiedB τ (stake 111) (vset 111) parent genesis (stK2 111) 3 3   -- true

end GasperBeaconChain.Executable.UseCases.Parametric
