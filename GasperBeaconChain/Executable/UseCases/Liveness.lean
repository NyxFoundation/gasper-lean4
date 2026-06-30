import GasperBeaconChain.Executable.UseCases.Model
import GasperBeaconChain.Core.Theories.PlausibleLiveness
import GasperBeaconChain.Core.Theories.SlashableBound


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

def genesisL : Nat := 0

def parentL : Nat → Nat → Prop := fun a b => b = a + 1

instance : DecidableRel parentL := fun a b => by unfold parentL; infer_instance

def vsetL : Nat → Finset V := fun _ => Finset.univ



theorem empty_not_slashed : ∀ v : V, ¬ slashed (∅ : State V Nat) v := by decide

theorem qctxL : QuorumContext τ stake vsetL :=
  quorum_context_of_threshold_pos τ stake vsetL
    (fun _ => (by decide : 0 < τ.two_third (wt stake (Finset.univ : Finset V))))



theorem two_thirds_good_empty : two_thirds_good τ stake vsetL (∅ : State V Nat) :=
  fun _ => ⟨Finset.univ,
    ⟨Finset.subset_univ _,
     (by decide : τ.two_third (wt stake (Finset.univ : Finset V)) ≤ wt stake Finset.univ)⟩,
    fun v _ => empty_not_slashed v⟩

theorem good_votes_empty : good_votes τ stake vsetL parentL genesisL (∅ : State V Nat) := by
  intro _ _ _ _ _
  refine ⟨fun _ _ _ _ hvm => absurd hvm (Finset.notMem_empty _),
          fun _ _ _ _ hvm => absurd hvm (Finset.notMem_empty _)⟩

theorem wf_empty : votes_from_target_vset_property vsetL (∅ : State V Nat) := by
  intro x s t s_h t_h hx
  exact absurd (mem_link_supporters.mp hx) (Finset.notMem_empty _)

theorem unslashed_empty : ¬ q_intersection_slashed τ stake vsetL (∅ : State V Nat) := by
  rintro ⟨bL, bR, qL, qR, hqLsub, hqRsub, hqL, hqR, hsl⟩
  have key := quorum_intersection_weight_lower τ stake hqLsub hqRsub hqL.2 hqR.2
  have hself : wt stake (vsetL bL ∩ vsetL bR) = wt stake (Finset.univ : Finset V) :=
    congrArg (wt stake) (Finset.inter_self (Finset.univ : Finset V))
  have hfast : (33 : Nat) ≤ wt stake (Finset.univ : Finset V)
      - τ.one_third (wt stake Finset.univ) - τ.one_third (wt stake Finset.univ) := by decide
  have h33 : (33 : Nat) ≤ wt stake (qL ∩ qR) :=
    le_trans
      (le_of_le_of_eq hfast
        (congrArg
          (fun x => x - τ.one_third (wt stake Finset.univ)
                      - τ.one_third (wt stake Finset.univ)) hself.symm))
      key
  have hz : wt stake (qL ∩ qR) = 0 :=
    Finset.sum_eq_zero (fun v hv =>
      absurd (hsl v (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)
             (empty_not_slashed v))
  exact absurd (le_of_le_of_eq h33 hz) (by decide)



theorem nth_anc_chain : ∀ (b n : Nat), nth_ancestor parentL n b (b + n)
  | b, 0 => nth_ancestor.nth_ancestor_0 b
  | b, n + 1 => nth_ancestor.nth_ancestor_nth (nth_anc_chain b n) rfl

theorem blocks_high : ∀ b : Nat, blocks_exist_high_over parentL b :=
  fun b n _ => ⟨b + n, nth_anc_chain b n⟩



theorem plausible_liveness_from_empty :
    ∃ st' : State V Nat,
      unslashed_can_extend (∅ : State V Nat) st' ∧
      no_new_slashed (∅ : State V Nat) st' ∧
      ∃ nf nc : Nat, ∃ nh : Nat,
        justified τ stake vsetL parentL genesisL st' nf nh ∧
        parentL nf nc ∧
        supermajority_link τ stake vsetL st' nf nc nh (nh + 1) :=
  plausible_liveness_construct_extension τ stake vsetL parentL genesisL ∅
    qctxL two_thirds_good_empty unslashed_empty good_votes_empty wf_empty
    (fun b _ _ => blocks_high b)



def stLive : State V Nat :=
  { { validator := 0, source := 0, target := 1, sourceHeight := 0, targetHeight := 5 },
    { validator := 0, source := 0, target := 2, sourceHeight := 0, targetHeight := 5 } }

#eval notSlashedB stLive 0
#eval notSlashedB stLive 1
#eval goodQuorumAtB τ stake vsetL stLive 0 Finset.univ
#eval goodQuorumAtB τ stake vsetL stLive 0 (Finset.univ.filter (fun v => v ≠ (0 : V)))

theorem slashed_0 : slashed stLive 0 :=
  Or.inl ⟨1, 2, by decide, 0, 0, 0, 0, 5, by decide, by decide⟩

theorem mem_stLive_val {w : Vote V Nat} (hw : w ∈ stLive) : w.validator = 0 :=
  (Finset.mem_insert.mp hw).elim
    (fun h => congrArg Vote.validator h)
    (fun h => congrArg Vote.validator (Finset.mem_singleton.mp h))

theorem only_0_slashed {v : V} (hsl : slashed stLive v) : v = 0 := by
  rcases hsl with ⟨_, _, _, _, _, _, _, _, hv, _⟩ | ⟨_, _, _, _, _, _, _, _, hv, _, _, _⟩
  · exact mem_stLive_val hv
  · exact mem_stLive_val hv

theorem univ_not_good : ¬ IsGoodQuorumAt τ stake vsetL stLive 0 Finset.univ :=
  fun ⟨_, hall⟩ => hall 0 (Finset.mem_univ 0) slashed_0

theorem erase0_good :
    IsGoodQuorumAt τ stake vsetL stLive 0 (Finset.univ.filter (fun v => v ≠ (0 : V))) :=
  ⟨⟨Finset.filter_subset _ _,
     (by decide : τ.two_third (wt stake (Finset.univ : Finset V))
        ≤ wt stake (Finset.univ.filter (fun v => v ≠ (0 : V))))⟩,
   fun v hv hsl => (Finset.mem_filter.mp hv).2 (only_0_slashed hsl)⟩

theorem two_thirds_good_as_checker (st : State V Nat) :
    two_thirds_good τ stake vsetL st ↔
    ∀ b : Nat, ∃ q2 : Finset V, IsGoodQuorumAt τ stake vsetL st b q2 :=
  two_thirds_good_iff_forall_exists_goodQuorum τ stake vsetL st

end GasperBeaconChain.Executable.UseCases
