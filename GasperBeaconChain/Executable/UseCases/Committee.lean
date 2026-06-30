import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import GasperBeaconChain.Core.AtomicDef.Weight


namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core



theorem nodup_ofFn_of_injective {α : Type*} :
    ∀ {m : Nat} (f : Fin m → α), Function.Injective f → (List.ofFn f).Nodup
  | 0, f, _ =>
      Eq.subst (motive := fun l => l.Nodup) (List.ofFn_zero (f := f)).symm List.nodup_nil
  | _ + 1, f, hf =>
      Eq.subst (motive := fun l => l.Nodup) (List.ofFn_succ (f := f)).symm
        (List.nodup_cons.mpr
          ⟨fun hmem => match List.mem_ofFn.mp hmem with
             | ⟨i, hi⟩ => Fin.succ_ne_zero i (hf hi),
           nodup_ofFn_of_injective (fun i => f i.succ)
             (fun _ _ h => Fin.succ_injective _ (hf h))⟩)

theorem nodup_finRange_cf (n : Nat) : (List.finRange n).Nodup :=
  nodup_ofFn_of_injective (fun i => i) (fun _ _ h => h)

instance (priority := 10000) finFintypeCF (n : Nat) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, nodup_finRange_cf n⟩, List.mem_finRange⟩



theorem card_univ_cf (n : Nat) : (Finset.univ : Finset (Fin n)).card = n :=
  (Multiset.coe_card (List.finRange n)).trans List.length_finRange

theorem wt_one_eq_card {α : Type*} (s : Finset α) :
    wt (fun _ => 1) s = s.card :=
  (Finset.card_eq_sum_ones s).symm

theorem wt_one_univ (N : Nat) :
    wt (fun _ => 1) (Finset.univ : Finset (Fin N)) = N :=
  (wt_one_eq_card _).trans (card_univ_cf N)



def lowerQuorum (N k : Nat) (h : k ≤ N) : Finset (Fin N) :=
  Finset.map (Fin.castLEEmb h) Finset.univ

theorem mem_lowerQuorum {N k : Nat} {h : k ≤ N} {i : Fin N} :
    i ∈ lowerQuorum N k h ↔ i.val < k :=
  ⟨fun hi => match Finset.mem_map.mp hi with
     | ⟨a, _, ha⟩ => Eq.subst (motive := fun x => x < k) (congrArg Fin.val ha) a.isLt,
   fun hlt => Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩⟩

theorem card_lowerQuorum (N k : Nat) (h : k ≤ N) :
    (lowerQuorum N k h).card = k :=
  (Finset.card_map _).trans (card_univ_cf k)

theorem wt_lowerQuorum (N k : Nat) (h : k ≤ N) :
    wt (fun _ => 1) (lowerQuorum N k h) = k :=
  (wt_one_eq_card _).trans (card_lowerQuorum N k h)

def offsetEmb (N base k : Nat) (h : base + k ≤ N) : Fin k ↪ Fin N :=
  ⟨fun j => ⟨base + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt base) h⟩,
   fun _ _ hab => Fin.ext (Nat.add_left_cancel (congrArg Fin.val hab))⟩

def upperQuorum (N base k : Nat) (h : base + k ≤ N) : Finset (Fin N) :=
  Finset.map (offsetEmb N base k h) Finset.univ

theorem mem_upperQuorum {N base k : Nat} {h : base + k ≤ N} {i : Fin N} :
    i ∈ upperQuorum N base k h ↔ base ≤ i.val ∧ i.val < base + k :=
  ⟨fun hi => match Finset.mem_map.mp hi with
     | ⟨j, _, hj⟩ =>
       have hval : base + j.val = i.val := congrArg Fin.val hj
       ⟨Eq.subst (motive := fun x => base ≤ x) hval (Nat.le_add_right base j.val),
        Eq.subst (motive := fun x => x < base + k) hval (Nat.add_lt_add_left j.isLt base)⟩,
   fun ⟨hge, hlt⟩ =>
     Finset.mem_map.mpr
       ⟨⟨i.val - base, Nat.sub_lt_left_of_lt_add hge hlt⟩, Finset.mem_univ _,
        Fin.ext (Nat.add_sub_cancel' hge)⟩⟩

theorem card_upperQuorum (N base k : Nat) (h : base + k ≤ N) :
    (upperQuorum N base k h).card = k :=
  (Finset.card_map _).trans (card_univ_cf k)

theorem wt_upperQuorum (N base k : Nat) (h : base + k ≤ N) :
    wt (fun _ => 1) (upperQuorum N base k h) = k :=
  (wt_one_eq_card _).trans (card_upperQuorum N base k h)

end GasperBeaconChain.Executable.UseCases
