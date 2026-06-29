import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import GasperBeaconChain.Core.AtomicDef.Weight

/-!
# Committee scaffolding — a `Classical.choice`-free, size-parametric validator universe

The executable use cases instantiate the abstractly-`[Fintype Validator]` Core at a
concrete validator type `Fin N`.  Mathlib's default `Fin.fintype` is
**`Classical.choice`-tainted** (its `elems` field carries the `Nodup` witness
`List.nodup_finRange`, whose axioms include `Classical.choice`; `Finset.range` likewise).
Consequently *every* `Finset.univ : Finset (Fin N)` — and therefore `link_supporters`,
the quorum weights, `vset` — would inherit `Classical.choice` the moment the Core is
instantiated at a concrete `Fin N`.

Previously this was patched per fixed `N` by discharging the `Nodup` obligation with
`decide` (only possible for a *literal* `N`).  Here we generalise that fix to **all `N`**:
we prove `(List.ofFn id).Nodup` constructively from the choice-free structural lemmas
`List.ofFn_succ` / `List.ofFn_zero` / `List.mem_ofFn` / `List.nodup_cons` and the
injectivity / non-vanishing of `Fin.succ`.  The completeness field is the already
choice-free `List.mem_finRange`.  The resulting instance `finFintypeCF n` depends only
on `[propext, Quot.sound]`.

Because a `Finset` is proof-irrelevant in its `Nodup` field, `Finset.univ` under this
instance is **definitionally equal** to the default one (same underlying `finRange`
multiset), so every structural `Finset` lemma applies verbatim; only the axiom
provenance is cleaned.

On top of this we build, with uniform unit stake, **exact-weight quorums** as images of
smaller universes (`Finset.map`), so a 2/3 quorum's weight is computed *exactly* (via
`Finset.card_map`) rather than `decide`d — size-independent, and free of the `maxRecDepth`
cost of deciding `O(N)`/`O(N²)` cardinalities.
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core


/-! ## 1. The choice-free finite universe -/

/--
`(List.ofFn f).Nodup` for an injective family `f`, proved constructively (no
`Classical.choice`).  Induction on the arity: the head `f 0` is distinct from every
`f i.succ` because `f` is injective and `i.succ ≠ 0`; the tail is `ofFn` of the injective
family `f ∘ Fin.succ`.
-/
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

/-- `List.finRange n = List.ofFn id` has no duplicates — choice-free. -/
theorem nodup_finRange_cf (n : Nat) : (List.finRange n).Nodup :=
  nodup_ofFn_of_injective (fun i => i) (fun _ _ h => h)

/--
A `Classical.choice`-free `Fintype (Fin n)` for **every** `n`.  Higher priority so it
overrides Mathlib's choice-tainted `Fin.fintype` wherever a concrete `Fin n` universe is
needed in the use cases.
-/
instance (priority := 10000) finFintypeCF (n : Nat) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, nodup_finRange_cf n⟩, List.mem_finRange⟩


/-! ## 2. Cardinality and uniform-stake weight -/

/-- `card (univ : Finset (Fin n)) = n`, choice-free (avoids the tainted `Fintype.card_fin`). -/
theorem card_univ_cf (n : Nat) : (Finset.univ : Finset (Fin n)).card = n :=
  (Multiset.coe_card (List.finRange n)).trans List.length_finRange

/-- Under unit stake, weight is just cardinality. -/
theorem wt_one_eq_card {α : Type*} (s : Finset α) :
    wt (fun _ => 1) s = s.card :=
  (Finset.card_eq_sum_ones s).symm

/-- The whole committee of `N` unit-stake validators has weight `N`. -/
theorem wt_one_univ (N : Nat) :
    wt (fun _ => 1) (Finset.univ : Finset (Fin N)) = N :=
  (wt_one_eq_card _).trans (card_univ_cf N)


/-! ## 3. Exact-weight quorums as images of smaller universes

The first `k` validators (`k ≤ N`), and a window of `k` validators starting at index
`base` (`base + k ≤ N`), realised as `Finset.map` images so their cardinalities — hence
weights under unit stake — are *exactly* `k`, computed by `Finset.card_map` independently
of `N`. -/

/-- The first `k` validators `{0,…,k-1}` of an `N`-committee (`k ≤ N`). -/
def lowerQuorum (N k : Nat) (h : k ≤ N) : Finset (Fin N) :=
  Finset.map (Fin.castLEEmb h) Finset.univ

/-- `i` is among the first `k` validators iff its index is `< k`. -/
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

/-- The offset embedding `j ↦ ⟨base + j, _⟩ : Fin k ↪ Fin N` for `base + k ≤ N`. -/
def offsetEmb (N base k : Nat) (h : base + k ≤ N) : Fin k ↪ Fin N :=
  ⟨fun j => ⟨base + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt base) h⟩,
   fun _ _ hab => Fin.ext (Nat.add_left_cancel (congrArg Fin.val hab))⟩

/-- The window of `k` validators `{base,…,base+k-1}` of an `N`-committee. -/
def upperQuorum (N base k : Nat) (h : base + k ≤ N) : Finset (Fin N) :=
  Finset.map (offsetEmb N base k h) Finset.univ

/-- `i` is in the window iff `base ≤ i.val < base + k`. -/
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
