import Mathlib.Data.Nat.Basic

universe v

namespace GasperBeaconChain.Core

/-!
# Strong induction principles

Two well-founded recursion principles over $`\mathbb{N}`, both
derived from {name}`Nat.strong_induction_on`.

## The two principles

* {lit}`strong_induction_ltn` — ordinary course-of-values induction
  on the $`<` order.
* {lit}`strong_induction_sub` — induction whose well-founded measure
  is the *gap* $`n - k` above a fixed offset $`k`, rather than $`n`
  itself.

## Why a shifted measure is needed

The accountable-safety proof walks from a justified block *downward*
along justification links toward a *fixed* finalized checkpoint at
height $`k`. At each step the source height strictly decreases
while staying above $`k`, so the gap $`(\cdot) - k` strictly
decreases. Ordinary induction on $`n` cannot express this because
the offset $`k` is a fixed external parameter, not part of the
recursion variable. {lit}`strong_induction_sub` packages exactly
this pattern: it recurses on the gap $`n - k`, with the guard
$`k < v_{1a}` ensuring the truncated subtraction is a genuine
positive quantity.

## Downstream use

{lit}`strong_induction_sub` drives the well-founded recursion of
{lit}`k_non_equal_height_case_ind` in
{lit}`Theories/AccountableSafety.lean`, where the induction
descends on $`b_{1,h} - b_{2,h}` as the source height strictly
decreases along justification links while staying above the
finalized height $`b_{2,h}`.
-/

/--
# Course-of-values induction on $`\mathbb{N}`

Ordinary **strong induction** on $`\mathbb{N}`:

$$`\bigl(\forall m,\; (\forall n,\; n < m \to P\,n) \to P\,m\bigr) \;\implies\; \forall n,\; P\,n`

# Interpretation

The hypothesis asserts that to prove $`P` at $`m`, it suffices to
know $`P` holds at every strictly smaller argument. The conclusion
then gives $`P\,n` for all $`n`. This is the standard
course-of-values induction on the well-founded order $`<` on
$`\mathbb{N}` — strictly stronger than ordinary induction because
the induction hypothesis is available at *all* predecessors, not
just $`m - 1`.

# Proof

A direct repackaging of {name}`Nat.strong_induction_on`, which
provides exactly this principle from the well-foundedness of $`<`
on $`\mathbb{N}`.
-/
theorem strong_induction_ltn
    {P : Nat → Prop}
    (IH : ∀ m : Nat, (∀ n : Nat, n < m → P n) → P m) :
    ∀ n : Nat, P n :=
  fun n => Nat.strong_induction_on n (fun m ih => IH m ih)

/--
# Strong induction on the gap $`n - k` above a fixed offset

**Strong induction on a shifted measure.** For a fixed offset
$`k`, the predicate $`P` holds everywhere provided each
$`P\,v_1\,h_1` follows from $`P` at all arguments whose *gap above
$`k`* is strictly smaller:

$$`\Bigl(\forall v_1\, h_1,\;\bigl(\forall v_{1a}\, h_{1a},\; k < v_{1a} \to v_{1a} - k < v_1 - k \to P\,v_{1a}\,h_{1a}\bigr) \to P\,v_1\,h_1\Bigr) \;\implies\; \forall n\, t,\; P\,n\,t`

# Interpretation

The recursion measure is the gap $`n - k`, not $`n` itself. The
guard $`k < v_{1a}` keeps the truncated subtraction $`v_{1a} - k`
honest (strictly positive), so $`v_{1a} - k < v_1 - k` is a genuine
decrease rather than an artefact of truncation at $`0`.

# Proof idea

Reduce to {name}`strong_induction_ltn` on the quantity
$`m = n - k`: prove the auxiliary
$`\forall m,\;\forall n\, t,\; n - k = m \to P\,n\,t` by ordinary
strong induction on $`m`, then instantiate at $`m = n - k` with
{lit}`rfl`.

# Role in the development

The induction backbone of {lit}`k_non_equal_height_case_ind`:
walking from a justified block down its justification links, the
source height drops at each step while remaining above the
finalized height $`b_{2,h}`, so the gap $`(\cdot) - b_{2,h}`
strictly decreases and the recursion is well-founded.
-/
theorem strong_induction_sub
    {k : Nat}
    {T : Type v}
    {P : Nat → T → Prop}
    (IH :
      ∀ (v1 : Nat) (h1 : T),
        (∀ (v1a : Nat) (h1a : T),
          k < v1a →
          v1a - k < v1 - k →
          P v1a h1a) →
        P v1 h1) :
    ∀ (n : Nat) (t : T), P n t :=
  have hQ : ∀ m : Nat, ∀ (n : Nat) (t : T), n - k = m → P n t :=
    strong_induction_ltn (P := fun m => ∀ (n : Nat) (t : T), n - k = m → P n t)
      (fun _ hm n t hn => IH n t
        (fun v1a h1a _ hlt => hm (v1a - k)
          (Eq.subst (motive := fun x => v1a - k < x) hn hlt) v1a h1a rfl))
  fun n t => hQ (n - k) n t rfl

end GasperBeaconChain.Core
