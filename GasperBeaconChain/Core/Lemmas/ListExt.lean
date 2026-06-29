import Mathlib.Data.List.Basic

universe u

namespace GasperBeaconChain.Core

/-!
# List indexing reconciliation

Three small facts reconciling the {name}`List` accessors used to
index the $`k`-finalization chain in {lit}`k_finalized`.

## The representation problem

The chain of $`k + 1` blocks is stored as a {lit}`List Hash`
(mirroring the Coq development) rather than a length-indexed
vector. Three different accessors are used in different contexts:

* {name}`List.headD` — reads the first block. Used in the head
  condition of {lit}`k_finalized`.
* {name}`List.getD` — reads an interior block by index. Used in
  the universal quantifier of {lit}`k_finalized`.
* {name}`List.getLastD` — reads the last block. Used in the
  supermajority-link conclusion of {lit}`k_finalized`.

## The reconciliation lemmas

These lemmas convert between the three accessors so that the
chain hypotheses (phrased with {name}`List.getD`) and the endpoint
conclusions (phrased with {name}`List.headD` /
{name}`List.getLastD`) can be matched:

* {lit}`list_getD_zero_eq_headD` —
  $`\mathrm{getD}\,0 = \mathrm{headD}`, definitional
* {lit}`list_getLastD_eq_getD_of_length_eq_succ` —
  the structural kernel, by induction on $`k`
* {lit}`list_getLastD_eq_getD_one_of_length_two` —
  the $`k = 1` specialization

## Downstream use

Consumed in {lit}`Lemmas/Justification.lean` by
{lit}`finalized_means_one_finalized` (the $`k = 1` head/last case)
and {lit}`k_finalized_last_justified` (the length-$`(k+1)` last
case).
-/

variable {α : Type u}

/--
# The zeroth element is the head

{name}`List.getD` at index $`0` agrees with {name}`List.headD`:

$$`xs.\mathrm{getD}\,0\,d \;=\; xs.\mathrm{headD}\,d`

Both sides inspect only the head constructor of $`xs`, so they
reduce identically; the proof is a case split on $`xs` closed by
{lit}`rfl`. Used in {lit}`k_finalized_means_justified` to convert
the chain's head condition (phrased with {name}`List.headD`) into
the positional accessor (phrased with {name}`List.getD`) at
$`n = 0`.
-/
theorem list_getD_zero_eq_headD
    (xs : List α)
    (d : α) :
    xs.getD 0 d = xs.headD d :=
  match xs with
  | [] => rfl
  | _ :: _ => rfl

/--
# The last element of a length-$`(k+1)` list is at index $`k`

For a list of length $`k + 1`, the last element equals the element
at positional index $`k`:

$$`|xs| = k + 1 \;\implies\; xs.\mathrm{getLastD}\,d \;=\; xs.\mathrm{getD}\,k\,d`

# Proof idea

Induction on $`k`, peeling one cons per step. The length hypothesis
$`|xs| = k + 1` keeps the list nonempty at every stage, so the
default value $`d` is never reached and the two accessors track the
same element.

# Role in the development

The indexing identity behind {lit}`k_finalized_last_justified`: the
$`k`-finalization chain has length $`k + 1`, and its last block —
written {lit}`ls.getLastD b` in the conclusion — is read
positionally at index $`k` (written {lit}`ls.getD k b`) in the
chain hypothesis.
-/
theorem list_getLastD_eq_getD_of_length_eq_succ
    (xs : List α)
    (d : α)
    {k : Nat}
    (hlen : xs.length = k + 1) :
    xs.getLastD d = xs.getD k d :=
  match k, xs, hlen with
  | 0, [_], _ => rfl
  | Nat.succ k, _ :: b :: ys, hlen =>
      show (b :: ys).getLastD d = (b :: ys).getD k d from
        list_getLastD_eq_getD_of_length_eq_succ (b :: ys) d (Nat.add_right_cancel hlen)

/--
# The last element of a two-element list is at index $`1`

The length-$`2` instance of
{name}`list_getLastD_eq_getD_of_length_eq_succ`:

$$`|xs| = 2 \;\implies\; xs.\mathrm{getLastD}\,d \;=\; xs.\mathrm{getD}\,1\,d`

Used in the $`k = 1` direction of
{lit}`finalized_means_one_finalized`, whose chain $`[b, c]` has
length $`2` and last block $`c` at index $`1`.
-/
theorem list_getLastD_eq_getD_one_of_length_two
    (xs : List α)
    (d : α)
    (hlen : xs.length = 2) :
    xs.getLastD d = xs.getD 1 d :=
  list_getLastD_eq_getD_of_length_eq_succ xs d hlen

end GasperBeaconChain.Core
