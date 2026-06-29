import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

universe u

namespace GasperBeaconChain.Core

/-!
# Weight of validator sets

The **weight** of a finite validator set — the sum of individual
stakes over the set.

## Definition

Given a stake function
$`\mathsf{stake} : \mathsf{Validator} \to \mathbb{N}` and a finite
set $`s \subseteq \mathsf{Validator}`, define

$$`\operatorname{wt}(\mathsf{stake},\; s) \;\;\coloneqq\;\; \sum_{v \in s} \mathsf{stake}(v)`

The sum is computed via {name}`Finset.sum`. It is independent of the
enumeration order because addition on $`\mathbb{N}` is associative
and commutative ($`(\mathbb{N}, +, 0)` is an additive commutative
monoid), and each validator contributes its stake exactly once
because a {name}`Finset` carries no duplicates.

## Arguments

The definition takes two explicit arguments and one implicit type
parameter:

* $`\mathsf{stake} : \mathsf{Validator} \to \mathbb{N}` —
  the per-validator weight function,
* $`s \in \mathsf{Finset}(\mathsf{Validator})` — the finite set
  to sum over.

When $`\mathsf{stake}` is fixed by the context, one writes
$`\operatorname{wt}(s)` for $`\operatorname{wt}(\mathsf{stake}, s)`.

## Mathematical role

For a fixed $`\mathsf{stake}`, the map
$`\operatorname{wt}(\mathsf{stake}, \cdot)` is a **finitely additive
set function** from $`\mathsf{Finset}(\mathsf{Validator})` to
$`\mathbb{N}`. In particular it is monotone with respect to the
subset ordering:
$`s \subseteq t \implies \operatorname{wt}(s) \le \operatorname{wt}(t)`.
These properties are established in
{lit}`Lemmas/Weight.lean` and are central to the quorum-intersection
arithmetic.

Coq: {lit}`wt (s : {set Validator}) := \sum_(v in s) stake.[st_fun v]`.
In the Coq development $`\mathsf{stake}` is a global parameter;
here it is an explicit argument.
-/

/--
The **weight function**: converts a finite set of validators into a
single natural number measuring its total stake.

$$`\operatorname{wt}(\mathsf{stake},\; s) \;\;\coloneqq\;\; \sum_{v \in s} \mathsf{stake}(v)`

The sum is computed via {name}`Finset.sum`. This definition is the
bridge between the combinatorial structure ({name}`Finset`) and the
arithmetic of quorum thresholds.

Coq source: {lit}`Weight.v`. Coq uses a partial finite map with a
totality witness; Lean uses a total function directly. In Coq
$`\mathsf{stake}` is a global parameter; here it is an explicit
argument.
-/
def wt
    {Validator : Type u}
    (stake : Validator → Nat)
    (s : Finset Validator) : Nat :=
  s.sum stake

end GasperBeaconChain.Core
