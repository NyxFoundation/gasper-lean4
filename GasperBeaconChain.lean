import GasperBeaconChain.Basic

/-!
# Gasper Beacon Chain

A Lean 4 + Mathlib formalization of the finality mechanism of
Casper FFG, the component of the
[Gasper protocol](https://arxiv.org/abs/2003.03052)
(Buterin et al., 2020) that guarantees irreversibility of
finalized blocks in the Ethereum Beacon Chain.

All proofs are written as explicit proof terms in
Lean 4, with an emphasis on constructive derivation
throughout. The proofs depend on {lit}`Quot.sound`
and {lit}`propext` (through Mathlib's {lit}`Finset`
infrastructure), but do not use the axiom of choice
({lit}`Classical.choice`). While the overall theorem
structure draws on the Coq formalization by Runtime
Verification, Inc., the Lean 4 version includes
substantial independent work: Coq's global axioms are
replaced by first-class values, boolean relations are
replaced by Prop-valued inductive closures, the
{lit}`Lemmas` layer introduces new constructions
(disjoint-union set algebra, weight inclusion–exclusion,
strong induction on height gaps, a corrected
block-existence predicate), and each proof is rebuilt
to fit the Lean 4 kernel's type theory.

## References

* V. Buterin et al.,
  [Combining GHOST and Casper](https://arxiv.org/abs/2003.03052),
  2020.
* Runtime Verification, Inc.,
  [Beacon Chain Verification (Coq)](https://github.com/runtimeverification/beacon-chain-verification).

## Accountable safety

Casper FFG Theorem 1 / Gasper Theorem 5.2, generalised
from $`1`-finalization to arbitrary $`k`-finalization and
from static to dynamic validator sets.

The proof has two complementary halves:

* *Structural half*
  ({lit}`accountable_safety`): a finalization fork
  forces every validator in the intersection of two
  $`\frac{2}{3}`-quorums to have violated a slashing
  condition — equivocation (S1) or surround vote (S2).
  The proof proceeds by three-way case split on the
  heights of the two $`k`-finalized blocks, descending
  along justification links by strong induction on the
  height gap.

$$`\operatorname{finalization\_fork}(\sigma)
   \;\Longrightarrow\;
   \operatorname{q\_intersection\_slashed}(\sigma)`

* *Quantitative half*
  ({lit}`slashable_bound`, Gasper Theorem 8.3): the
  weight of that quorum intersection is lower-bounded
  by a churn-adjusted expression, derived via
  inclusion–exclusion on the validator-set weights and
  the quorum thresholds.

$$`\max\!\bigl(\operatorname{wt}(V_L) - a_L - e_R,\;
   \operatorname{wt}(V_R) - a_R - e_L\bigr)
   - f_{1/3}\!\bigl(\operatorname{wt}(V_L)\bigr)
   - f_{1/3}\!\bigl(\operatorname{wt}(V_R)\bigr)
   \;\le\;
   \operatorname{wt}(q_L \cap q_R)`

where $`a_L, a_R` are activation weights and
$`e_L, e_R` are exit weights relative to a reference
validator set $`V_0`.

## Plausible liveness

Casper FFG Theorem 2 / Gasper Theorem 6.1.
Regardless of any previous events, it is always possible
to extend the protocol state and finalize a new block
without introducing new slashing — provided the
underlying blockchain keeps producing blocks and at
least $`\frac{2}{3}` of the stake is honest. The proof
constructs the extended state explicitly by adding two
vote batches at heights $`H + 1` and $`H + 2` (where
$`H` is the highest target height in the current state)
and verifying via a $`3 \times 3` case matrix that no
new double vote or surround vote is introduced.

$$`\exists\,\sigma',\;\;
   \operatorname{unslashed\_can\_extend}(\sigma, \sigma')
   \;\wedge\;
   \operatorname{no\_new\_slashed}(\sigma, \sigma')
   \;\wedge\;
   \operatorname{finalized}(\sigma')`

## Structure

* **AtomicDef** — Core definitions that mirror the Coq
  model: validators and stake, block trees and ancestry,
  votes and protocol states, slashing conditions (S1, S2),
  quorums and thresholds, justification, finalization,
  $`k`-finalization, and the plausible-liveness hypotheses.
* **Lemmas** — Structural lemmas connecting the definitions
  to the theorems: ancestry closure and conflict
  propagation, disjoint-union set algebra,
  weight monotonicity and inclusion–exclusion,
  quorum up-closure and nonemptiness, the
  finalized–$`k`-finalized bridge, strong induction on
  height gaps, the same-height slashing construction,
  state extension with vote classification, and
  maximal-link / highest-block existence.
* **Theories** — The main theorems: accountable safety,
  plausible liveness, and the slashable bound. Each
  theorem is accompanied by a {lit}`#detail_explode`
  invocation that renders its Fitch-style proof tree.

## Scope

This formalization covers Casper FFG finality only.
It does not address the LMD GHOST fork-choice rule,
probabilistic liveness (Gasper §7), or the concrete
Beacon Chain specification.
-/
