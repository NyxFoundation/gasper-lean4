import GasperBeaconChain.Basic

/-!
# Gasper Beacon Chain

Lean 4 formalization of the core safety and liveness properties of
Casper FFG, the finality gadget underlying the Ethereum Beacon Chain.

This development establishes three results from
*Combining GHOST and Casper* (Buterin et al., 2020),
ported and extended from the
[Coq formalization](https://github.com/runtimeverification/beacon-chain-verification)
by Musab A. Alturki (Runtime Verification / KAUST, 2020).

## Accountable safety

A finalization fork (two conflicting finalized blocks) implies the
existence of two $`\frac{2}{3}`-quorums whose intersection consists
entirely of slashed validators.

$$`\operatorname{finalization\_fork}(\sigma)
   \;\Longrightarrow\;
   \operatorname{q\_intersection\_slashed}(\sigma)`

The proof generalizes to arbitrary $`k`-finalization and dynamic
validator sets.

## Plausible liveness

Regardless of previous events, it is always possible to extend the
state and finalize a new block without introducing new slashing,
provided blocks exist at sufficient heights and at least
$`\frac{2}{3}` of the stake is honest.

$$`\exists\,\sigma',\;\;
   \operatorname{unslashed\_can\_extend}(\sigma,\sigma')
   \;\wedge\;
   \operatorname{no\_new\_slashed}(\sigma,\sigma')
   \;\wedge\;
   \operatorname{finalized}(\sigma')`

## Slashable bound

A finalization fork produces a quorum pair whose intersection weight
is lower-bounded by the churn-adjusted validator-set overlap:

$$`\max\!\bigl(\operatorname{wt}(V_L) - a_L - e_R,\;
   \operatorname{wt}(V_R) - a_R - e_L\bigr)
   - f_{1/3}\!\bigl(\operatorname{wt}(V_L)\bigr)
   - f_{1/3}\!\bigl(\operatorname{wt}(V_R)\bigr)
   \;\le\;
   \operatorname{wt}(q_L \cap q_R)`

## Structure

The formalization is organized in three layers:

* **AtomicDef** — Validators, block trees, votes, states, slashing
  conditions, quorums, justification, finalization, thresholds.
* **Lemmas** — Ancestry closure, weight monotonicity,
  inclusion–exclusion, list indexing, strong induction, same-height
  slashing, state extension, maximal-link existence.
* **Theories** — The three main theorems above, with Fitch-style
  proof trees rendered via {lit}`#detail_explode`.
-/
