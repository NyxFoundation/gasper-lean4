# Formal Verification of Gasper in Lean 4

A Lean 4 + Mathlib formalization of the finality mechanism of **Casper FFG**, the component of the
[Gasper protocol](https://arxiv.org/abs/2003.03052) (Buterin et al., 2020) that guarantees
irreversibility of finalized blocks in the Ethereum Beacon Chain.

**[Live documentation](https://nyxfoundation.github.io/gasper-lean4/)**

---

## What is proved

Three core properties of Casper FFG are formally verified:

### Accountable Safety

If two conflicting blocks are both finalized — meaning the protocol has committed to two
incompatible histories — then every validator in the intersection of the two supporting
⅔-quorums has provably violated a slashing condition:

- **(S1) Equivocation** — two votes to distinct targets at the same height.
- **(S2) Surround vote** — one vote's source–target span strictly contains another's.

The result generalises Casper FFG Theorem 1 (and Gasper Theorem 5.2) in two directions:
from 1-finalization to arbitrary *k*-finalization, and from static to dynamic validator sets.

$$\text{finalization-fork}(\sigma) \;\Longrightarrow\; \text{q-intersection-slashed}(\sigma)$$

### Plausible Liveness

Regardless of past events, it is always possible to extend the protocol state and finalize a new
block without introducing new slashing — provided the underlying blockchain keeps producing blocks
and at least ⅔ of the stake is honest.

$$\exists\,\sigma',\quad \text{unslashed-can-extend}(\sigma,\sigma') \;\wedge\; \text{no-new-slashed}(\sigma,\sigma') \;\wedge\; \text{finalized}(\sigma')$$

### Slashable Bound

The quorum intersection that Accountable Safety forces to be slashed has quantitatively positive
weight, with an explicit lower bound accounting for validator churn (activations and exits relative
to a reference set):

$$\max\!\bigl(\mathrm{wt}(V_L)-a_L-e_R,\;\mathrm{wt}(V_R)-a_R-e_L\bigr) - f_{1/3}\!\bigl(\mathrm{wt}(V_L)\bigr) - f_{1/3}\!\bigl(\mathrm{wt}(V_R)\bigr) \;\le\; \mathrm{wt}(q_L \cap q_R)$$

---

## Relation to the Coq formalization

This development translates and substantially extends the Coq formalization by
[Runtime Verification, Inc.](https://github.com/runtimeverification/beacon-chain-verification)

**Key departures from the Coq version:**

| Aspect | Coq version | This Lean 4 version |
|---|---|---|
| Axiom of choice | Used globally | **Eliminated** — proofs are constructive |
| Boolean relations | Defined as `bool`-valued functions | Prop-valued inductive closures |
| Global axioms | Environment-level | First-class term-level values |
| Block existence predicate | Contains a bug | Corrected |
| Lemmas layer | Minimal | New: disjoint-union algebra, weight inclusion–exclusion, strong induction on height gaps |

Eliminating `Classical.choice` means all proofs elaborate to closed terms in the kernel's type
theory, making the theorems constructively valid and the predicates **computationally executable**
via `decide`.

The only non-constructive axioms present are `Quot.sound` and `propext`, inherited through
Mathlib's `Finset` infrastructure.

---

## Structure

```
GasperBeaconChain/
├── Core/
│   ├── AtomicDef/   — validators, block trees, votes, slashing conditions,
│   │                  quorums, justification, k-finalization, liveness hypotheses
│   ├── Lemmas/      — ancestry closure, set algebra, weight monotonicity,
│   │                  quorum up-closure, strong induction, slashing constructions
│   └── Theories/    — AccountableSafety, PlausibleLiveness, SlashableBound
├── Executable/      — Boolean decision-procedure wrappers for all key predicates;
│   └── UseCases/      concrete runnable examples (fork scenarios, slashing detection)
└── Visualizations/  — interactive diagrams (justification ladders, Venn overlaps, …)
```

Each theorem in `Theories/` is accompanied by a `#detail_explode` invocation that renders its
full Fitch-style proof tree in the [live documentation](https://nyxfoundation.github.io/gasper-lean4/).

---

## Building

**Requirements:** [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (`leanprover/lean4:v4.31.0`) and the Lake build tool (included with Lean).

```sh
# Fetch dependencies (Mathlib cache included)
lake update
lake exe cache get

# Build all proofs
lake build
```

**Literate HTML documentation** (requires [Verso](https://github.com/leanprover/verso)):

```sh
make verso-pages   # generates docs/ ready for GitHub Pages
# or, to preview locally:
make verso-facet   # builds and serves at http://localhost:8000
```

---

## References

- V. Buterin et al., [Combining GHOST and Casper](https://arxiv.org/abs/2003.03052), 2020.
- Runtime Verification, Inc., [Beacon Chain Verification (Coq)](https://github.com/runtimeverification/beacon-chain-verification).

---

## License

[MIT](LICENSE) — Copyright © 2026 Nyx Foundation and gasper-lean4 contributors.
