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

## Model interpretation: the checkpoint tree

The tree on which every definition and theorem is stated is Gasper's **checkpoint tree**,
not the slot-level block tree:

- a node of the type `Hash` is an *epoch boundary pair* $(B, j)$ — a block together with an
  attestation epoch (eth2's `Checkpoint = (epoch, root)`);
- one parent edge spans one attestation epoch, so the tree is graded by the epoch and the vote
  heights $h_s, h_t$ are attestation epochs, i.e. depths in the tree;
- the same block root may occur as several distinct nodes (empty epochs).

This is the reading fixed by the Coq original (`HashTree.v`: *"a 'block' refers to a
'checkpoint block' throughout"*), which the first version of this port left undocumented. It is
now stated in the docstrings of `HashTree.lean`, `State.lean` and `Justification.lean`, and —
more importantly — it is **machine-checked** rather than asserted:

| Gasper notion | Counterpart in the model | Status | Backing |
|---|---|---|---|
| epoch boundary pair $(B, j)$ | node of `Hash`; concretely `Checkpoint = ⟨block, epoch⟩` | formalized | `cp_context` (the concrete tree is a `HashTreeContext`) |
| attestation epoch | heights `s_h`, `t_h` = depth in the tree | formalized | `cp_graded`, `justified_depth`, `justified_height_eq` |
| "source is on the target's checkpoint chain" | graded ancestry `nth_ancestor parent (t_h - s_h) s t` in `justification_link` | formalized | `justification_link_iff_ancestor` (abstract), `cp_link_correspondence`, `cp_justification_link_iff` (concrete) |
| epoch boundary block $\mathrm{EBB}(B, j)$ | `ebb` on a `SlottedChainContext` | formalized | `ebb_slot_le`, `ebb_on_chain`, `on_chain_ebb_of_le`, `ebb_zero`, `ebb_tower` |
| empty epoch (same block as consecutive checkpoints) | distinct nodes with the same `block` | formalized | `cp_empty_epoch`; executable example `Executable/UseCases/EmptyEpoch.lean` |
| $J(G)$ of Definition 4.6 without the chain condition | — | documented only | see limitations below |

Reading guide:

- `Core/AtomicDef/Grading.lean` — the hypothesis `height_graded` (genesis at height 0, each
  parent edge adds 1).
- `Core/Lemmas/Grading.lean` — under that hypothesis the graded condition of
  `justification_link` is equivalent to plain checkpoint ancestry
  (`justification_link_iff_ancestor`), and justified heights are forced to be true depths
  (`justified_height_eq`); `justified_depth` shows the latter even without the hypothesis.
- `Core/Refinement/SlottedChain.lean`, `Core/Refinement/CheckpointTree.lean` — a concrete
  checkpoint tree built from slotted blocks: `Checkpoint`, `cp_parent`, `cp_valid`, the
  refinement `cp_context`, the grading `cp_graded`, empty epochs `cp_empty_epoch`, depth
  `cp_depth`, and the correspondence `cp_ancestor_iff_on_chain` / `cp_link_correspondence`.
- `Executable/UseCases/EmptyEpoch.lean` — a three-block chain with an empty epoch in which the
  checkpoint $(B, 2)$ is justified through the link from $(B, 1)$, both as a proof term over
  the concrete tree and by `decide` / `#eval` on a finite encoding.

**Honest limitations.**

- `justification_link` requires the source to be an ancestor of the target in the checkpoint
  tree. Gasper's raw set $J(G)$ (Definition 4.6) is generated from supermajority links alone
  and imposes no such condition. The ancestry conjunct is a deliberate strengthening inherited
  from the Coq model: it is justification as computed along a chain from the attestations valid
  for that chain. The justified pairs of this model form a subset of $J(G)$; a model variant
  without the ancestry conjunct is not verified here.
- The beacon state transition (committee selection, `process_justification_and_finalization`)
  is not formalized. The refinement layer stops at the structural correspondence of the
  checkpoint tree: nodes, parent edges, grading, and the ancestry condition.
- The height fields of a `Vote` are redundant with checkpoint identifiers and are not
  constrained by the model: states may contain votes with inconsistent heights. This is an
  over-approximation of the reachable states (it can only strengthen the safety theorems);
  along justification chains consistency is forced anyway (`justified_height_eq`).
- `SlottedChainContext` assumes only that slots strictly decrease along parent edges, that
  genesis is at slot 0, and that genesis is the only root. Reachability of every block from
  genesis is derived (`genesis_on_chain`), and $C > 0$ is not needed.

---

## Structure

```
GasperBeaconChain/
├── Audit/           — axiom auditing and build verification tooling;
│   ├── Automated/     automated build audit (axiom-set checks run on every build)
│   └── Meta/          meta-commands: axiom reporting, JSON export, scope checks
├── Core/
│   ├── AtomicDef/   — validators, checkpoint trees, votes, slashing conditions,
│   │                  quorums, justification, k-finalization, liveness hypotheses,
│   │                  height grading of the checkpoint tree
│   ├── Lemmas/      — ancestry closure, set algebra, weight monotonicity,
│   │                  quorum up-closure, strong induction, slashing constructions,
│   │                  grading lemmas (justification heights are depths)
│   ├── Theories/    — AccountableSafety, PlausibleLiveness, SlashableBound
│   └── Refinement/  — concrete (block, epoch) checkpoint tree built from slotted
│                      blocks via epoch boundary blocks; refinement into the abstract tree
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
