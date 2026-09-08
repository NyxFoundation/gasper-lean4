# Reply to the review of `justification_link` (draft)

**Status**: final draft, all claims backed by theorems on branch `fix/checkpoint-tree-semantics`
(see `planning/checkpoint-tree-remediation.md`, acceptance criteria AC1–AC7).

---

Thank you — your reading of the Lean code is exactly right: `justification_link`
(`Core/AtomicDef/Justification.lean`) does require the source and target to be separated by
*exactly* `t_h − s_h` parent links, and if `Hash` were a type of block roots with the slot-level
parent relation, that condition would not be Gasper's and a justification across an empty epoch
would not even be expressible.

The intended semantics — inherited from the Runtime Verification Coq development this repository
ports, whose `HashTree.v` states up front that *"a 'block' refers to a 'checkpoint block'
throughout"* — is that the tree is Gasper's **checkpoint tree**:

* a node is an epoch boundary pair `(B, j)` (eth2's `Checkpoint = (epoch, root)`), so the same
  block root can occur as several distinct nodes across empty epochs;
* one parent edge spans one attestation epoch: the parent of `(B, j+1)` is `(EBB(B, j), j)`;
* heights are attestation epochs, which coincide with tree depth because `(B, 0)` is genesis for
  every `B`.

Under that reading the graded condition `s →^{t_h − s_h} t` is equivalent to "the source
checkpoint lies on the target's checkpoint chain", which is Gasper's condition. Our Lean port
dropped the Coq note and even described the structure as a "block tree" — that is a real defect
on our side, and your reading was the natural one for the code as documented.

We have fixed this in three layers, without changing any existing definition or theorem
(the diff to existing files is docstrings and imports only; `lake build` re-verifies everything):

1. **Documentation.** The checkpoint-tree interpretation is now stated in `HashTree.lean`,
   `State.lean`, `Justification.lean` and the README ("Model interpretation: the checkpoint
   tree"), including the fact that irreflexivity is a property of checkpoint *nodes* and does
   not exclude repeated block roots.

2. **Machine-checked in the abstract model** (`Core/AtomicDef/Grading.lean`,
   `Core/Lemmas/Grading.lean`). With `height_graded parent genesis ht` (genesis at height 0,
   each parent edge adds 1):
   * `justification_link_iff_ancestor` — the graded condition of `justification_link` is
     equivalent to plain checkpoint ancestry `hash_ancestor parent s t` (plus the forward and
     supermajority conjuncts);
   * `justified_height_eq` — the height certified by any `justified` derivation equals the
     true depth, even though votes may carry arbitrary height fields;
   * `justified_depth` — even without the grading hypothesis, `justified st b h` implies that
     `b` is reached from genesis by exactly `h` parent edges.

3. **A concrete refinement layer** (`Core/Refinement/SlottedChain.lean`,
   `Core/Refinement/CheckpointTree.lean`). From slotted blocks (`SlottedChainContext`: parent
   map, slots decreasing along parent edges, genesis the unique root at slot 0) we define
   `ebb` (Gasper's epoch boundary block, with `ebb_slot_le`, `ebb_on_chain`,
   `on_chain_ebb_of_le`, `ebb_zero`, and the tower property `ebb_tower`), build
   `Checkpoint = ⟨block, epoch⟩` with `cp_parent (B, j+1) = (ebb B j, j)`, and prove:
   * `cp_context` — the checkpoint tree is a `HashTreeContext` (R1);
   * `cp_graded` — the epoch is a height grading (R2), so everything in layer 2 applies;
   * `cp_empty_epoch` — every valid `(B, j)` is the parent of `(B, j+1)`: empty epochs are
     representable (R3);
   * `cp_depth` — a valid `(B, j)` is reached from `(genesis, 0)` in exactly `j` steps (R4);
   * `cp_link_correspondence` / `cp_ancestor_iff_on_chain` — abstract ancestry in the
     checkpoint tree is exactly `block(s) = EBB(block(t), epoch(s))` with
     `epoch(s) ≤ epoch(t)` (R5);
   * `cp_justification_link_iff` — combining the above: on the concrete checkpoint tree a
     `justification_link` is a supermajority link whose source lies on the target's checkpoint
     chain, with strictly increasing epoch.

   `Executable/UseCases/EmptyEpoch.lean` runs the empty-epoch case: a three-block chain with
   `C = 2` where epoch 2 is empty, so `(B, 1)` and `(B, 2)` are consecutive checkpoints with the
   same block; with a ⅔-quorum voting `(B,1) → (B,2)`, `(B, 2)` is `justified` at height 2 —
   as a proof term over `cp_parent`, and by `decide` / `#eval` on a finite encoding.

We also document the deliberate deviations from the paper's raw Definition 4.6: our
justification links require checkpoint ancestry (matching per-chain justification from valid
attestations), so the justified pairs of the model form a subset of J(G); the beacon state
transition is not modelled; and vote height fields are unconstrained (an over-approximation of
the reachable states, harmless for safety and forced to be consistent along justification chains
by `justified_height_eq`).

The axiom audit (`make audit`) reports that the new declarations, like the rest of the
development, depend only on `propext` and `Quot.sound`; no `sorry`, no `Classical.choice`,
no native computation.
