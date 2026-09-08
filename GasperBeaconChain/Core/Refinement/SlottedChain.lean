universe u

namespace GasperBeaconChain.Core

/-!
# Slotted block chains and epoch boundary blocks

This file is the first half of the concrete refinement layer. It
models the slot-level block structure of Gasper (§ 4.1 of the paper)
in the minimal form needed to *define* epoch boundary blocks, and
proves the properties of that definition which the checkpoint tree of
{lit}`CheckpointTree.lean` relies on.

## Blocks with slots

A {lit}`SlottedChainContext` consists of a type of blocks, a partial
parent function (every block except genesis has exactly one parent),
a slot number per block that strictly decreases along parent edges,
and the number of slots per epoch $`C`. Genesis is the unique root
and sits at slot $`0`.

## Epoch boundary blocks

Gasper defines, for a block $`B` and an epoch $`j`, the **epoch
boundary block** $`\operatorname{EBB}(B, j)` as the block of
$`\operatorname{chain}(B)` with the highest slot not exceeding
$`jC`. The function {lit}`ebb` computes it by walking up the chain
from $`B` until the slot bound is met. It is implemented by
fuel-based structural recursion (the fuel being the slot of the
starting block) so that it reduces inside the kernel and can be used
with {lit}`decide` in the executable layer.

The main facts proved here:

* {lit}`ebb_slot_le` — the result respects the slot bound;
* {lit}`ebb_on_chain` and {lit}`on_chain_ebb_of_le` — the result lies
  on $`\operatorname{chain}(B)` and every block of
  $`\operatorname{chain}(B)` within the bound lies below it, i.e. it
  is the *latest* such block, as in the paper;
* {lit}`ebb_self_iff` — $`\operatorname{EBB}(B, j) = B` exactly when
  $`B` itself is within the bound;
* {lit}`ebb_zero` — $`\operatorname{EBB}(B, 0)` is genesis for every
  $`B` (paper, § 4.1);
* {lit}`ebb_tower` — epoch boundary blocks are compatible under
  nesting: $`\operatorname{EBB}(\operatorname{EBB}(B, j_2), j_1) = \operatorname{EBB}(B, j_1)`
  whenever $`j_1 \le j_2`. This is the lemma that makes the
  checkpoint tree a tree graded by the epoch.

## Chain induction

Because slots strictly decrease along parent edges, a property that
propagates from parent to child holds everywhere
({lit}`chain_induction`). All results about {lit}`ebb` are proved by
this principle rather than by unfolding the fuel.

## Non-assumptions

Nothing is assumed about the existence of children, about the number
of blocks per slot, or about $`C > 0`; and the reachability of every
block from genesis, which one might expect as an axiom, is *derived*
({lit}`genesis_on_chain`) from the uniqueness of the root and the
decrease of slots.
-/

/--
A **slotted block chain** in the sense of Gasper § 4.1: blocks with a
parent map, slot numbers, a genesis block, and the epoch length $`C`
(slots per epoch).

# Data

* {lit}`bparent` — the parent map; {lit}`none` marks a root;
* {lit}`slot` — the slot of a block;
* {lit}`bgenesis` — the genesis block;
* {lit}`C` — slots per epoch (Gasper's $`C`).

# Laws

* {lit}`slot_genesis` — genesis is at slot $`0`;
* {lit}`slot_lt` — slots strictly decrease along parent edges;
* {lit}`root_unique` — genesis is the only root.

# Intended semantics

The parent map is a *function*, so "at most one parent" holds by
construction. Together, {lit}`slot_lt` and {lit}`root_unique` imply
that every block reaches genesis by finitely many parent steps
({lit}`genesis_on_chain`), which is why reachability is not a
separate field.

# Non-assumptions

$`C > 0` is not assumed (it is never used); no bound on the number
of blocks per slot, and no fork-choice rule, is imposed.
-/
structure SlottedChainContext (Block : Type u) where
  bparent : Block → Option Block
  slot : Block → Nat
  bgenesis : Block
  C : Nat
  slot_genesis : slot bgenesis = 0
  slot_lt : ∀ {b p : Block}, bparent b = some p → slot p < slot b
  root_unique : ∀ {b : Block}, bparent b = none → b = bgenesis

variable {Block : Type u}

/-!
## § 1 Chain membership and chain induction
-/

/--
**Chain membership.** $`x \in \operatorname{chain}(b)`: the block
$`x` is $`b` itself or is reached from $`b` by following parent
edges upward. Two constructors:

$$`\dfrac{\vphantom{X}}{b \in \operatorname{chain}(b)}\;\textsf{refl} \qquad\qquad \dfrac{x \in \operatorname{chain}(p) \qquad \operatorname{bparent}(b) = p}{x \in \operatorname{chain}(b)}\;\textsf{step}`

This is Gasper's $`\operatorname{chain}(B)`, the set of ancestors of
$`B` including $`B`.
-/
inductive on_chain (ctx : SlottedChainContext Block) : Block → Block → Prop
| refl (b : Block) :
    on_chain ctx b b
| step {x p b : Block} :
    on_chain ctx x p →
    ctx.bparent b = some p →
    on_chain ctx x b

/--
# Slot-bounded chain induction (auxiliary)

If a property holds at $`b` whenever it holds at the parent of $`b`,
then it holds at every block whose slot is at most $`n`. Induction on
$`n`; the slot of a parent is strictly smaller
({lit}`slot_lt`), so it fits the smaller bound.
-/
theorem chain_induction_aux
    (ctx : SlottedChainContext Block)
    {P : Block → Prop}
    (ih : ∀ b : Block, (∀ p : Block, ctx.bparent b = some p → P p) → P b) :
    ∀ (n : Nat) (b : Block), ctx.slot b ≤ n → P b
  | 0, b, hb =>
      ih b (fun _ hp =>
        absurd (Nat.lt_of_lt_of_le (ctx.slot_lt hp) hb) (Nat.not_lt_zero _))
  | n + 1, b, hb =>
      ih b (fun p hp =>
        chain_induction_aux ctx ih n p
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (ctx.slot_lt hp) hb)))

/--
# Chain induction

**Induction along parent edges.** A property that holds at a block
whenever it holds at the block's parent holds at every block:

$$`\bigl(\forall\, b,\; (\forall\, p,\; \operatorname{bparent}(b) = p \implies P(p)) \implies P(b)\bigr) \;\implies\; \forall\, b,\; P(b)`

Well-foundedness comes from the strictly decreasing slot
({lit}`slot_lt`), via {lit}`chain_induction_aux` at bound
$`\operatorname{slot}(b)`. Roots satisfy the premise vacuously.
-/
theorem chain_induction
    (ctx : SlottedChainContext Block)
    {P : Block → Prop}
    (ih : ∀ b : Block, (∀ p : Block, ctx.bparent b = some p → P p) → P b) :
    ∀ b : Block, P b :=
  fun b => chain_induction_aux ctx ih (ctx.slot b) b (Nat.le_refl _)

/--
# Genesis has no parent

Derived, not assumed: a parent of genesis would have slot
$`< 0`.
-/
theorem bparent_genesis
    (ctx : SlottedChainContext Block) :
    ctx.bparent ctx.bgenesis = none :=
  match hp : ctx.bparent ctx.bgenesis with
  | some _ =>
      absurd (ctx.slot_lt hp)
        (Eq.subst (motive := fun n => ¬ ctx.slot _ < n) ctx.slot_genesis.symm
          (Nat.not_lt_zero _))
  | none => rfl

/--
# A block at slot $`0` is genesis

A block with $`\operatorname{slot}(b) \le 0` has no parent (its
parent would have a smaller slot), so it is a root, hence genesis by
{lit}`root_unique`.
-/
theorem eq_genesis_of_slot_le_zero
    (ctx : SlottedChainContext Block)
    {b : Block}
    (h : ctx.slot b ≤ 0) :
    b = ctx.bgenesis :=
  match hp : ctx.bparent b with
  | some _ => absurd (Nat.lt_of_lt_of_le (ctx.slot_lt hp) h) (Nat.not_lt_zero _)
  | none => ctx.root_unique hp

/--
# Every block reaches genesis

$`\operatorname{genesis} \in \operatorname{chain}(b)` for every
$`b`. This is the reachability property one might have postulated;
here it follows by chain induction from {lit}`root_unique`.
-/
theorem genesis_on_chain
    (ctx : SlottedChainContext Block) :
    ∀ b : Block, on_chain ctx ctx.bgenesis b :=
  chain_induction ctx fun b ih =>
    match hp : ctx.bparent b with
    | some p => on_chain.step (ih p hp) hp
    | none =>
        Eq.subst (motive := fun x => on_chain ctx ctx.bgenesis x)
          (ctx.root_unique hp).symm
          (on_chain.refl ctx.bgenesis)

/--
# A block above a slot bound has a parent

If $`\operatorname{slot}(b) > m` then $`b` is not genesis (whose slot
is $`0`), hence not a root, hence has a parent.
-/
theorem exists_parent_of_not_le
    (ctx : SlottedChainContext Block)
    {b : Block} {m : Nat}
    (h : ¬ ctx.slot b ≤ m) :
    ∃ p : Block, ctx.bparent b = some p :=
  match hp : ctx.bparent b with
  | some p => ⟨p, rfl⟩
  | none =>
      absurd
        (show ctx.slot b ≤ m from by
          rw [ctx.root_unique hp, ctx.slot_genesis]
          exact Nat.zero_le m)
        h

/-!
## § 2 Epoch boundary blocks
-/

/--
Fuel-based worker for {lit}`ebb`. With fuel $`n + 1` it returns $`b`
if $`\operatorname{slot}(b) \le jC`, and otherwise recurses into the
parent with fuel $`n`; with fuel $`0` it returns $`b`. When the fuel
is at least $`\operatorname{slot}(b)` the fuel never runs out before
the bound is met ({lit}`ebbAux_fuel_irrel`), which is why {lit}`ebb`
uses $`\operatorname{slot}(b)` as fuel. The {lit}`none` branch is
unreachable under the context laws (a root has slot $`0 \le jC`).
-/
def ebbAux (ctx : SlottedChainContext Block) (j : Nat) : Nat → Block → Block
  | 0, b => b
  | n + 1, b =>
      if ctx.slot b ≤ j * ctx.C then b
      else
        match ctx.bparent b with
        | some p => ebbAux ctx j n p
        | none => b

/--
**Epoch boundary block** (Gasper § 4.1): $`\operatorname{EBB}(B, j)`
is the block of $`\operatorname{chain}(B)` with the highest slot not
exceeding $`jC`,

$$`\operatorname{EBB}(B, j) \;\;=\;\; \text{the latest } B' \in \operatorname{chain}(B) \text{ with } \operatorname{slot}(B') \le jC .`

Computed by walking up from $`B` ({lit}`ebbAux` with fuel
$`\operatorname{slot}(B)`). The characterizing properties are
{lit}`ebb_slot_le` (within the bound), {lit}`ebb_on_chain` (on the
chain) and {lit}`on_chain_ebb_of_le` (latest such block).

The definition is by structural recursion on the fuel, so it is
kernel-reducible: concrete checkpoint trees can be explored with
{lit}`decide` and {lit}`#eval` (see
{lit}`Executable/UseCases/EmptyEpoch.lean`).
-/
def ebb (ctx : SlottedChainContext Block) (b : Block) (j : Nat) : Block :=
  ebbAux ctx j (ctx.slot b) b

/--
# Within the bound, the worker returns its input

If $`\operatorname{slot}(b) \le jC` then {lit}`ebbAux` returns $`b`
for every fuel.
-/
theorem ebbAux_of_le
    (ctx : SlottedChainContext Block)
    {j : Nat} {b : Block}
    (h : ctx.slot b ≤ j * ctx.C) :
    ∀ n : Nat, ebbAux ctx j n b = b
  | 0 => rfl
  | _ + 1 => by simp [ebbAux, h]

/--
# Above the bound, the worker steps to the parent

If $`\operatorname{slot}(b) > jC` and $`\operatorname{bparent}(b) = p`,
then {lit}`ebbAux` with fuel $`n + 1` at $`b` equals {lit}`ebbAux`
with fuel $`n` at $`p`.
-/
theorem ebbAux_succ_of_gt
    (ctx : SlottedChainContext Block)
    {j n : Nat} {b p : Block}
    (h : ¬ ctx.slot b ≤ j * ctx.C)
    (hp : ctx.bparent b = some p) :
    ebbAux ctx j (n + 1) b = ebbAux ctx j n p := by
  simp [ebbAux, h, hp]

/--
# The result does not depend on the fuel, once the fuel suffices

For any two fuels $`n, m \ge \operatorname{slot}(b)` the worker gives
the same result. Induction on $`n`, generalizing $`b` and $`m`; the
slot strictly decreases at each step so the bound is maintained.
-/
theorem ebbAux_fuel_irrel
    (ctx : SlottedChainContext Block)
    {j : Nat} :
    ∀ {n m : Nat} {b : Block},
      ctx.slot b ≤ n → ctx.slot b ≤ m → ebbAux ctx j n b = ebbAux ctx j m b
  | 0, m, b, hn, _ =>
      have h : ctx.slot b ≤ j * ctx.C := Nat.le_trans hn (Nat.zero_le _)
      (ebbAux_of_le ctx h 0).trans (ebbAux_of_le ctx h m).symm
  | n + 1, m, b, hn, hm =>
      if h : ctx.slot b ≤ j * ctx.C then
        (ebbAux_of_le ctx h (n + 1)).trans (ebbAux_of_le ctx h m).symm
      else
        match exists_parent_of_not_le ctx h with
        | ⟨p, hp⟩ =>
          match m, hm with
          | 0, hm =>
              absurd (Nat.le_trans hm (Nat.zero_le _)) h
          | m' + 1, hm =>
              have hpn : ctx.slot p ≤ n :=
                Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (ctx.slot_lt hp) hn)
              have hpm : ctx.slot p ≤ m' :=
                Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (ctx.slot_lt hp) hm)
              (ebbAux_succ_of_gt ctx h hp).trans
                ((ebbAux_fuel_irrel ctx hpn hpm).trans
                  (ebbAux_succ_of_gt ctx h hp).symm)

/--
# {lit}`ebb` equals the worker at any sufficient fuel
-/
theorem ebb_eq_ebbAux
    (ctx : SlottedChainContext Block)
    {j n : Nat} {b : Block}
    (hn : ctx.slot b ≤ n) :
    ebb ctx b j = ebbAux ctx j n b :=
  ebbAux_fuel_irrel ctx (Nat.le_refl _) hn

/--
# Within the bound, the epoch boundary block is the block itself

$$`\operatorname{slot}(b) \le jC \;\implies\; \operatorname{EBB}(b, j) = b`
-/
theorem ebb_of_le
    (ctx : SlottedChainContext Block)
    {j : Nat} {b : Block}
    (h : ctx.slot b ≤ j * ctx.C) :
    ebb ctx b j = b :=
  ebbAux_of_le ctx h _

/--
# Above the bound, the epoch boundary block is that of the parent

$$`\operatorname{slot}(b) > jC \;\wedge\; \operatorname{bparent}(b) = p \;\implies\; \operatorname{EBB}(b, j) = \operatorname{EBB}(p, j)`

The fuel is raised to $`\operatorname{slot}(b) + 1` to expose one
recursion step, then lowered again to $`\operatorname{slot}(p)`
({lit}`ebbAux_fuel_irrel`).
-/
theorem ebb_of_gt
    (ctx : SlottedChainContext Block)
    {j : Nat} {b p : Block}
    (h : ¬ ctx.slot b ≤ j * ctx.C)
    (hp : ctx.bparent b = some p) :
    ebb ctx b j = ebb ctx p j :=
  (ebb_eq_ebbAux ctx (Nat.le_succ _)).trans
    ((ebbAux_succ_of_gt ctx h hp).trans
      (ebbAux_fuel_irrel ctx (Nat.le_of_lt (ctx.slot_lt hp)) (Nat.le_refl _)))

/--
# The epoch boundary block respects the slot bound

$$`\operatorname{slot}(\operatorname{EBB}(b, j)) \le jC`

Chain induction: within the bound the result is $`b`; above it the
result is the parent's, which satisfies the bound inductively. A root
above the bound is impossible ({lit}`exists_parent_of_not_le`).
-/
theorem ebb_slot_le
    (ctx : SlottedChainContext Block)
    (j : Nat) :
    ∀ b : Block, ctx.slot (ebb ctx b j) ≤ j * ctx.C :=
  chain_induction ctx fun b ih =>
    if h : ctx.slot b ≤ j * ctx.C then
      Eq.subst (motive := fun x => ctx.slot x ≤ j * ctx.C) (ebb_of_le ctx h).symm h
    else
      match exists_parent_of_not_le ctx h with
      | ⟨p, hp⟩ =>
          Eq.subst (motive := fun x => ctx.slot x ≤ j * ctx.C)
            (ebb_of_gt ctx h hp).symm (ih p hp)

/--
# The epoch boundary block lies on the chain

$$`\operatorname{EBB}(b, j) \in \operatorname{chain}(b)`
-/
theorem ebb_on_chain
    (ctx : SlottedChainContext Block)
    (j : Nat) :
    ∀ b : Block, on_chain ctx (ebb ctx b j) b :=
  chain_induction ctx fun b ih =>
    if h : ctx.slot b ≤ j * ctx.C then
      Eq.subst (motive := fun x => on_chain ctx x b) (ebb_of_le ctx h).symm
        (on_chain.refl b)
    else
      match exists_parent_of_not_le ctx h with
      | ⟨p, hp⟩ =>
          Eq.subst (motive := fun x => on_chain ctx x b) (ebb_of_gt ctx h hp).symm
            (on_chain.step (ih p hp) hp)

/--
# The epoch boundary block is the latest block within the bound

Every block of $`\operatorname{chain}(b)` whose slot is within the
bound lies on the chain of $`\operatorname{EBB}(b, j)`:

$$`x \in \operatorname{chain}(b) \;\wedge\; \operatorname{slot}(x) \le jC \;\implies\; x \in \operatorname{chain}(\operatorname{EBB}(b, j))`

Together with {lit}`ebb_on_chain` and {lit}`ebb_slot_le` this
identifies {lit}`ebb` with Gasper's "block with the highest slot
$`\le jC` on $`\operatorname{chain}(B)`". Chain induction on $`b`;
when $`b` is above the bound, $`x \ne b`, so $`x` lies on the
parent's chain.
-/
theorem on_chain_ebb_of_le
    (ctx : SlottedChainContext Block)
    (j : Nat) :
    ∀ b x : Block, on_chain ctx x b → ctx.slot x ≤ j * ctx.C →
      on_chain ctx x (ebb ctx b j) :=
  chain_induction ctx fun b ih x hx hxs =>
    if h : ctx.slot b ≤ j * ctx.C then
      Eq.subst (motive := fun y => on_chain ctx x y) (ebb_of_le ctx h).symm hx
    else
      match hx with
      | .refl _ => absurd hxs h
      | .step hx' hp =>
          Eq.subst (motive := fun y => on_chain ctx x y) (ebb_of_gt ctx h hp).symm
            (ih _ hp x hx' hxs)

/--
# $`\operatorname{EBB}(b, j) = b` iff $`b` is within the bound

$$`\operatorname{EBB}(b, j) = b \;\iff\; \operatorname{slot}(b) \le jC`

The forward direction transports {lit}`ebb_slot_le` along the
equation; the reverse is {lit}`ebb_of_le`.
-/
theorem ebb_self_iff
    (ctx : SlottedChainContext Block)
    {j : Nat} {b : Block} :
    ebb ctx b j = b ↔ ctx.slot b ≤ j * ctx.C :=
  ⟨fun h =>
    Eq.subst (motive := fun x => ctx.slot x ≤ j * ctx.C) h (ebb_slot_le ctx j b),
   fun h => ebb_of_le ctx h⟩

/--
# The epoch-$`0` boundary block is genesis

$$`\operatorname{EBB}(b, 0) = \operatorname{genesis}`

for every $`b` (Gasper § 4.1). The result has slot
$`\le 0 \cdot C = 0`, hence is genesis by
{lit}`eq_genesis_of_slot_le_zero`.
-/
theorem ebb_zero
    (ctx : SlottedChainContext Block)
    (b : Block) :
    ebb ctx b 0 = ctx.bgenesis :=
  eq_genesis_of_slot_le_zero ctx
    (Eq.subst (motive := fun n => ctx.slot (ebb ctx b 0) ≤ n) (Nat.zero_mul ctx.C)
      (ebb_slot_le ctx 0 b))

/--
# Tower property of epoch boundary blocks

**Nested epoch boundary blocks collapse**: for $`j_1 \le j_2`,

$$`\operatorname{EBB}(\operatorname{EBB}(b, j_2),\, j_1) \;=\; \operatorname{EBB}(b, j_1) .`

# Proof idea

Chain induction on $`b`. If $`\operatorname{slot}(b) \le j_2 C`, then
$`\operatorname{EBB}(b, j_2) = b` and both sides agree. Otherwise
$`\operatorname{slot}(b) > j_2 C \ge j_1 C`, so both
$`\operatorname{EBB}(b, j_2)` and $`\operatorname{EBB}(b, j_1)` step to
the parent $`p` ({lit}`ebb_of_gt`), and the induction hypothesis at
$`p` closes the goal.

# Role

This is the lemma that makes the checkpoint tree
({lit}`CheckpointTree.lean`) graded by the epoch: the parent of
$`(B, j+1)` is $`(\operatorname{EBB}(B, j), j)`, and walking $`k`
parent edges from $`(B, j)` lands on $`(\operatorname{EBB}(B, j-k), j-k)`
precisely because of this property
({lit}`cp_link_correspondence`).
-/
theorem ebb_tower
    (ctx : SlottedChainContext Block)
    {j₁ j₂ : Nat}
    (hj : j₁ ≤ j₂) :
    ∀ b : Block, ebb ctx (ebb ctx b j₂) j₁ = ebb ctx b j₁ :=
  chain_induction ctx fun b ih =>
    if h₂ : ctx.slot b ≤ j₂ * ctx.C then
      congrArg (fun x => ebb ctx x j₁) (ebb_of_le ctx h₂)
    else
      have h₁ : ¬ ctx.slot b ≤ j₁ * ctx.C :=
        fun h => h₂ (Nat.le_trans h (Nat.mul_le_mul_right ctx.C hj))
      match exists_parent_of_not_le ctx h₂ with
      | ⟨p, hp⟩ =>
          (congrArg (fun x => ebb ctx x j₁) (ebb_of_gt ctx h₂ hp)).trans
            ((ih p hp).trans (ebb_of_gt ctx h₁ hp).symm)

/--
# Idempotence of the epoch boundary block

$$`\operatorname{EBB}(\operatorname{EBB}(b, j),\, j) = \operatorname{EBB}(b, j)`

The $`j_1 = j_2` instance of {lit}`ebb_tower`.
-/
theorem ebb_idem
    (ctx : SlottedChainContext Block)
    (b : Block) (j : Nat) :
    ebb ctx (ebb ctx b j) j = ebb ctx b j :=
  ebb_tower ctx (Nat.le_refl j) b

end GasperBeaconChain.Core
