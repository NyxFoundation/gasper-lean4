import GasperBeaconChain.Executable.UseCases.Model

/-!
# Use case 1 — the slashing-detection oracle (watchtower)

**Scenario.** A *watchtower* observes the global vote set `st` and must, for every
validator `v`, decide whether `v` has produced cryptographic evidence of a
protocol violation — a **double vote** (slashing condition I: two votes with the
*same target height* but *different targets*) or a **surround vote** (condition
II: one vote's height interval `[s_h, t_h]` *strictly nests* inside another's).
Such a `v` is *slashable*; the watchtower submits the two offending votes as
evidence.

`Executable.slashedB st v` is precisely this oracle. It scans the **finite** state
`st` (no block enumeration, no `[Fintype Hash]`), and by `slashedB_iff` its `Bool`
verdict is **sound and complete** for `Core.slashed`. Below we:

1. **compute** the verdict (`#eval`) — the operational oracle;
2. **exhibit the explicit logical witness** for each offender — the essential
   content: *which* two votes, and *why* they violate condition I / II;
3. prove **completeness** — honest validators are provably *not* slashable;
4. transport between computation and logic via the reflect bridge.

Everything is kernel-checked (`by decide`, never `native_decide`) and
`Classical.choice`-free.
-/

namespace GasperBeaconChain.Executable.UseCases

open GasperBeaconChain.Core GasperBeaconChain.Executable

/-- The observed vote set.

| validator | votes (validator, source, target, sourceHeight, targetHeight) | fault |
|:--|:--|:--|
| `0` | `(0,1,5)` and `(0,4,5)` | double vote: targets `1 ≠ 4` at height `5` |
| `1` | `(0,3,0,10)` and `(1,2,2,5)` | surround: `[0,10]` strictly nests `[2,5]` |
| `2` | `(0,1,0,1)` | honest |
| `3` | `(0,1,0,1)` | honest | -/
def stSlashing : State V H :=
  { { validator := 0, source := 0, target := 1, sourceHeight := 0, targetHeight := 5 },
    { validator := 0, source := 0, target := 4, sourceHeight := 0, targetHeight := 5 },
    { validator := 1, source := 0, target := 3, sourceHeight := 0, targetHeight := 10 },
    { validator := 1, source := 1, target := 2, sourceHeight := 2, targetHeight := 5 },
    { validator := 2, source := 0, target := 1, sourceHeight := 0, targetHeight := 1 },
    { validator := 3, source := 0, target := 1, sourceHeight := 0, targetHeight := 1 } }


/-! ### 1. The operational oracle (`#eval`) -/

#eval slashedB stSlashing 0   -- true   (double vote)
#eval slashedB stSlashing 1   -- true   (surround vote)
#eval slashedB stSlashing 2   -- false  (honest)
#eval slashedB stSlashing 3   -- false  (honest)

-- The watchtower's actual output: the set of validators it can slash.
#eval (List.finRange 99).filter (fun v => slashedB stSlashing v)   -- [0, 1]


/-! ### 2. Explicit logical witnesses (the essential content)

We do not merely assert `slashedB … = true`; we *construct* the slashing-condition
witness, exhibiting the exact offending votes and the inequality that makes them a
fault. These terms are the evidence a watchtower would actually submit on-chain. -/

/-- Validator `0` double-voted: targets `1 ≠ 4` at the common target height `5`,
with the two concrete votes present in `st`. -/
theorem v0_double_vote : slashed_double_vote stSlashing 0 :=
  ⟨1, 4,            -- the two conflicting targets t₁ ≠ t₂
   by decide,        -- 1 ≠ 4 in `Fin 6`
   0, 0, 0, 0, 5,    -- sources `0,0`, source-heights `0,0`, common target height `5`
   by decide,        -- vote (0; 0→1 @ 0→5) ∈ st
   by decide⟩        -- vote (0; 0→4 @ 0→5) ∈ st

/-- Validator `1` surround-voted: the outer vote spans `[0,10]`, the inner vote
spans `[2,5]`, and `0 < 2 ∧ 5 < 10` (a strict interval nesting). -/
theorem v1_surround_vote : slashed_surround_vote stSlashing 1 :=
  ⟨0, 3, 0, 10,      -- outer vote: source 0, target 3, interval [s₁_h=0, t₁_h=10]
   1, 2, 2, 5,       -- inner vote: source 1, target 2, interval [s₂_h=2, t₂_h=5]
   by decide,        -- outer vote ∈ st
   by decide,        -- inner vote ∈ st
   by decide,        -- s₁_h < s₂_h : 0 < 2
   by decide⟩        -- t₂_h < t₁_h : 5 < 10

/-- Hence both validators are `Core.slashed` (the `Prop`, not just the `Bool`). -/
theorem v0_slashed : slashed stSlashing 0 := Or.inl v0_double_vote
theorem v1_slashed : slashed stSlashing 1 := Or.inr v1_surround_vote


/-! ### 3. Completeness — honest validators are provably NOT slashable

Soundness alone (`slashedB = true → slashed`) is not enough for a fair protocol:
we also need that an honest validator is **never** falsely accused. Here the
reflect bridge gives completeness for free — `slashedB v = false` transports to
`¬ slashed v`. -/

/-- Validator `2` cannot be slashed: no double vote, no surround vote. -/
theorem v2_not_slashed : ¬ slashed stSlashing 2 :=
  fun h => absurd ((slashedB_iff stSlashing 2).mpr h) (by decide)

/-- Validator `3` likewise. -/
theorem v3_not_slashed : ¬ slashed stSlashing 3 :=
  fun h => absurd ((slashedB_iff stSlashing 3).mpr h) (by decide)


/-! ### 4. Computation ↔ logic (the reflect bridge in both directions) -/

/-- Soundness: the computed `true` is genuine `Core.slashed` evidence. -/
example : slashed stSlashing 0 := (slashedB_iff stSlashing 0).mp (by decide)

/-- The watchtower's slashed set, *as a logical statement*: across the **entire**
99-validator committee, `v` is slashable **iff** `v ∈ {0, 1}`. Soundness and
completeness at once, kernel-checked over the finite validator type (no
`native_decide`). This is the migration of the old four-case characterization to
committee scale — strengthened, not dropped. -/
theorem slashed_set_characterization :
    ∀ v : V, slashed stSlashing v ↔ (v = 0 ∨ v = 1) := by decide

end GasperBeaconChain.Executable.UseCases
