import GasperBeaconChain.Executable.UseCases.SurroundFork
import GasperBeaconChain.Executable.UseCases.JustifiedFork
import GasperBeaconChain.Executable.UseCases.FinalizationK2

/-!
# Random-committee executable evaluation harness

The parametric use cases (`SurroundFork`, `JustifiedFork`, `FinalizationK2`) are proved for
**every** committee size `N`.  This harness draws a *random* `N ∈ [99, 255]` (the practical
committee range — `111` is the Gasper paper's heuristic, `255` the Eth2 max committee size),
instantiates the demonstration at that concrete `N`, runs the **compiled Boolean oracles**
(`slashedB`, `justifiedB`), and checks they match the values guaranteed by the proofs:

* the number of slashed validators equals `two_third N = N - N/3` (exactly the `qTT` voters);
* the intended checkpoints are justified (including via skip links), the unvoted ones are not.

Run with `lake env lean GasperBeaconChain/Executable/UseCases/RandomEval.lean` to see a fresh
random instantiation evaluated end to end.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

/-- `two_third N` for the canonical threshold, as a runtime value. -/
def twoThird (n : Nat) : Nat := n - n / 3

private def verdict (b : Bool) : String := if b then "✓ PASS" else "✗ FAIL"

/-- Evaluate the S2 surround fork at a concrete committee size and verify. -/
def evalSurround (n : Nat) : IO Unit := do
  IO.println s!"┌─ S2 surround fork   (committee N = {n},  two_third {n} = {twoThird n})"
  let slashed := ((List.finRange n).filter (fun v => slashedB (stFork n) v)).length
  IO.println s!"│   surround-slashed validators = {slashed}   expected = {twoThird n}   {verdict (slashed == twoThird n)}"
  let j1 := justifiedB τ (stake n) (vset n) parent genesis (stFork n) 1 1
  let j6 := justifiedB τ (stake n) (vset n) parent genesis (stFork n) 6 3
  let j3 := justifiedB τ (stake n) (vset n) parent genesis (stFork n) 3 3
  IO.println s!"│   block 1 @h1 justified = {j1} (exp true);  block 6 @h3 via SKIP link = {j6} (exp true);  block 3 @h3 = {j3} (exp false)"
  IO.println s!"└   {verdict (j1 && j6 && !j3)}"

/-- Evaluate the Lemma-4.11 same-height fork at a concrete committee size and verify. -/
def evalJustified (n : Nat) : IO Unit := do
  IO.println s!"┌─ Lemma 4.11 same-height fork   (committee N = {n})"
  let slashed := ((List.finRange n).filter (fun v => slashedB (stJust n) v)).length
  IO.println s!"│   S1 double-voters = {slashed}   expected two_third {n} = {twoThird n}   {verdict (slashed == twoThird n)}"
  let j1 := justifiedB τ (stake n) (vset n) parent genesis (stJust n) 1 1
  let j4 := justifiedB τ (stake n) (vset n) parent genesis (stJust n) 4 1
  IO.println s!"│   block 1 @h1 = {j1};  block 4 @h1 = {j4}   (both justified at the SAME height 1)"
  IO.println s!"└   {verdict (j1 && j4)}"

/-- Evaluate the k=2 finalization at a concrete committee size and verify. -/
def evalK2 (n : Nat) : IO Unit := do
  IO.println s!"┌─ k=2 finalization   (committee N = {n})"
  let j1 := justifiedB τ (stake n) (vset n) parent genesis (stK2 n) 1 1
  let j2 := justifiedB τ (stake n) (vset n) parent genesis (stK2 n) 2 2
  let j3 := justifiedB τ (stake n) (vset n) parent genesis (stK2 n) 3 3
  IO.println s!"│   chain justified: 1@h1 = {j1}, 2@h2 = {j2}, 3@h3 = {j3}   (k=2 finalizes block 1 via skip link 1⇒3)"
  IO.println s!"└   {verdict (j1 && j2 && j3)}"

/-- Draw a random committee size in `[99, 255]` and evaluate all three demonstrations. -/
def runRandom : IO Unit := do
  IO.println "════════ Gasper use cases — random committee evaluation ════════"
  let n1 ← IO.rand 99 255
  evalSurround n1
  let n2 ← IO.rand 99 255
  evalJustified n2
  let n3 ← IO.rand 99 255
  evalK2 n3
  IO.println "════════════════════════════════════════════════════════════════"

#eval runRandom

end GasperBeaconChain.Executable.UseCases.Parametric
