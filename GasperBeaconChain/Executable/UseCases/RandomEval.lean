import GasperBeaconChain.Executable.UseCases.SurroundFork
import GasperBeaconChain.Executable.UseCases.JustifiedFork
import GasperBeaconChain.Executable.UseCases.FinalizationK2


namespace GasperBeaconChain.Executable.UseCases.Parametric

open GasperBeaconChain.Core GasperBeaconChain.Executable GasperBeaconChain.Executable.UseCases

def twoThird (n : Nat) : Nat := n - n / 3

private def verdict (b : Bool) : String := if b then "✓ PASS" else "✗ FAIL"

def evalSurround (n : Nat) : IO Unit := do
  IO.println s!"┌─ S2 surround fork   (committee N = {n},  two_third {n} = {twoThird n})"
  let slashed := ((List.finRange n).filter (fun v => slashedB (stFork n) v)).length
  IO.println s!"│   surround-slashed validators = {slashed}   expected = {twoThird n}   {verdict (slashed == twoThird n)}"
  let j1 := justifiedB τ (stake n) (vset n) parent genesis (stFork n) 1 1
  let j6 := justifiedB τ (stake n) (vset n) parent genesis (stFork n) 6 3
  let j3 := justifiedB τ (stake n) (vset n) parent genesis (stFork n) 3 3
  IO.println s!"│   block 1 @h1 justified = {j1} (exp true);  block 6 @h3 via SKIP link = {j6} (exp true);  block 3 @h3 = {j3} (exp false)"
  IO.println s!"└   {verdict (j1 && j6 && !j3)}"

def evalJustified (n : Nat) : IO Unit := do
  IO.println s!"┌─ Lemma 4.11 same-height fork   (committee N = {n})"
  let slashed := ((List.finRange n).filter (fun v => slashedB (stJust n) v)).length
  IO.println s!"│   S1 double-voters = {slashed}   expected two_third {n} = {twoThird n}   {verdict (slashed == twoThird n)}"
  let j1 := justifiedB τ (stake n) (vset n) parent genesis (stJust n) 1 1
  let j4 := justifiedB τ (stake n) (vset n) parent genesis (stJust n) 4 1
  IO.println s!"│   block 1 @h1 = {j1};  block 4 @h1 = {j4}   (both justified at the SAME height 1)"
  IO.println s!"└   {verdict (j1 && j4)}"

def evalK2 (n : Nat) : IO Unit := do
  IO.println s!"┌─ k=2 finalization   (committee N = {n})"
  let j1 := justifiedB τ (stake n) (vset n) parent genesis (stK2 n) 1 1
  let j2 := justifiedB τ (stake n) (vset n) parent genesis (stK2 n) 2 2
  let j3 := justifiedB τ (stake n) (vset n) parent genesis (stK2 n) 3 3
  IO.println s!"│   chain justified: 1@h1 = {j1}, 2@h2 = {j2}, 3@h3 = {j3}   (k=2 finalizes block 1 via skip link 1⇒3)"
  IO.println s!"└   {verdict (j1 && j2 && j3)}"

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
