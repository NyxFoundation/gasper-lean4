import GasperBeaconChain.Executable.UseCases.SurroundFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — the causal structure of accountable safety (Thm 3.2 / Buterin–Griffith Thm 1)

The theorem `accountable_safety` is the keystone of Casper FFG.  Its *proof* is a short
causal chain, and this panel renders that chain as a vertical flow, with the **live data**
of the real fork state `SurroundFork.stFork` (committee `N = vizN`) at each step:

```text
  ① a finalization fork              finalized(1,h1) ∧ finalized(6,h3),  1 ⋬ 6 ∧ 6 ⋬ 1
            │
  ② two 2/3 quorums                  the supporters of the two finalizing links,
            │                          |qL|, |qR| ≥ two_third N
            ▼
  ③ pigeonhole                       |qL ∩ qR| ≥ N − ⌊N/3⌋ − ⌊N/3⌋   (quorum_intersection_weight_lower)
            │
  ④ slashing                         every v ∈ qL ∩ qR committed S2  ⇒  slashed
            ▼
  ⑤ q_intersection_slashed           ∎  (accountable_safety)
```

Steps ①, ④ carry the **computed verdicts** (`justifiedB`, `slashedB`) of `stFork`; step ③
carries the arithmetic pigeonhole value `N − 2⌊N/3⌋` from the real threshold `τ`.  The
diagram is therefore a faithful trace of *why* a fork is impossible without ≥ N/3 slashed
stake.  Put the cursor on `#html` to view.
-/

namespace GasperBeaconChain.Visualizations.AccountableSafetyFlow

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

private def just1 : Bool := justifiedB τ (stake vizN) (vset vizN) parent genesis (stFork vizN) 1 1
private def just6 : Bool := justifiedB τ (stake vizN) (vset vizN) parent genesis (stFork vizN) 6 3
private def slashedN : Nat := ((List.finRange vizN).filter (fun v => slashedB (stFork vizN) v)).length
private def twoThird : Nat := τ.two_third vizN
private def pigeon : Nat := vizN - τ.one_third vizN - τ.one_third vizN

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 700; width := 700; height := 500

/-- The `i`-th stage box (top `y`), with a heading and a live-data subtitle. -/
private def stageBox (i : Nat) (col : Float × Float × Float)
    (heading sub : String) : List (Svg.Element frame) :=
  let y := 46.0 + 86.0 * Float.ofNat i
  [ rect (60.0, y) (.abs 580.0) (.abs 58.0)
      |>.setFill col |>.setStroke (70., 70., 70.) (.px 2),
    text (74.0, y + 24.0) heading (.px 15) |>.setFill (0.08, 0.08, 0.08),
    text (74.0, y + 45.0) sub (.px 12) |>.setFill (0.32, 0.32, 0.32) ]

/-- A downward arrow between stage `i` and stage `i+1`. -/
private def arrow (i : Nat) : List (Svg.Element frame) :=
  let y := 46.0 + 86.0 * Float.ofNat i + 58.0
  [ line (350.0, y) (350.0, y + 24.0) |>.setStroke (70., 70., 70.) (.px 2),
    text (343.0, y + 26.0) "▼" (.px 16) |>.setFill (0.35, 0.35, 0.35) ]

private def safetySvg : Svg frame :=
  { elements :=
      #[ text (40.0, 30.0) "accountable safety — why a fork costs ≥ N/3 slashable stake"
           (.px 16) |>.setFill (0.2, 0.2, 0.2) ]
      ++ (stageBox 0 (0.95, 0.86, 0.86)
            "① finalization fork:  finalized(1,h1)  ∧  finalized(6,h3),  conflicting"
            ("live:  justified(1,1) = " ++ toString just1
              ++ ",   justified(6,3) via skip-link = " ++ toString just6)).toArray
      ++ (arrow 0).toArray
      ++ (stageBox 1 (0.86, 0.90, 0.96)
            "② the two finalizing links each have a 2/3-quorum of supporters  qL, qR"
            ("|qL|, |qR|  ≥  two_third N  =  " ++ toString twoThird)).toArray
      ++ (arrow 1).toArray
      ++ (stageBox 2 (0.88, 0.93, 0.88)
            "③ pigeonhole  (quorum_intersection_weight_lower)"
            ("|qL ∩ qR|  ≥  N − ⌊N/3⌋ − ⌊N/3⌋  =  " ++ toString pigeon
              ++ "   (= one_third N, the safety margin)")).toArray
      ++ (arrow 2).toArray
      ++ (stageBox 3 (0.96, 0.84, 0.84)
            "④ every v ∈ qL ∩ qR committed S2 (surround)  ⇒  slashed"
            ("live:  slashedB count on stFork  =  " ++ toString slashedN
              ++ "   (the whole qTT quorum)")).toArray
      ++ (arrow 3).toArray
      ++ (stageBox 4 (0.80, 0.86, 0.95)
            "⑤  ∴  q_intersection_slashed        (Core theorem  accountable_safety)   ∎"
            "the fork is impossible unless validators of weight ≥ N/3 are provably slashable").toArray }

#html safetySvg.toHtml

end GasperBeaconChain.Visualizations.AccountableSafetyFlow
