import GasperBeaconChain.Executable.UseCases.SurroundFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — the S2 surround-vote *processing flow* and its actual behavior

This is a **behavioral** picture of the protocol running on the real fork state
`SurroundFork.stFork`: it traces the justification → finalization → fork → slashing flow and
colours every checkpoint by the **actual oracle verdict**, not by hand.

```text
        depth:  h0      h1      h2      h3      h4
   left  chain:  0 ──▶── 1 ──▶── 2 ──▶── 3
                  ╲                         (supermajority links ▶ = the justification flow)
   right chain:    ╲──── 4 ───── 5 ───── 6 ───── 7
                    ╰─────────────skip 0⇒6────────╯   (one link spanning 3 heights)
```

* node fill — `justifiedB`/finalization **evaluated on `stFork`**: deep blue = finalized,
  light blue = justified, grey = neither (the actual reachability of the protocol);
* green arrows — the left finalizing supermajority links `0⇒1`, `1⇒2` (inner interval `[1,2]`);
* red arc — the right **skip** supermajority link `0⇒6` (outer interval `[0,3]`), which
  *strictly surrounds* the green interval — the S2 violation;
* the bottom strip is the **processing pipeline**, ending in the live count of `slashedB`
  voters: the surround-vote is detected and the `qTT` quorum is slashed.

So the diagram is a faithful trace of the protocol's behavior on this state.  Put the cursor
on the `#html` line to view.
-/

namespace GasperBeaconChain.Visualizations.SurroundFlow

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

/-- Committee size for evaluating the oracles (the justification structure is `N`-independent). -/
private def vizN : Nat := 9

/-- Computable shadow of `ModelN.parent`: the tree's parent function. -/
private def parentFnOpt (b : Fin 8) : Option (Fin 8) :=
  match b.val with
  | 1 => some 0 | 2 => some 1 | 3 => some 2
  | 4 => some 0 | 5 => some 4 | 6 => some 5 | 7 => some 6
  | _ => none

/-- Tree height (distance from genesis). -/
private def heightFn (b : Fin 8) : Nat :=
  match b.val with
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | _ => 0

/-- Is `b` justified **on the real state `stFork`**? (the actual oracle). -/
private def isJust (b : Fin 8) : Bool :=
  justifiedB τ (stake vizN) (vset vizN) parent genesis (stFork vizN) b (heightFn b)

/-- Is `b` finalized: justified, with a tree-child justified one height higher. -/
private def isFinal (b : Fin 8) : Bool :=
  isJust b && (List.finRange 8).any (fun c =>
    (parentFnOpt c == some b) &&
    justifiedB τ (stake vizN) (vset vizN) parent genesis (stFork vizN) c (heightFn b + 1))

/-- Live count of validators slashed (surround-vote) on `stFork`. -/
private def slashedCount : Nat :=
  ((List.finRange vizN).filter (fun v => slashedB (stFork vizN) v)).length

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 660; width := 660; height := 470

private def posX (b : Fin 8) : Float :=
  if b.val == 0 then 90.0 else 90.0 + 130.0 * Float.ofNat (heightFn b)
private def posY (b : Fin 8) : Float :=
  if b.val == 0 then 165.0 else if b.val ≤ 3 then 90.0 else 250.0

/-- A checkpoint node, coloured by its computed justification/finalization status. -/
private def mkNode (b : Fin 8) : List (Svg.Element frame) :=
  let fill : Float × Float × Float :=
    if isFinal b then (0.16, 0.42, 0.93)
    else if isJust b then (0.62, 0.80, 0.98)
    else (0.87, 0.87, 0.87)
  [ circle (posX b, posY b) (.px 22) |>.setFill fill |>.setStroke (50., 50., 50.) (.px 2),
    text (posX b - 6.0, posY b + 6.0) (toString b.val) (.px 20) |>.setFill (0.04, 0.04, 0.04) ]

/-- A grey parent edge (tree structure). -/
private def mkEdge (b : Fin 8) : List (Svg.Element frame) :=
  match parentFnOpt b with
  | none => []
  | some p => [ line (posX p, posY p) (posX b, posY b) |>.setStroke (175., 175., 175.) (.px 2) ]

/-- A labelled stage box of the processing pipeline. -/
private def stage (x : Float) (label : String) (c : Float × Float × Float) :
    List (Svg.Element frame) :=
  [ rect (x, 405.0) (.abs 116.0) (.abs 34.0) |>.setFill c |>.setStroke (90., 90., 90.) (.px 1),
    text (x + 8.0, 426.0) label (.px 12) |>.setFill (0.1, 0.1, 0.1) ]

private def surroundFlowSvg : Svg frame :=
  { elements :=
      (((List.finRange 8).flatMap mkEdge)
        ++ [ -- the justification FLOW: left finalizing links (green) and the right skip (red)
             line (posX 0, posY 0) (posX 1, posY 1) |>.setStroke (40., 165., 80.) (.px 4),
             line (posX 1, posY 1) (posX 2, posY 2) |>.setStroke (40., 165., 80.) (.px 4),
             path "M105,150 C300,300 470,300 470,272" |>.setStroke (215., 45., 45.) (.px 4) ]
        ++ ((List.finRange 8).flatMap mkNode)).toArray
      ++ #[ text (300.0, 70.0) "skip 0⇒6  (outer [0,3])" (.px 14) |>.setFill (0.80, 0.18, 0.18),
            text (150.0, 130.0) "fin 1⇒2  (inner [1,2])" (.px 13) |>.setFill (0.16, 0.55, 0.30),
            text (40.0, 30.0) "S2 surround-vote: outer link strictly surrounds the finalized inner interval"
              (.px 14) |>.setFill (0.2, 0.2, 0.2),
            text (40.0, 388.0) "processing flow:" (.px 13) |>.setFill (0.3, 0.3, 0.3) ]
      ++ (stage 150.0 "votes (qTT)" (0.92, 0.92, 0.80)).toArray
      ++ (stage 276.0 "≥2/3 link" (0.80, 0.90, 0.95)).toArray
      ++ (stage 402.0 "justified" (0.62, 0.80, 0.98)).toArray
      ++ (stage 528.0 ("slashed = " ++ toString slashedCount) (0.96, 0.62, 0.62)).toArray
      ++ #[ line (266.0, 422.0) (276.0, 422.0) |>.setStroke (90., 90., 90.) (.px 2),
            line (392.0, 422.0) (402.0, 422.0) |>.setStroke (90., 90., 90.) (.px 2),
            line (518.0, 422.0) (528.0, 422.0) |>.setStroke (90., 90., 90.) (.px 2) ] }

#html surroundFlowSvg.toHtml

end GasperBeaconChain.Visualizations.SurroundFlow
