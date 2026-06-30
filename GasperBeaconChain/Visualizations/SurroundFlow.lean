import GasperBeaconChain.Executable.UseCases.SurroundFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Visualizations.SurroundFlow

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

private def parentFnOpt (b : Fin 8) : Option (Fin 8) :=
  match b.val with
  | 1 => some 0 | 2 => some 1 | 3 => some 2
  | 4 => some 0 | 5 => some 4 | 6 => some 5 | 7 => some 6
  | _ => none

private def heightFn (b : Fin 8) : Nat :=
  match b.val with
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | _ => 0

private def isJust (b : Fin 8) : Bool :=
  justifiedB τ (stake vizN) (vset vizN) parent genesis (stFork vizN) b (heightFn b)

private def isFinal (b : Fin 8) : Bool :=
  isJust b && (List.finRange 8).any (fun c =>
    (parentFnOpt c == some b) &&
    justifiedB τ (stake vizN) (vset vizN) parent genesis (stFork vizN) c (heightFn b + 1))

private def slashedCount : Nat :=
  ((List.finRange vizN).filter (fun v => slashedB (stFork vizN) v)).length

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 660; width := 660; height := 470

private def posX (b : Fin 8) : Float :=
  if b.val == 0 then 90.0 else 90.0 + 130.0 * Float.ofNat (heightFn b)
private def posY (b : Fin 8) : Float :=
  if b.val == 0 then 165.0 else if b.val ≤ 3 then 90.0 else 250.0

private def mkNode (b : Fin 8) : List (Svg.Element frame) :=
  let fill : Float × Float × Float :=
    if isFinal b then (0.16, 0.42, 0.93)
    else if isJust b then (0.62, 0.80, 0.98)
    else (0.87, 0.87, 0.87)
  [ circle (posX b, posY b) (.px 22) |>.setFill fill |>.setStroke (50., 50., 50.) (.px 2),
    text (posX b - 6.0, posY b + 6.0) (toString b.val) (.px 20) |>.setFill (0.04, 0.04, 0.04) ]

private def mkEdge (b : Fin 8) : List (Svg.Element frame) :=
  match parentFnOpt b with
  | none => []
  | some p => [ line (posX p, posY p) (posX b, posY b) |>.setStroke (175., 175., 175.) (.px 2) ]

private def stage (x : Float) (label : String) (c : Float × Float × Float) :
    List (Svg.Element frame) :=
  [ rect (x, 405.0) (.abs 116.0) (.abs 34.0) |>.setFill c |>.setStroke (90., 90., 90.) (.px 1),
    text (x + 8.0, 426.0) label (.px 12) |>.setFill (0.1, 0.1, 0.1) ]

private def surroundFlowSvg : Svg frame :=
  { elements :=
      (((List.finRange 8).flatMap mkEdge)
        ++ [
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
