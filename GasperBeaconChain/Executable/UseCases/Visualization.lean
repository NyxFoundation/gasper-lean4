import GasperBeaconChain.Executable.UseCases.SurroundFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Executable.UseCases.Parametric.Viz

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases.Parametric

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

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 620; width := 620; height := 460

private def posX (b : Fin 8) : Float :=
  if b.val == 0 then 310.0 else if b.val ≤ 3 then 210.0 else 430.0
private def posY (b : Fin 8) : Float := 50.0 + 90.0 * Float.ofNat (heightFn b)

private def mkNode (b : Fin 8) : List (Svg.Element frame) :=
  let fill : Float × Float × Float :=
    if isFinal b then (0.20, 0.45, 0.95)
    else if isJust b then (0.60, 0.78, 0.98)
    else (0.88, 0.88, 0.88)
  [ circle (posX b, posY b) (.px 21) |>.setFill fill |>.setStroke (55., 55., 55.) (.px 2),
    text (posX b - 6.0, posY b + 6.0) (toString b.val) (.px 19) |>.setFill (0.04, 0.04, 0.04) ]

private def mkEdge (b : Fin 8) : List (Svg.Element frame) :=
  match parentFnOpt b with
  | none => []
  | some p => [ line (posX p, posY p) (posX b, posY b) |>.setStroke (155., 155., 155.) (.px 3) ]

private def surroundForkSvg : Svg frame :=
  { elements :=
      (((List.finRange 8).flatMap mkEdge)
        ++ [
             path "M310,50 C570,95 575,290 430,320" |>.setStroke (220., 40., 40.) (.px 4),
             line (210., 140.) (210., 230.) |>.setStroke (40., 170., 70.) (.px 5) ]
        ++ ((List.finRange 8).flatMap mkNode)
        ++ [ text (485., 120.) "skip 0⇒6 (outer [0,3])" (.px 14) |>.setFill (0.78, 0.16, 0.16),
             text (95., 195.) "fin 1⇒2 (inner [1,2])" (.px 13) |>.setFill (0.16, 0.55, 0.27),
             text (20., 54.)  "h0" (.px 15) |>.setFill (0.55, 0.55, 0.55),
             text (20., 140.) "h1" (.px 15) |>.setFill (0.55, 0.55, 0.55),
             text (20., 230.) "h2" (.px 15) |>.setFill (0.55, 0.55, 0.55),
             text (20., 320.) "h3" (.px 15) |>.setFill (0.55, 0.55, 0.55),
             text (20., 410.) "h4" (.px 15) |>.setFill (0.55, 0.55, 0.55) ]).toArray }

#html surroundForkSvg.toHtml

end GasperBeaconChain.Executable.UseCases.Parametric.Viz
