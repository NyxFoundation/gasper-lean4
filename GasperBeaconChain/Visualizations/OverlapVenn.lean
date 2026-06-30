import GasperBeaconChain.Executable.UseCases.QuorumOverlap
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Executable.UseCases.Parametric.VizOverlap

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable.UseCases
open GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 30

private def t2 : Nat := τ.two_third vizN
private def t1 : Nat := τ.one_third vizN
private def ov : Nat := τ.two_third vizN - τ.one_third vizN

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 620; width := 620; height := 320

private def pxPer : Float := 16.0
private def xOf (i : Nat) : Float := 45.0 + pxPer * Float.ofNat i
private def wOf (k : Nat) : Float := pxPer * Float.ofNat k

private def qLrowY : Float := 95.0
private def qRrowY : Float := 165.0
private def barH : Float := 46.0

private def guide (i : Nat) : Svg.Element frame :=
  line (xOf i, 70.0) (xOf i, 240.0) |>.setStroke (120., 120., 120.) (.px 1)

private def tick (i : Nat) : List (Svg.Element frame) :=
  [ line (xOf i, 250.0) (xOf i, 258.0) |>.setStroke (60., 60., 60.) (.px 2),
    text (xOf i - 6.0, 274.0) (toString i) (.px 14) |>.setFill (0.3, 0.3, 0.3) ]

private def overlapVennSvg : Svg frame :=
  { elements :=
      #[
         rect (xOf 0, qLrowY) (.abs (wOf t2)) (.abs barH)
           |>.setFill (0.62, 0.80, 0.98) |>.setStroke (45., 90., 170.) (.px 2),
         rect (xOf t1, qRrowY) (.abs (wOf (vizN - t1))) (.abs barH)
           |>.setFill (0.62, 0.92, 0.70) |>.setStroke (40., 150., 80.) (.px 2),
         rect (xOf t1, qLrowY) (.abs (wOf ov)) (.abs barH)
           |>.setFill (0.93, 0.42, 0.42) |>.setStroke (170., 35., 35.) (.px 2),
         rect (xOf t1, qRrowY) (.abs (wOf ov)) (.abs barH)
           |>.setFill (0.93, 0.42, 0.42) |>.setStroke (170., 35., 35.) (.px 2),
         guide t1, guide t2,
         line (xOf 0, 250.0) (xOf vizN, 250.0) |>.setStroke (60., 60., 60.) (.px 2) ]
      ++ (tick 0).toArray ++ (tick t1).toArray ++ (tick t2).toArray ++ (tick vizN).toArray
      ++ #[
           text (xOf 0, qLrowY - 10.0)
             ("q_L = [0, 2N/3)   w = " ++ toString t2) (.px 15) |>.setFill (0.16, 0.35, 0.66),
           text (xOf t1, qRrowY + barH + 20.0)
             ("q_R = [N/3, N)   w = " ++ toString t2) (.px 15) |>.setFill (0.14, 0.52, 0.30),
           text (xOf t1 - 8.0, 40.0)
             ("q_L ∩ q_R = [N/3, 2N/3)   w = " ++ toString ov ++ " = N/3  (slashable, TIGHT)")
             (.px 15) |>.setFill (0.74, 0.16, 0.16),
           text (380.0, 300.0)
             ("committee N = " ++ toString vizN ++ ",  one_third = " ++ toString t1
               ++ ",  two_third = " ++ toString t2) (.px 13) |>.setFill (0.4, 0.4, 0.4) ] }

#html overlapVennSvg.toHtml

end GasperBeaconChain.Executable.UseCases.Parametric.VizOverlap
