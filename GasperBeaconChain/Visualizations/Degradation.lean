import GasperBeaconChain.Executable.UseCases.DynamicBound
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Executable.UseCases.Parametric.VizDegrade

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 30

private def beta (e : Nat) : Nat :=
  (vizN - e) - τ.one_third vizN - τ.one_third (vizN - e)

private def betaStatic : Nat := vizN - τ.one_third vizN - τ.one_third vizN

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 620; width := 620; height := 340

private def marginL : Float := 55.0
private def baseY : Float := 255.0
private def xscale : Float := 17.0
private def yscale : Float := 16.0
private def xOf (e : Nat) : Float := marginL + xscale * Float.ofNat e
private def yOf (v : Nat) : Float := baseY - yscale * Float.ofNat v

private def betaPts : Array (Point frame) :=
  ((List.range (vizN + 1)).map (fun e => ((xOf e, yOf (beta e)) : Point frame))).toArray

private def marker (e : Nat) : List (Svg.Element frame) :=
  [ circle (xOf e, yOf (beta e)) (.px 3) |>.setFill (0.80, 0.16, 0.16),
    text (xOf e - 6.0, yOf (beta e) - 9.0) (toString (beta e)) (.px 12)
      |>.setFill (0.6, 0.13, 0.13) ]

private def xtick (e : Nat) : List (Svg.Element frame) :=
  [ line (xOf e, baseY) (xOf e, baseY + 6.0) |>.setStroke (60., 60., 60.) (.px 2),
    text (xOf e - 6.0, baseY + 22.0) (toString e) (.px 13) |>.setFill (0.35, 0.35, 0.35) ]

private def degradationSvg : Svg frame :=
  { elements :=
      #[
         line (marginL, 40.0) (marginL, baseY) |>.setStroke (60., 60., 60.) (.px 2),
         line (marginL, baseY) (xOf vizN, baseY) |>.setStroke (60., 60., 60.) (.px 2),
         line (marginL, yOf betaStatic) (xOf vizN, yOf betaStatic)
           |>.setStroke (150., 150., 150.) (.px 2),
         polyline betaPts |>.setStroke (210., 40., 40.) (.px 3) ]
      ++ (xtick 0).toArray ++ (xtick 5).toArray ++ (xtick 10).toArray
      ++ (xtick 15).toArray ++ (xtick 20).toArray ++ (xtick vizN).toArray
      ++ (marker 0).toArray ++ (marker 5).toArray ++ (marker 10).toArray
      ++ (marker 15).toArray ++ (marker 20).toArray
      ++ #[ text (marginL - 4.0, 30.0)
              ("slashable bound  β(e)   (committee N = " ++ toString vizN ++ ")")
              (.px 15) |>.setFill (0.74, 0.16, 0.16),
            text (xOf vizN - 150.0, yOf betaStatic - 8.0)
              ("static  N/3 = " ++ toString betaStatic) (.px 13) |>.setFill (0.45, 0.45, 0.45),
            text (xOf 9, baseY + 44.0) "number of exited validators  e"
              (.px 14) |>.setFill (0.35, 0.35, 0.35) ] }

#html degradationSvg.toHtml

end GasperBeaconChain.Executable.UseCases.Parametric.VizDegrade
