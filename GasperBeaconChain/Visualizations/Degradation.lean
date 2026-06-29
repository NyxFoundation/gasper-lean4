import GasperBeaconChain.Executable.UseCases.DynamicBound
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — graceful degradation of the §8.6 slashable bound vs. number of exits

A data-driven SVG plot of `DynamicBound`: the slashable-weight guarantee

$$ \beta(e)\;=\;(N-e)\;-\;\big\lfloor N/3\big\rfloor\;-\;\big\lfloor (N-e)/3\big\rfloor $$

as a function of the number of exited validators `e ∈ \{0,\dots,N\}` (left branch stable,
no activations).  This is **exactly the quantity** `dyn_quorum_bound` lower-bounds; the curve
is computed from the real threshold `τ.one_third`, so it is a faithful trace of the proof.

* the red curve is `β(e)` — it descends monotonically as validators leave;
* the grey dashed line is the static Casper bound `β(0) = N/3` (no churn);
* `β` hits `0` once roughly a third of the committee has exited — past that, a fork need
  not be slashable, exactly Gasper's §8.6 warning.

Put the cursor on the `#html` line to view.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric.VizDegrade

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable.UseCases.Parametric

/-- Committee size for the plot. -/
private def vizN : Nat := 30

/-- The §8.6 dynamic bound as a pure number (the value `dyn_quorum_bound` lower-bounds):
`β(e) = (N - e) - one_third N - one_third (N - e)`. -/
private def beta (e : Nat) : Nat :=
  (vizN - e) - τ.one_third vizN - τ.one_third (vizN - e)

/-- The static (no-churn) bound `β(0) = N/3`. -/
private def betaStatic : Nat := vizN - τ.one_third vizN - τ.one_third vizN

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 620; width := 620; height := 340

/-- Plot geometry. -/
private def marginL : Float := 55.0
private def baseY : Float := 255.0
private def xscale : Float := 17.0
private def yscale : Float := 16.0
private def xOf (e : Nat) : Float := marginL + xscale * Float.ofNat e
private def yOf (v : Nat) : Float := baseY - yscale * Float.ofNat v

/-- The polyline points of `β` over `e = 0 … N`. -/
private def betaPts : Array (Point frame) :=
  ((List.range (vizN + 1)).map (fun e => ((xOf e, yOf (beta e)) : Point frame))).toArray

/-- A marker dot plus value label at exit count `e`. -/
private def marker (e : Nat) : List (Svg.Element frame) :=
  [ circle (xOf e, yOf (beta e)) (.px 3) |>.setFill (0.80, 0.16, 0.16),
    text (xOf e - 6.0, yOf (beta e) - 9.0) (toString (beta e)) (.px 12)
      |>.setFill (0.6, 0.13, 0.13) ]

/-- An x-axis tick (exit count) with label. -/
private def xtick (e : Nat) : List (Svg.Element frame) :=
  [ line (xOf e, baseY) (xOf e, baseY + 6.0) |>.setStroke (60., 60., 60.) (.px 2),
    text (xOf e - 6.0, baseY + 22.0) (toString e) (.px 13) |>.setFill (0.35, 0.35, 0.35) ]

private def degradationSvg : Svg frame :=
  { elements :=
      #[ -- axes
         line (marginL, 40.0) (marginL, baseY) |>.setStroke (60., 60., 60.) (.px 2),
         line (marginL, baseY) (xOf vizN, baseY) |>.setStroke (60., 60., 60.) (.px 2),
         -- static reference β(0) = N/3
         line (marginL, yOf betaStatic) (xOf vizN, yOf betaStatic)
           |>.setStroke (150., 150., 150.) (.px 2),
         -- the degradation curve β(e)
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
