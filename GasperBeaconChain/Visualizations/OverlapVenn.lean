import GasperBeaconChain.Executable.UseCases.QuorumOverlap
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — the two distinct 2/3 quorums and their *exactly-`N/3`* overlap (Lemma 5.1)

A data-driven SVG read-out of `QuorumOverlap`: the two most spread-apart 2/3 quorums of an
`N`-committee, drawn as two bars over the validator axis `[0, N)`, with their intersection
highlighted.  **Every coordinate is computed from the real threshold functions**
`τ.two_third`/`τ.one_third` evaluated at the committee size `vizN` — the picture is the proof.

```text
  q_L = [0 , 2N/3)   ████████████████░░░░░░░░         (light blue)
  q_R = [N/3 , N)     ░░░░░░░░████████████████         (light green)
  q_L ∩ q_R = [N/3 , 2N/3) = the red columns          (slashable; width = N/3, TIGHT)
```

The red region's width is `τ.two_third vizN − τ.one_third vizN`, which `overlap_weight_exact`
proves equals the Core lower bound `N − N/3 − N/3` — i.e. the Casper 1/3 bound is attained.
Put the cursor on the `#html` line to view.
-/

namespace GasperBeaconChain.Executable.UseCases.Parametric.VizOverlap

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable.UseCases
open GasperBeaconChain.Executable.UseCases.Parametric

/-- Committee size used for the picture (the geometry is proved identical for every `N`). -/
private def vizN : Nat := 30

/-- The two thirds, read off the *actual* threshold the proofs use. -/
private def t2 : Nat := τ.two_third vizN        -- = 20  (= 2N/3)
private def t1 : Nat := τ.one_third vizN         -- = 10  (=  N/3)
private def ov : Nat := τ.two_third vizN - τ.one_third vizN   -- = 10 (= overlap = N/3, exact)

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 620; width := 620; height := 320

/-- Pixels per validator, and the x-coordinate of validator index `i`. -/
private def pxPer : Float := 16.0
private def xOf (i : Nat) : Float := 45.0 + pxPer * Float.ofNat i
private def wOf (k : Nat) : Float := pxPer * Float.ofNat k

private def qLrowY : Float := 95.0
private def qRrowY : Float := 165.0
private def barH : Float := 46.0

/-- A dashed vertical guide at validator index `i`. -/
private def guide (i : Nat) : Svg.Element frame :=
  line (xOf i, 70.0) (xOf i, 240.0) |>.setStroke (120., 120., 120.) (.px 1)

/-- A bottom-axis tick with its index label. -/
private def tick (i : Nat) : List (Svg.Element frame) :=
  [ line (xOf i, 250.0) (xOf i, 258.0) |>.setStroke (60., 60., 60.) (.px 2),
    text (xOf i - 6.0, 274.0) (toString i) (.px 14) |>.setFill (0.3, 0.3, 0.3) ]

private def overlapVennSvg : Svg frame :=
  { elements :=
      #[ -- q_L bar  [0, t2)  — light blue
         rect (xOf 0, qLrowY) (.abs (wOf t2)) (.abs barH)
           |>.setFill (0.62, 0.80, 0.98) |>.setStroke (45., 90., 170.) (.px 2),
         -- q_R bar  [t1, N)  — light green
         rect (xOf t1, qRrowY) (.abs (wOf (vizN - t1))) (.abs barH)
           |>.setFill (0.62, 0.92, 0.70) |>.setStroke (40., 150., 80.) (.px 2),
         -- the intersection columns  [t1, t2)  painted red over BOTH bars
         rect (xOf t1, qLrowY) (.abs (wOf ov)) (.abs barH)
           |>.setFill (0.93, 0.42, 0.42) |>.setStroke (170., 35., 35.) (.px 2),
         rect (xOf t1, qRrowY) (.abs (wOf ov)) (.abs barH)
           |>.setFill (0.93, 0.42, 0.42) |>.setStroke (170., 35., 35.) (.px 2),
         -- guides at the two thirds
         guide t1, guide t2,
         -- bottom axis
         line (xOf 0, 250.0) (xOf vizN, 250.0) |>.setStroke (60., 60., 60.) (.px 2) ]
      ++ (tick 0).toArray ++ (tick t1).toArray ++ (tick t2).toArray ++ (tick vizN).toArray
      ++ #[ -- row / region labels (carrying the exact computed weights)
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
