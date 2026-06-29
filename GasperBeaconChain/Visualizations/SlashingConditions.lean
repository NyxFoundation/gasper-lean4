import GasperBeaconChain.Executable.UseCases.SurroundFork
import GasperBeaconChain.Executable.UseCases.JustifiedFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — the *interval geometry* of the two slashing conditions (S1, S2)

The slashing predicates are, at heart, **geometric statements about vote-intervals on the
height axis**.  A Casper FFG vote is `(s ⟶ t, s_h ⟶ t_h)`: it spans the height interval
`[s_h, t_h]` from a source checkpoint up to a target checkpoint.  The two conditions are:

* **S1 (double vote)** — two votes of one validator with the **same target height** `t_h`
  but **different targets**.  Geometrically: two intervals reaching the *same height level*
  yet landing on *different blocks* (a fork at one height).
  Core: `vote_msg v s₁ t₁ _ t_h ∧ vote_msg v s₂ t₂ _ t_h ∧ t₁ ≠ t₂`.

* **S2 (surround vote)** — `s₁_h < s₂_h ∧ t₂_h < t₁_h`: one interval **strictly nests**
  inside another.  Geometrically: an outer interval that *surrounds* an inner one.

This panel draws both conditions, using the **actual witnessing votes** of the project's
fork states:

* S1 from `JustifiedFork.stJust` — one `qTT` validator voted `0⟶1` and `0⟶4`, both at target
  height `1` (`1 ≠ 4`);
* S2 from `SurroundFork.stFork` — one `qTT` validator voted the skip link `0⟶6` (`h0⟶h3`)
  and `1⟶2` (`h1⟶h2`), and `0<1 ∧ 2<3`.

The verdict strip at the bottom is the **live** `slashedB` evaluated on those states — the
geometry shown is exactly what the decision procedure detects.  Put the cursor on `#html`.
-/

namespace GasperBeaconChain.Visualizations.SlashingConditions

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

/-- The live S1 verdict: a `qTT` validator of `stJust` is slashed (double vote). -/
private def s1Verdict : Bool := slashedB (stJust vizN) ⟨0, by decide⟩
/-- The live S2 verdict: a `qTT` validator of `stFork` is slashed (surround vote). -/
private def s2Verdict : Bool := slashedB (stFork vizN) ⟨0, by decide⟩

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 680; width := 680; height := 390

/-- Height `h` maps to a `y`-coordinate (axis points up: `h0` at the bottom). -/
private def yOfH (h : Nat) : Float := 300.0 - 60.0 * Float.ofNat h

/-- A height tick label at the given axis `x`. -/
private def htick (x : Float) (h : Nat) : List (Svg.Element frame) :=
  [ line (x, yOfH h) (x + 6.0, yOfH h) |>.setStroke (90., 90., 90.) (.px 1),
    text (x - 22.0, yOfH h + 5.0) ("h" ++ toString h) (.px 13) |>.setFill (0.4, 0.4, 0.4) ]

/-- A vote drawn as a vertical interval `[s_h, t_h]` at horizontal position `x`,
with a filled disc at the target (top) end. -/
private def voteInterval (x : Float) (sh th : Nat) (col : Float × Float × Float)
    (label : String) : List (Svg.Element frame) :=
  [ line (x, yOfH sh) (x, yOfH th) |>.setStroke (255.0 * col.1, 255.0 * col.2.1, 255.0 * col.2.2) (.px 5),
    circle (x, yOfH th) (.px 6) |>.setFill col,
    circle (x, yOfH sh) (.px 3) |>.setFill (0.45, 0.45, 0.45),
    text (x + 10.0, yOfH th + 4.0) label (.px 13) |>.setFill col ]

/-- A dashed horizontal guide at height `h` between two `x` positions. -/
private def hguide (x1 x2 : Float) (h : Nat) (col : Float × Float × Float) : Svg.Element frame :=
  line (x1, yOfH h) (x2, yOfH h) |>.setStroke (255.0 * col.1, 255.0 * col.2.1, 255.0 * col.2.2) (.px 1)

private def red : Float × Float × Float := (0.84, 0.18, 0.18)
private def grn : Float × Float × Float := (0.13, 0.55, 0.30)
private def blu : Float × Float × Float := (0.18, 0.40, 0.80)

private def slashingSvg : Svg frame :=
  { elements :=
      -- ── S1 panel (double vote): two intervals to the SAME height, DIFFERENT blocks ──
      #[ text (40.0, 36.0) "S1 — double vote" (.px 17) |>.setFill red,
         line (95.0, yOfH 0) (95.0, yOfH 1) |>.setStroke (90., 90., 90.) (.px 2) ]
      ++ (htick 95.0 0).toArray ++ (htick 95.0 1).toArray
      ++ (voteInterval 160.0 0 1 red "0⟶1").toArray
      ++ (voteInterval 250.0 0 1 red "0⟶4").toArray
      ++ #[ hguide 150.0 270.0 1 red,
            text (120.0, yOfH 1 - 14.0) "same t_h = 1,  targets 1 ≠ 4" (.px 12) |>.setFill red,
            text (60.0, 345.0) "∃ v: vote(v,_,1,_,1) ∧ vote(v,_,4,_,1)  ⇒  slashed (S1)"
              (.px 12) |>.setFill (0.3, 0.1, 0.1) ]
      -- ── divider ──
      ++ #[ line (350.0, 60.0) (350.0, 320.0) |>.setStroke (200., 200., 200.) (.px 1) ]
      -- ── S2 panel (surround vote): outer interval strictly nests the inner ──
      ++ #[ text (400.0, 36.0) "S2 — surround vote" (.px 17) |>.setFill grn,
            line (410.0, yOfH 0) (410.0, yOfH 3) |>.setStroke (90., 90., 90.) (.px 2) ]
      ++ (htick 410.0 0).toArray ++ (htick 410.0 1).toArray
      ++ (htick 410.0 2).toArray ++ (htick 410.0 3).toArray
      ++ (voteInterval 480.0 0 3 red "0⟶6  (skip)").toArray
      ++ (voteInterval 560.0 1 2 grn "1⟶2").toArray
      ++ #[ hguide 470.0 600.0 0 red, hguide 470.0 600.0 3 red,
            hguide 550.0 600.0 1 grn, hguide 550.0 600.0 2 grn,
            text (430.0, 348.0) "s₁(0) < s₂(1)  ∧  t₂(2) < t₁(3)  ⇒  slashed (S2)"
              (.px 12) |>.setFill (0.1, 0.3, 0.15) ]
      -- ── live verdict strip ──
      ++ #[ rect (40.0, 362.0) (.abs 600.0) (.abs 24.0)
              |>.setFill (0.96, 0.96, 0.92) |>.setStroke (180., 180., 180.) (.px 1),
            text (50.0, 379.0)
              ("live verdict (slashedB on the real states):   S1 = " ++ toString s1Verdict
                ++ "    S2 = " ++ toString s2Verdict) (.px 13) |>.setFill (0.2, 0.2, 0.2) ] }

#html slashingSvg.toHtml

end GasperBeaconChain.Visualizations.SlashingConditions
