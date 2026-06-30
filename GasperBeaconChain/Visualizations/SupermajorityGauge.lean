import GasperBeaconChain.Executable.UseCases.SurroundFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Visualizations.SupermajorityGauge

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

private def N  : Nat := vizN
private def tt : Nat := τ.two_third vizN
private def ot : Nat := τ.one_third vizN

private def linkWeight (s t : Fin 8) (sh th : Nat) : Nat :=
  wt (stake vizN) (link_supporters (stFork vizN) s t sh th)

private def isSuper (s t : Fin 8) (sh th : Nat) : Bool :=
  decide (supermajority_link τ (stake vizN) (vset vizN) (stFork vizN) s t sh th)

private def wFull : Nat := wt (stake vizN) (vset vizN 1)
private def wA : Nat := linkWeight 0 1 0 1
private def wB : Nat := linkWeight 2 3 2 3
private def superA : Bool := isSuper 0 1 0 1
private def superB : Bool := isSuper 2 3 2 3

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 660; width := 660; height := 320

private def marginL : Float := 80.0
private def axisY : Float := 262.0
private def wscale : Float := 54.0
private def xOf (w : Nat) : Float := marginL + wscale * Float.ofNat w

private def green : Float × Float × Float := (0.45, 0.82, 0.55)
private def grey  : Float × Float × Float := (0.80, 0.80, 0.82)
private def red   : Float × Float × Float := (0.92, 0.55, 0.55)

private def gauge (y : Float) (w : Nat) (col : Float × Float × Float)
    (caption : String) (verdict : Option Bool) : List (Svg.Element frame) :=
  let body : List (Svg.Element frame) :=
    if w == 0 then
      [ text (marginL - 2.0, y + 18.0) "∅" (.px 16) |>.setFill (0.7, 0.25, 0.25) ]
    else
      [ rect (marginL, y) (.abs (xOf w - marginL)) (.abs 28.0)
          |>.setFill col |>.setStroke (70., 70., 70.) (.px 1) ]
  body ++
  [ text (marginL, y - 6.0) caption (.px 12) |>.setFill (0.25, 0.25, 0.25),
    text (xOf w + 8.0, y + 19.0)
      ("w = " ++ toString w ++ (match verdict with
        | some b => "   supermajority_link = " ++ toString b
        | none => "")) (.px 12)
      |>.setFill (match verdict with
        | some true => (0.13, 0.5, 0.27) | some false => (0.7, 0.25, 0.25)
        | none => (0.4, 0.4, 0.4)) ]

private def threshold (w : Nat) (label : String) (col : Float × Float × Float) :
    List (Svg.Element frame) :=
  [ line (xOf w, 56.0) (xOf w, axisY) |>.setStroke (255.0 * col.1, 255.0 * col.2.1, 255.0 * col.2.2) (.px 2),
    text (xOf w - 14.0, 50.0) label (.px 13) |>.setFill col ]

private def gaugeSvg : Svg frame :=
  { elements :=
      #[ text (40.0, 32.0)
           "supermajority gauge —  w(link_supporters)  vs  the 2/3 line of the committee"
           (.px 15) |>.setFill (0.2, 0.2, 0.2),
         line (marginL, axisY) (xOf N, axisY) |>.setStroke (60., 60., 60.) (.px 2),
         text (marginL - 8.0, axisY + 20.0) "0" (.px 12) |>.setFill (0.4, 0.4, 0.4),
         text (xOf N - 4.0, axisY + 20.0) (toString N) (.px 12) |>.setFill (0.4, 0.4, 0.4),
         text (240.0, axisY + 38.0) "validator weight  →" (.px 12) |>.setFill (0.4, 0.4, 0.4) ]
      ++ (threshold ot "1/3" (0.85, 0.55, 0.15)).toArray
      ++ (threshold tt "2/3" (0.13, 0.55, 0.30)).toArray
      ++ (gauge 80.0  wFull grey  "committee  univ  (the target's validator set vset t)" none).toArray
      ++ (gauge 140.0 wA    green "link 0⇒1   supporters = link_supporters(stFork,0,1,0,1) = qTT" (some superA)).toArray
      ++ (gauge 200.0 wB    red   "link 2⇒3   supporters = ∅   (no validator cast this vote)" (some superB)).toArray }

#html gaugeSvg.toHtml

end GasperBeaconChain.Visualizations.SupermajorityGauge
