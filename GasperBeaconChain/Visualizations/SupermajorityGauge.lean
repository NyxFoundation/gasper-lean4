import GasperBeaconChain.Executable.UseCases.SurroundFork
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — the supermajority gauge: how a vote-set becomes a justification link

The single definitional bridge from *votes* to *finality* is `supermajority_link`:

$$
\text{supermajority\_link}(st, s\!\to\!t, s_h\!\to\!t_h)
\;:\Longleftrightarrow\;
w\big(\underbrace{\text{link\_supporters}(st,s,t,s_h,t_h)}_{=\,\{v\mid \text{vote\_msg}\,v\,s\,t\,s_h\,t_h\}}\big)
\;\ge\; \tfrac23\,w(\text{vset}\,t).
$$

i.e. *count the validators who actually cast this exact vote, weigh them, and compare to the
two-thirds line of the target's validator set.*  This panel renders that comparison as a set
of **weight bars** measured against the `1/3` and `2/3` threshold lines of the committee, on
the real fork state `SurroundFork.stFork`:

* the full committee `univ` (weight `N`) — the `100%` reference;
* the link `0⇒1`, whose supporters are the actual `link_supporters (stFork) 0 1 0 1 = qTT`
  (weight `two_third N`): the bar reaches the `2/3` line, so `supermajority_link` **holds**;
* the link `2⇒3`, for which **no validator voted** (`link_supporters = ∅`, weight `0`): the
  bar is empty, well below `2/3`, so `supermajority_link` **fails**.

Every bar length is the *computed* `wt (link_supporters …)`, and each verdict is the live
`decide (supermajority_link …)` — the picture is the decision procedure.  Put the cursor on
`#html` to view.
-/

namespace GasperBeaconChain.Visualizations.SupermajorityGauge

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

private def N  : Nat := vizN
private def tt : Nat := τ.two_third vizN          -- the 2/3 line
private def ot : Nat := τ.one_third vizN           -- the 1/3 line

/-- Weight of the *actual* supporters of a link in `stFork` (computed `link_supporters`). -/
private def linkWeight (s t : Fin 8) (sh th : Nat) : Nat :=
  wt (stake vizN) (link_supporters (stFork vizN) s t sh th)

/-- Live `supermajority_link` verdict for a link in `stFork`. -/
private def isSuper (s t : Fin 8) (sh th : Nat) : Bool :=
  decide (supermajority_link τ (stake vizN) (vset vizN) (stFork vizN) s t sh th)

private def wFull : Nat := wt (stake vizN) (vset vizN 1)        -- = N
private def wA : Nat := linkWeight 0 1 0 1                       -- = two_third N (qTT)
private def wB : Nat := linkWeight 2 3 2 3                       -- = 0 (no voters)
private def superA : Bool := isSuper 0 1 0 1                     -- true
private def superB : Bool := isSuper 2 3 2 3                     -- false

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 660; width := 660; height := 320

private def marginL : Float := 80.0
private def axisY : Float := 262.0
private def wscale : Float := 54.0
private def xOf (w : Nat) : Float := marginL + wscale * Float.ofNat w

private def green : Float × Float × Float := (0.45, 0.82, 0.55)
private def grey  : Float × Float × Float := (0.80, 0.80, 0.82)
private def red   : Float × Float × Float := (0.92, 0.55, 0.55)

/-- A weight bar of computed length `w`, at row `y`, with caption and verdict. -/
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

/-- A dashed threshold line at weight `w`, with a label. -/
private def threshold (w : Nat) (label : String) (col : Float × Float × Float) :
    List (Svg.Element frame) :=
  [ line (xOf w, 56.0) (xOf w, axisY) |>.setStroke (255.0 * col.1, 255.0 * col.2.1, 255.0 * col.2.2) (.px 2),
    text (xOf w - 14.0, 50.0) label (.px 13) |>.setFill col ]

private def gaugeSvg : Svg frame :=
  { elements :=
      #[ text (40.0, 32.0)
           "supermajority gauge —  w(link_supporters)  vs  the 2/3 line of the committee"
           (.px 15) |>.setFill (0.2, 0.2, 0.2),
         -- weight axis
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
