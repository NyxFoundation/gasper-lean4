import GasperBeaconChain.Executable.UseCases.ModelN
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Visualizations.PlausibleLivenessViz

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private abbrev vizN : Nat := 9

private def stLiveViz : State (Fin vizN) H :=
  { { validator := 0, source := 0, target := 1, sourceHeight := 0, targetHeight := 1 },
    { validator := 0, source := 0, target := 2, sourceHeight := 0, targetHeight := 1 } }

private def honest : Finset (Fin vizN) := Finset.univ.filter (fun v => v ≠ (0 : Fin vizN))

private def slashedCell (v : Fin vizN) : Bool := slashedB stLiveViz v
private def goodUniv : Bool := goodQuorumAtB τ (stake vizN) (vset vizN) stLiveViz 0 Finset.univ
private def goodHonest : Bool := goodQuorumAtB τ (stake vizN) (vset vizN) stLiveViz 0 honest
private def honestWeight : Nat := wt (stake vizN) honest
private def tt : Nat := τ.two_third vizN

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 620; width := 620; height := 300

private def cellX (i : Nat) : Float := 56.0 + 58.0 * Float.ofNat i

private def red   : Float × Float × Float := (0.93, 0.50, 0.50)
private def green : Float × Float × Float := (0.58, 0.86, 0.62)

private def mkCell (v : Fin vizN) : List (Svg.Element frame) :=
  let faulty := slashedCell v
  [ rect (cellX v.val, 78.0) (.abs 44.0) (.abs 44.0)
      |>.setFill (if faulty then red else green) |>.setStroke (60., 60., 60.) (.px 2),
    text (cellX v.val + 14.0, 106.0) (toString v.val) (.px 17) |>.setFill (0.06, 0.06, 0.06) ]

private def livenessSvg : Svg frame :=
  { elements :=
      (#[ text (40.0, 32.0)
            "plausible liveness — select an honest 2/3 quorum, route finality around faults"
            (.px 14) |>.setFill (0.2, 0.2, 0.2),
          text (40.0, 64.0) ("committee  (slashedB live):") (.px 13) |>.setFill (0.35, 0.35, 0.35) ]
        ++ ((List.finRange vizN).flatMap mkCell).toArray)
      ++ #[
            line (cellX 1, 132.0) (cellX (vizN - 1) + 44.0, 132.0) |>.setStroke (40., 140., 70.) (.px 3),
            line (cellX 1, 132.0) (cellX 1, 126.0) |>.setStroke (40., 140., 70.) (.px 3),
            line (cellX (vizN - 1) + 44.0, 132.0) (cellX (vizN - 1) + 44.0, 126.0)
              |>.setStroke (40., 140., 70.) (.px 3),
            text (cellX 3, 150.0)
              ("honest quorum = committee \\ {0},  weight " ++ toString honestWeight)
              (.px 13) |>.setFill (0.14, 0.5, 0.28),
            text (40.0, 196.0)
              ("goodQuorumAtB (whole committee univ) = " ++ toString goodUniv
                ++ "    (✗ — contains the slashed validator 0)")
              (.px 13) |>.setFill (0.7, 0.25, 0.25),
            text (40.0, 222.0)
              ("goodQuorumAtB (committee \\ {0}) = " ++ toString goodHonest
                ++ "    (✓ — weight " ++ toString honestWeight ++ " ≥ two_third " ++ toString vizN
                ++ " = " ++ toString tt ++ ")")
              (.px 13) |>.setFill (0.14, 0.5, 0.28),
            text (40.0, 258.0)
              "⇒ a single faulty validator cannot deadlock finality: an honest 2/3 always exists"
              (.px 13) |>.setFill (0.2, 0.2, 0.2) ] }

#html livenessSvg.toHtml

end GasperBeaconChain.Visualizations.PlausibleLivenessViz
