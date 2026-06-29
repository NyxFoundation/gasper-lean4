import GasperBeaconChain.Executable.UseCases.FinalizationK2
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — the *inductive derivation* of justification (the `justified` proof tree)

`Core.justified` is an **inductive predicate** with two rules:

```text
  ──────────────────────────  justified_genesis        (the base / axiom)
    ⊢ justified(genesis, 0)

    ⊢ justified(s, s_h)     justification_link(s ⟶ t, s_h ⟶ t_h)
  ─────────────────────────────────────────────────────────────  justified_link
                        ⊢ justified(t, t_h)
```

So a checkpoint is justified iff there is a *derivation* climbing from genesis along
supermajority links of strictly increasing height.  This panel renders exactly that
derivation as an upward **ladder** on the chain state `FinalizationK2.stK2`
(`0⇒1⇒2⇒3`, every link supported by `qTT = two_third N`):

* each rung `⊢ justified(b, h)` is **coloured live** by `justifiedB` on `stK2`
  (green = derivable, grey = not);
* each inference bar between two rungs is a `justified_link` step, labelled with the
  link and the supermajority side-condition `|supporters| ≥ two_third N`;
* the bottom bar is the `justified_genesis` axiom.

This is the *operational semantics of finality*: the decision procedure `justifiedB`
is precisely the bottom-up evaluation of this derivation (height recursion).  Put the
cursor on `#html` to view.
-/

namespace GasperBeaconChain.Visualizations.JustificationLadder

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

/-- The supermajority size each link must meet (`two_third vizN`). -/
private def quorumSize : Nat := τ.two_third vizN

/-- Is `(b, h)` derivable as `justified` on the chain state `stK2`? (live oracle).
The block index is reduced mod `8` so a free `b` still lands in `Fin 8` (the ladder only
ever queries `b ∈ {0,1,2,3}`, where `b % 8 = b`). -/
private def jrung (b h : Nat) : Bool :=
  justifiedB τ (stake vizN) (vset vizN) parent genesis (stK2 vizN)
    ⟨b % 8, Nat.mod_lt b (by decide)⟩ h

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 640; width := 640; height := 430

/-- The four ladder levels (genesis at the bottom): level `L` ↦ block `L`, height `L`. -/
private def yOf (L : Nat) : Float := 330.0 - 66.0 * Float.ofNat L

private def green : Float × Float × Float := (0.62, 0.90, 0.68)
private def grey  : Float × Float × Float := (0.88, 0.88, 0.88)

/-- A derivation rung `⊢ justified(b, h)`, filled by the live `justifiedB` verdict. -/
private def rung (L : Nat) : List (Svg.Element frame) :=
  let ok := jrung L L
  [ rect (200.0, yOf L - 18.0) (.abs 250.0) (.abs 36.0)
      |>.setFill (if ok then green else grey) |>.setStroke (60., 60., 60.) (.px 2),
    text (214.0, yOf L + 5.0)
      ("⊢ justified(" ++ toString L ++ ", h" ++ toString L ++ ")") (.px 15)
      |>.setFill (0.08, 0.08, 0.08),
    text (462.0, yOf L + 5.0) (if ok then "✓" else "·") (.px 17)
      |>.setFill (if ok then (0.13, 0.5, 0.27) else (0.6, 0.6, 0.6)),
    text (150.0, yOf L + 5.0) ("h" ++ toString L) (.px 13) |>.setFill (0.45, 0.45, 0.45) ]

/-- An inference bar `justified_link` between level `L` (premise) and `L+1` (conclusion). -/
private def infer (L : Nat) : List (Svg.Element frame) :=
  let midY := (yOf L + yOf (L + 1)) / 2.0 + 4.0
  [ line (195.0, midY) (455.0, midY) |>.setStroke (70., 70., 70.) (.px 1),
    text (462.0, midY + 4.0)
      ("justified_link  " ++ toString L ++ "⇒" ++ toString (L + 1)
        ++ "  [≥ " ++ toString quorumSize ++ "]") (.px 11)
      |>.setFill (0.30, 0.30, 0.55) ]

private def ladderSvg : Svg frame :=
  { elements :=
      #[ text (40.0, 34.0)
           "inductive derivation of  justified  (height-recursion = bottom-up evaluation)"
           (.px 15) |>.setFill (0.2, 0.2, 0.2) ]
      ++ (infer 0).toArray ++ (infer 1).toArray ++ (infer 2).toArray
      ++ (rung 0).toArray ++ (rung 1).toArray ++ (rung 2).toArray ++ (rung 3).toArray
      -- the genesis axiom bar, below the base rung
      ++ #[ line (195.0, yOf 0 + 30.0) (455.0, yOf 0 + 30.0) |>.setStroke (70., 70., 70.) (.px 1),
            text (210.0, yOf 0 + 47.0) "justified_genesis   (base case / axiom)" (.px 12)
              |>.setFill (0.30, 0.30, 0.55),
            text (40.0, 410.0)
              ("committee N = " ++ toString vizN ++ ",  every link supported by qTT, weight "
                ++ toString quorumSize ++ " = two_third " ++ toString vizN
                ++ "  ⇒  the whole chain 0⇒1⇒2⇒3 is justified")
              (.px 12) |>.setFill (0.4, 0.4, 0.4) ] }

#html ladderSvg.toHtml

end GasperBeaconChain.Visualizations.JustificationLadder
