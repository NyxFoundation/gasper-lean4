import GasperBeaconChain.Executable.UseCases.FinalizationK2
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Visualization — depth-`k` finalization (Gasper Definition 4.9 / §8.5 four-case rule)

Ordinary finalization (`finalized b`, the `k = 1` case) needs the *immediate* child of `b` to
be justified.  Gasper's Definition 4.9 generalises this to **depth-`k` finalization**:

$$
\text{k\_finalized}(b, b_h, k)\;:\Longleftrightarrow\;
\exists\,\ell s = [b=\ell_0,\dots,\ell_k],\;
\Big(\forall n\le k:\ \text{justified}(\ell_n, b_h{+}n)\wedge \ell_n = \text{anc}_n(b)\Big)
\;\wedge\;
\underbrace{\text{supermajority\_link}(b\Rightarrow \ell_k,\ b_h\to b_h{+}k)}_{\text{a single skip link spanning }k\text{ heights}} .
$$

So `b` is finalized at depth `k` when a *chain of `k+1` justified checkpoints* rises above it
**and** one supermajority **skip link** jumps the full `k` heights from `b` to the top.  This
absorbs attestation-inclusion delay: even if no height-`+1` link exists, a longer skip link
finalizes `b`.

This panel renders the `k = 2` finalization of block `1` on `FinalizationK2.stK2`
(`1⋖2⋖3`, witnessing list `[1,2,3]`):

* the three rungs `1,2,3` are coloured by live `justifiedB` (the `∀ n ≤ 2` justified pairs);
* the green link `1⇒2` is the ordinary depth-`1` finalizing link;
* the **purple arc `1⇒3`** is the depth-`2` finalizing skip link (heights `1→3`), the
  irreducibly-`k=2` ingredient — its supporters' weight (`= two_third N`) meets the 2/3 line,
  so `supermajority_link(1⇒3)` holds.

Put the cursor on `#html` to view.
-/

namespace GasperBeaconChain.Visualizations.KFinalization

open ProofWidgets Svg
open GasperBeaconChain.Core GasperBeaconChain.Executable
open GasperBeaconChain.Executable.UseCases GasperBeaconChain.Executable.UseCases.Parametric

private def vizN : Nat := 9

/-- Live `justifiedB` of a block on `stK2` (`b` reduced mod 8 into `Fin 8`). -/
private def jrung (b h : Nat) : Bool :=
  justifiedB τ (stake vizN) (vset vizN) parent genesis (stK2 vizN)
    ⟨b % 8, Nat.mod_lt b (by decide)⟩ h

/-- Live `supermajority_link` of the depth-2 skip link `1 ⇒ 3` (heights `1→3`) on `stK2`. -/
private def superSkip : Bool :=
  decide (supermajority_link τ (stake vizN) (vset vizN) (stK2 vizN) 1 3 1 3)

/-- Weight of the skip link's supporters (`= two_third N`). -/
private def skipWeight : Nat :=
  wt (stake vizN) (link_supporters (stK2 vizN) 1 3 1 3)

private def frame : Frame where
  xmin := 0; ymin := 0; xSize := 640; width := 640; height := 420

/-- Chain level `L` (0 = block 1, the finalized base) ↦ `(x, y)`. -/
private def chainX : Float := 250.0
private def yOf (L : Nat) : Float := 320.0 - 78.0 * Float.ofNat L

private def blue : Float × Float × Float := (0.62, 0.80, 0.98)
private def grey : Float × Float × Float := (0.88, 0.88, 0.88)

/-- A chain checkpoint `(block, height)` at level `L`, coloured by live `justifiedB`. -/
private def node (L block height : Nat) : List (Svg.Element frame) :=
  let ok := jrung block height
  [ circle (chainX, yOf L) (.px 22) |>.setFill (if ok then blue else grey)
      |>.setStroke (55., 55., 55.) (.px 2),
    text (chainX - 6.0, yOf L + 6.0) (toString block) (.px 19) |>.setFill (0.05, 0.05, 0.05),
    text (chainX - 78.0, yOf L + 5.0) ("h" ++ toString height) (.px 13) |>.setFill (0.45, 0.45, 0.45),
    text (chainX + 34.0, yOf L + 5.0)
      ("justified " ++ toString ok) (.px 12)
      |>.setFill (if ok then (0.13, 0.5, 0.27) else (0.6, 0.6, 0.6)) ]

private def kFinSvg : Svg frame :=
  { elements :=
      #[ text (40.0, 30.0)
           "depth-k finalization (Def 4.9):  k=2 finalizes block 1 by a skip link 1⇒3"
           (.px 15) |>.setFill (0.2, 0.2, 0.2),
         -- parent edges 1→2→3 (grey, the tree)
         line (chainX, yOf 0) (chainX, yOf 1) |>.setStroke (165., 165., 165.) (.px 2),
         line (chainX, yOf 1) (chainX, yOf 2) |>.setStroke (165., 165., 165.) (.px 2),
         -- ordinary depth-1 finalizing link 1⇒2 (green), drawn just left of the chain
         line (chainX - 12.0, yOf 0) (chainX - 12.0, yOf 1) |>.setStroke (40., 165., 80.) (.px 4),
         text (chainX - 150.0, (yOf 0 + yOf 1) / 2.0 + 4.0) "k=1 link 1⇒2" (.px 12)
           |>.setFill (0.16, 0.55, 0.30),
         -- depth-2 finalizing SKIP link 1⇒3 (purple arc on the right)
         path "M272,320 C390,280 390,200 272,164" |>.setStroke (130., 60., 180.) (.px 4),
         text (398.0, 240.0) "k=2 skip link" (.px 13) |>.setFill (0.45, 0.20, 0.62),
         text (398.0, 258.0) "1⇒3  (heights 1→3)" (.px 12) |>.setFill (0.45, 0.20, 0.62) ]
      ++ (node 0 1 1).toArray ++ (node 1 2 2).toArray ++ (node 2 3 3).toArray
      ++ #[ text (40.0, 388.0)
              ("witnessing list ls = [1,2,3]  (k+1 = 3 justified pairs);  skip link 1⇒3 supporters weight = "
                ++ toString skipWeight ++ " = two_third " ++ toString vizN
                ++ ",  supermajority = " ++ toString superSkip)
              (.px 12) |>.setFill (0.4, 0.4, 0.4) ] }

#html kFinSvg.toHtml

end GasperBeaconChain.Visualizations.KFinalization
