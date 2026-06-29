import GasperBeaconChain.Visualizations.SlashingConditions
import GasperBeaconChain.Visualizations.SupermajorityGauge
import GasperBeaconChain.Visualizations.JustificationLadder
import GasperBeaconChain.Visualizations.KFinalization
import GasperBeaconChain.Visualizations.AccountableSafety
import GasperBeaconChain.Visualizations.PlausibleLiveness
import GasperBeaconChain.Visualizations.SurroundFlow
import GasperBeaconChain.Visualizations.OverlapVenn
import GasperBeaconChain.Visualizations.Degradation

/-!
# Visualizations — data-driven ProofWidgets read-outs of the verified structures

Each visualization computes its geometry from the **real** Core/Executable functions
(`τ.one_third`/`τ.two_third`, `justifiedB`, `slashedB`, the dynamic-bound number `β`), so the
picture is a faithful trace of the proof, not a hand-drawn sketch.  Open a file and put the
cursor on its `#html` line to view in the infoview.

Two thematic groups:

**Definitional core** — the meaning of the primitives and theorems:
* `SlashingConditions` — the *interval geometry* of S1 (double) & S2 (surround), live `slashedB`.
* `SupermajorityGauge` — `w(link_supporters)` vs the 2/3 line, live `supermajority_link`.
* `JustificationLadder` — the *inductive derivation* of `justified` (proof tree), live `justifiedB`.
* `KFinalization` — depth-`k` finalization (Def 4.9): the `k=2` skip link `1⇒3` on `stK2`.
* `AccountableSafety` — the *causal structure* of Thm 3.2 (fork → 2/3 quorums → N/3 → slashing).
* `PlausibleLiveness` — no-deadlock: select an honest 2/3 quorum (`goodQuorumAtB`) around faults.

**Behavior & quantities** — the protocol running and its bounds:
* `SurroundFlow` — the S2 surround-vote **processing flow & behavior** on the real `stFork`:
  justification → finalization (oracle-coloured) → fork → live `slashedB` count.
* `OverlapVenn`  — the two distinct 2/3 quorums and their exactly-`N/3` intersection (Lemma 5.1).
* `Degradation`  — the §8.6 slashable bound `β(e)` degrading as validators exit (Thm 8.3).
-/
