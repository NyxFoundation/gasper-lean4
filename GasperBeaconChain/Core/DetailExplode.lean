import Mathlib.Tactic.Explode

/-!
# `#detail_explode` command

A wrapper around `#explode` that sets pretty-printer options for
maximum detail in the Fitch table output:

* `pp.proofs true` — display proof terms
* `pp.notation false` — use raw application syntax
* `pp.fieldNotation false` — use explicit projections
* `pp.proofs.withType true` — annotate proof terms with types

This exists so that Verso's literate renderer can match the command
by its leading keyword `#detail_explode` in `show_output`, rather
than matching `set_option` (which would be the leading keyword of
`set_option ... in #explode`).
-/

open Lean Elab Command in
elab "#detail_explode " name:ident : command =>
  elabCommand (← `(
    set_option pp.proofs true in
    set_option pp.notation false in
    set_option pp.fieldNotation false in
    set_option pp.proofs.withType true in
    #explode $name))
