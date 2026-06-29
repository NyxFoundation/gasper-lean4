import Mathlib.Tactic.Explode

/-!
# {lit}`#detail_explode` command

A wrapper around {lit}`#explode` that sets pretty-printer options for
maximum detail in the Fitch table output:

* {lit}`pp.proofs true` — display proof terms
* {lit}`pp.notation false` — use raw application syntax
* {lit}`pp.fieldNotation false` — use explicit projections
* {lit}`pp.proofs.withType true` — annotate proof terms with types

This exists so that Verso's literate renderer can match the command
by its leading keyword {lit}`#detail_explode` in {lit}`show_output`,
rather than matching {lit}`set_option` (which would be the leading
keyword of {lit}`set_option ... in #explode`).
-/

open Lean Elab Command in
elab "#detail_explode " name:ident : command => do
  elabCommand (← `(
    set_option pp.proofs true in
    set_option pp.notation false in
    set_option pp.fieldNotation false in
    set_option pp.proofs.withType true in
    #explode $name))
