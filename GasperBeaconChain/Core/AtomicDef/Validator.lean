import Mathlib.Data.Fintype.Basic

universe u

namespace GasperBeaconChain.Core

/-!
# Validator context

A **validator context** specifies the set of protocol participants and
their stakes. It consists of:

* a finite type $`\mathsf{Validator}` with decidable equality,
* a total stake function
  $`\mathsf{stake} : \mathsf{Validator} \to \mathbb{N}`.

The finiteness of $`\mathsf{Validator}` (formalised as a
{name}`Fintype` instance) is essential: it provides
{lit}`Finset.univ : Finset Validator` (the set of all validators),
which is used in {lit}`link_supporters` to collect the supporters of
a checkpoint link.

Most definitions in Core are parameterised explicitly by
{lit}`Validator`, {lit}`[DecidableEq Validator]`,
{lit}`[Fintype Validator]`, and {lit}`stake` rather than by a bundled
context, so {lit}`ValidatorContext` serves primarily as documentation
of the required assumptions.

Coq source: {lit}`Validator.v`. Coq declares
{lit}`Validator : finType` and
{lit}`stake : {fmap Validator -> nat}` as global parameters with a
totality axiom; Lean replaces the partial finite map with a total
function and bundles the assumptions into a structure.
-/

/--
A **bundled validator context** — a finite type of participants
equipped with a stake function. It packages the ambient population
over which weights, quorums, and thresholds are computed.

# Data

* {lit}`Validator` — the type of protocol participants,
* {lit}`instDecidableEq` — a {name}`DecidableEq` instance on
  {lit}`Validator`,
* {lit}`instFintype` — a {name}`Fintype` instance on
  {lit}`Validator` (finiteness),
* {lit}`stake` — a total function
  $`\mathsf{stake} : \mathsf{Validator} \to \mathbb{N}`.

The first three fields jointly provide a finite type with decidable
equality; the fourth assigns a natural-number weight to each
participant.

# Intended semantics

The Gasper paper idealizes stake as a positive real of average
$`1` (total $`N`). Modelling it as $`\mathbb{N}`, as the Coq
development does, keeps all weight arithmetic exact; the only
divergence from that idealization is that zero-stake validators are
permitted, and these contribute nothing to any quorum or threshold
weight.

# Non-assumptions

This structure does *not* assume:

* positivity of $`\mathsf{stake}` — zero-stake validators are
  allowed;
* injectivity of $`\mathsf{stake}` — distinct validators may share
  a weight;
* non-emptiness of {lit}`Validator` — the empty population is a
  legal context;
* any normalization of the total weight (no fixed total $`N`, no
  average $`1`).

# Provenance

This is a first-class value, not a global axiom. Most Core
definitions take {lit}`Validator`, {lit}`[DecidableEq Validator]`,
{lit}`[Fintype Validator]`, and {lit}`stake` as explicit parameters
rather than this bundle, so the structure serves mainly to document
the required assumptions in one place.
-/
structure ValidatorContext where
  Validator : Type u
  instDecidableEq : DecidableEq Validator
  instFintype : Fintype Validator
  stake : Validator → Nat

end GasperBeaconChain.Core
