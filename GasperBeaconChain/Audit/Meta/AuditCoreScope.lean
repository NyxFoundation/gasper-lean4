import Lean

/-!
# Audited scope enumeration for `GasperBeaconChain`

`sortedAuditedDeclNames`: all declarations under `GasperBeaconChain.Core.*`
**and** `GasperBeaconChain.Executable.*`, filtered only by
`Name.isInternalDetail` (compiler internals). Auto-generated recursors,
constructors, `.below`, etc. are included.

The `Executable` (computational) layer is held to the same axiom hygiene as
`Core` (the logical layer): both must stay free of `Classical.choice`,
`sorryAx`, and native-compute axioms. Including `Executable` here makes that a
standing guarantee of `#mr_audit_axioms` (hence of `make audit`).
-/

namespace GasperBeaconChain.Audit.Meta

open Lean

/-- A declaration in the audited project scope: the logical `Core` layer or the
computational `Executable` layer. -/
def isAuditedDecl (env : Environment) (n : Name) : Bool :=
  ((`GasperBeaconChain.Core).isPrefixOf n
    || (`GasperBeaconChain.Executable).isPrefixOf n) &&
  !n.isInternalDetail &&
  env.contains n

def gatherAuditedDeclNames (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if isAuditedDecl env n then acc.push n else acc

def sortedAuditedDeclNames (env : Environment) : Array Name :=
  (gatherAuditedDeclNames env).qsort fun a b => Name.cmp a b == Ordering.lt

end GasperBeaconChain.Audit.Meta
