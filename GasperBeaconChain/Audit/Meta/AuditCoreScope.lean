import Lean


namespace GasperBeaconChain.Audit.Meta

open Lean

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
