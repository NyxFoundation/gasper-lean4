import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Data.Json
import GasperBeaconChain.Audit.Meta.AuditCoreScope


namespace GasperBeaconChain.Audit.Meta

open Lean Elab Command

private def isNativeComputeAxiomJ (n : Name) : Bool :=
  match (toString n).splitOn "._native." with
  | [_] => false
  | _   => true

private def hasNativeComputeJ (ax : Array Name) : Bool :=
  ax.contains ``Lean.trustCompiler || ax.any isNativeComputeAxiomJ

private def declModuleNameJ? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]?
  | none => none

private structure Tally where
  total      : Nat := 0
  sorryC     : Nat := 0
  nativeC    : Nat := 0
  choiceC    : Nat := 0
  propextC   : Nat := 0
  quotC      : Nat := 0
  funextC    : Nat := 0
  errorC     : Nat := 0
  warnC      : Nat := 0
  infoC      : Nat := 0
  cleanC     : Nat := 0
  deriving Inhabited

private def Tally.add (t : Tally) (ax : Array Name) : Tally :=
  let hasSorry  := ax.contains ``sorryAx
  let hasNative := hasNativeComputeJ ax
  let hasChoice := ax.contains ``Classical.choice
  { total    := t.total + 1
    sorryC   := t.sorryC   + (if hasSorry then 1 else 0)
    nativeC  := t.nativeC  + (if hasNative then 1 else 0)
    choiceC  := t.choiceC  + (if hasChoice then 1 else 0)
    propextC := t.propextC + (if ax.contains ``propext then 1 else 0)
    quotC    := t.quotC    + (if ax.contains ``Quot.sound then 1 else 0)
    funextC  := t.funextC  + (if ax.contains ``funext then 1 else 0)
    errorC   := t.errorC + (if hasSorry then 1 else 0)
    warnC    := t.warnC  + (if !hasSorry && (hasChoice || hasNative) then 1 else 0)
    infoC    := t.infoC  +
      (if !ax.isEmpty && !hasSorry && !hasChoice && !hasNative then 1 else 0)
    cleanC   := t.cleanC + (if ax.isEmpty then 1 else 0) }

private def Tally.toJson (t : Tally) (modules : Nat) : Json :=
  Json.mkObj
    [ ("project", Json.str "GasperBeaconChain"),
      ("totalDeclarations", Json.num t.total),
      ("modules", Json.num modules),
      ("axiomProfile", Json.mkObj
        [ ("sorryAx", Json.num t.sorryC),
          ("nativeCompute", Json.num t.nativeC),
          ("Classical.choice", Json.num t.choiceC),
          ("propext", Json.num t.propextC),
          ("Quot.sound", Json.num t.quotC),
          ("funext", Json.num t.funextC) ]),
      ("severity", Json.mkObj
        [ ("error", Json.num t.errorC),
          ("warn", Json.num t.warnC),
          ("info", Json.num t.infoC),
          ("clean", Json.num t.cleanC) ]),
      ("health", Json.mkObj
        [ ("choiceFree", Json.bool (t.choiceC == 0)),
          ("sorryFree", Json.bool (t.sorryC == 0)),
          ("nativeFree", Json.bool (t.nativeC == 0)),
          ("funextFree", Json.bool (t.funextC == 0)),
          ("axiomDependent", Json.num (t.errorC + t.warnC + t.infoC)),
          ("axiomFree", Json.num t.cleanC) ]) ]

elab "#mr_audit_json" : command => do
  let env ← getEnv
  let names := sortedAuditedDeclNames env
  let mut t : Tally := {}
  let mut mods : Array Name := #[]
  for n in names do
    let ax ← liftCoreM (collectAxioms n)
    t := t.add ax
    match declModuleNameJ? env n with
    | some m => unless mods.contains m do mods := mods.push m
    | none => pure ()
  let j := t.toJson mods.size
  logInfo m!"{j.pretty}"

end GasperBeaconChain.Audit.Meta
