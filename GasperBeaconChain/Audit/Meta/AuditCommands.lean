import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.DeclarationRange
import GasperBeaconChain.Audit.Meta.AuditCoreScope


namespace GasperBeaconChain.Audit.Meta

open Lean Elab Command


private abbrev AxiomCache := NameMap (Array Name)

private def cachedCollect (cache : AxiomCache) (n : Name) :
    CommandElabM (Array Name × AxiomCache) := do
  match cache.find? n with
  | some ax => return (ax, cache)
  | none =>
    let ax ← liftCoreM (collectAxioms n)
    return (ax, cache.insert n ax)


private def declModuleName? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]?
  | none => none

private def moduleToPath (m : Name) : String :=
  (toString m).replace "." "/" ++ ".lean"

private def constInfoKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .defnInfo _   => "def"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "recursor"

private def declLine? (ranges? : Option DeclarationRanges) : Option Nat :=
  ranges?.map fun r => r.range.pos.line

private def pct (n total : Nat) : String :=
  if total == 0 then "—" else s!"{(n * 1000 / total + 5) / 10}%"


private def isNativeComputeAxiom (n : Name) : Bool :=
  match (toString n).splitOn "._native." with
  | [_] => false
  | _   => true

private def hasNativeCompute (ax : Array Name) : Bool :=
  ax.contains ``Lean.trustCompiler || ax.any isNativeComputeAxiom

private def normalizeAxiomName (n : Name) : Name :=
  if isNativeComputeAxiom n then `_native_compute
  else if n == ``Lean.trustCompiler then `_native_compute
  else n

private def axiomDisplayName (n : Name) : String :=
  if n == `_native_compute then "native compute (trustCompiler / ._native.*)"
  else toString n


private inductive Severity where
  | error | warn | info | clean
  deriving BEq, Inhabited

private def classifySeverity (ax : Array Name) : Severity :=
  if ax.isEmpty then .clean
  else if ax.contains ``sorryAx then .error
  else if ax.contains ``Classical.choice || hasNativeCompute ax then .warn
  else .info

private def severityMark : Severity → String
  | .error => "✗" | .warn => "⚠" | .info => "·" | .clean => "✓"


private abbrev HopEntry := Name × Array Name × Array Name

private def scanOneHop (env : Environment) (cache : AxiomCache)
    (n : Name) (ax : Array Name) :
    CommandElabM (Array HopEntry × AxiomCache) := do
  match env.find? n with
  | none => return (#[], cache)
  | some ci =>
    let typeConsts := ci.type.getUsedConstants
    let valueConsts := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants | none => #[]
    let mut result : Array HopEntry := #[]
    let mut cache := cache
    for a in ax do
      let mut tSrc : Array Name := #[]
      let mut vSrc : Array Name := #[]
      for d in typeConsts do
        if d == n then continue
        let (dax, c) ← cachedCollect cache d; cache := c
        if dax.contains a then tSrc := tSrc.push d
      for d in valueConsts do
        if d == n || tSrc.contains d then continue
        let (dax, c) ← cachedCollect cache d; cache := c
        if dax.contains a then vSrc := vSrc.push d
      result := result.push (a, tSrc, vSrc)
    return (result, cache)


private structure AuditEntry where
  name     : Name
  axioms   : Array Name
  severity : Severity
  kind     : String
  line?    : Option Nat
  module?  : Option Name
  oneHop   : Array HopEntry


private def countPerAxiom (entries : Array AuditEntry) : Array (Name × Nat) := Id.run do
  let mut counts : Array (Name × Nat) := #[]
  for e in entries do
    for a in e.axioms do
      let key := normalizeAxiomName a
      match counts.findIdx? (fun p => p.1 == key) with
      | some idx => counts := counts.modify idx fun (n, c) => (n, c + 1)
      | none => counts := counts.push (key, 1)
  return counts.qsort fun a b => a.2 > b.2

private def aggregateSources (entries : Array AuditEntry) :
    Array (Name × Array (Name × Nat)) := Id.run do
  let mut raw : Array (Name × Name × Nat) := #[]
  for e in entries do
    for (a, tSrc, vSrc) in e.oneHop do
      let key := normalizeAxiomName a
      for d in tSrc ++ vSrc do
        match raw.findIdx? (fun t => t.1 == key && t.2.1 == d) with
        | some idx => raw := raw.modify idx fun (ax, dn, c) => (ax, dn, c + 1)
        | none => raw := raw.push (key, d, 1)
  let mut axiomNames : Array Name := #[]
  for (a, _, _) in raw do
    unless axiomNames.contains a do axiomNames := axiomNames.push a
  let mut result : Array (Name × Array (Name × Nat)) := #[]
  for a in axiomNames do
    let sources := raw.filter (·.1 == a) |>.map (fun (_, d, c) => (d, c))
    result := result.push (a, sources.qsort fun x y => x.2 > y.2)
  return result.qsort fun a b =>
    a.2.foldl (fun acc p => acc + p.2) 0 > b.2.foldl (fun acc p => acc + p.2) 0


private def fmtDeclDetail (e : AuditEntry) : String := Id.run do
  let mark := severityMark e.severity
  let lineStr := match e.line? with | some l => s!"line {l}" | none => "line ?"
  let mut s := s!"  {mark} {e.name} ({lineStr}) [{e.kind}]"
  if e.severity == .clean then return s
  s := s ++ s!"\n    ↦ {e.axioms}"
  for (a, tSrc, vSrc) in e.oneHop do
    let mut parts : Array String := #[]
    unless tSrc.isEmpty do
      parts := parts.push s!"{String.intercalate ", " (tSrc.toList.map toString)} (type)"
    unless vSrc.isEmpty do
      parts := parts.push s!"{String.intercalate ", " (vSrc.toList.map toString)} (value)"
    if parts.isEmpty then
      s := s ++ s!"\n    ← {a}: [direct reference]"
    else
      s := s ++ s!"\n    ← {a}: {String.intercalate "; " parts.toList}"
  return s


private def fmtModuleReport (modName : Name) (entries : Array AuditEntry) : String := Id.run do
  let path := moduleToPath modName
  let nErr := entries.filter (·.severity == .error) |>.size
  let nWrn := entries.filter (·.severity == .warn)  |>.size
  let nInf := entries.filter (·.severity == .info)  |>.size
  let nCln := entries.filter (·.severity == .clean) |>.size
  let mut parts : Array String := #[]
  if nErr > 0 then parts := parts.push s!"{nErr} error"
  if nWrn > 0 then parts := parts.push s!"{nWrn} warn"
  if nInf > 0 then parts := parts.push s!"{nInf} dep"
  if nCln > 0 then parts := parts.push s!"{nCln} clean"
  let mut s := s!"{path}\n"
  s := s ++ s!"  {modName}\n"
  s := s ++ s!"  {entries.size} declarations ({String.intercalate ", " parts.toList})\n"
  let depEntries := entries.filter (·.severity != .clean)
  let clnEntries := entries.filter (·.severity == .clean)
  for e in depEntries do
    s := s ++ s!"\n{fmtDeclDetail e}"
  if !clnEntries.isEmpty then
    s := s ++ s!"\n  Clean ({clnEntries.size}):"
    for e in clnEntries do
      let lineStr := match e.line? with | some l => s!"line {l}" | none => "line ?"
      s := s ++ s!"\n  ✓ {e.name} ({lineStr}) [{e.kind}]"
  return s


private def knownAxioms : Array Name :=
  #[``sorryAx, `_native_compute, ``Classical.choice, ``propext, ``Quot.sound, ``funext]


elab "#mr_audit_axioms" : command => do
  let env ← getEnv
  let names := sortedAuditedDeclNames env

  let mut cache : AxiomCache := {}
  let mut allEntries : Array AuditEntry := #[]

  for n in names do
    let (ax, c) ← cachedCollect cache n; cache := c
    let sev := classifySeverity ax
    let (hops, c2) ← if ax.isEmpty then pure (#[], cache) else scanOneHop env cache n ax
    cache := c2
    let ranges? ← findDeclarationRanges? n
    let kind := match env.find? n with | some ci => constInfoKind ci | none => "unknown"
    allEntries := allEntries.push {
      name := n, axioms := ax, severity := sev, kind := kind,
      line? := declLine? ranges?, module? := declModuleName? env n,
      oneHop := hops }

  for e in allEntries do
    if e.severity == .error then
      logError m!"[Audit][error] {e.name} ↦ {e.axioms}"
    if e.severity == .warn then
      logWarning m!"[Audit][warn] {e.name} ↦ {e.axioms}"

  let mut modList : Array Name := #[]
  for e in allEntries do
    let m := e.module?.getD `_unknown
    unless modList.contains m do modList := modList.push m

  let sortedMods := modList.qsort fun a b => Id.run do
    let aE := allEntries.filter fun e => e.module?.getD `_unknown == a
    let bE := allEntries.filter fun e => e.module?.getD `_unknown == b
    let aw := aE.foldl (fun acc e => acc + match e.severity with
      | .error => 10000 | .warn => 100 | .info => 1 | .clean => 0) 0
    let bw := bE.foldl (fun acc e => acc + match e.severity with
      | .error => 10000 | .warn => 100 | .info => 1 | .clean => 0) 0
    return aw > bw

  for mn in sortedMods do
    let modEntries := allEntries.filter fun e => e.module?.getD `_unknown == mn
    let modEntries := modEntries.qsort fun a b =>
      let sa := match a.severity with | .error => 0 | .warn => 1 | .info => 2 | .clean => 3
      let sb := match b.severity with | .error => 0 | .warn => 1 | .info => 2 | .clean => 3
      if sa != sb then sa < sb
      else match a.line?, b.line? with
        | some la, some lb => la < lb
        | _, _ => Name.cmp a.name b.name == Ordering.lt
    logInfo m!"{fmtModuleReport mn modEntries}"

  let total := names.size
  let errorE := allEntries.filter (·.severity == .error)
  let warnE  := allEntries.filter (·.severity == .warn)
  let infoE  := allEntries.filter (·.severity == .info)
  let cleanE := allEntries.filter (·.severity == .clean)
  let dep := errorE.size + warnE.size + infoE.size
  let axiomCounts := countPerAxiom allEntries
  let sources := aggregateSources allEntries

  let mut summary := s!"════════════ Project Summary ════════════\n"
  summary := summary ++ s!"{total} declarations, {modList.size} modules\n"
  summary := summary ++ s!"\nAxiom Profile:\n"
  for ka in knownAxioms do
    match axiomCounts.find? (fun p => p.1 == ka) with
    | some (_, c) =>
      let mark := if ka == ``sorryAx || ka == `_native_compute || ka == ``Classical.choice
                  then "✗" else "·"
      summary := summary ++ s!"  {mark} {axiomDisplayName ka}: {c} decl ({pct c total})\n"
    | none =>
      summary := summary ++ s!"  ✓ {axiomDisplayName ka}: not used\n"
  for (a, c) in axiomCounts do
    unless knownAxioms.contains a do
      summary := summary ++ s!"  ? {a}: {c} decl ({pct c total}) [unexpected]\n"
  summary := summary ++ s!"\nHealth:\n"
  summary := summary ++ s!"  Incomplete proofs (sorryAx):     " ++
    (if errorE.isEmpty then "✓ none\n" else s!"✗ {errorE.size} — build blocked\n")
  summary := summary ++ s!"  Non-constructive (choice/native): " ++
    (if warnE.isEmpty then "✓ none\n" else s!"⚠ {warnE.size}\n")
  summary := summary ++ s!"  Axiom-dependent:                 {dep} ({pct dep total})\n"
  summary := summary ++ s!"  Axiom-free:                      {cleanE.size} ({pct cleanE.size total})\n"
  summary := summary ++ s!"\nRoot Causes (one-hop axiom sources):\n"
  for (a, srcs) in sources do
    let top := srcs.toSubarray 0 (min 8 srcs.size)
    let more := if srcs.size > 8 then s!" ... and {srcs.size - 8} more" else ""
    summary := summary ++ s!"\n  {axiomDisplayName a}:\n"
    for (d, c) in top do
      summary := summary ++ s!"    {d} → {c} decl\n"
    unless more.isEmpty do
      summary := summary ++ s!"   {more}\n"

  if errorE.size > 0 then logError m!"{summary}"
  else if warnE.size > 0 then logWarning m!"{summary}"
  else logInfo m!"{summary}"

end GasperBeaconChain.Audit.Meta