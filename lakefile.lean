import Lake
open Lake DSL

package «GasperBeaconChain» where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

require verso from git "https://github.com/leanprover/verso.git" @ "v4.31.0"

-- subverso for export
-- require subverso from git "https://github.com/leanprover/subverso" @ "0bd508e8362f56d4a05cbf63614d4c97db954041"

/-- デバッグ／証明詳細化オプション -/
def debugLeanOptions : Array LeanOption := #[
  ⟨`doc.verso, true⟩,
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`pp.universes, true⟩,
  ⟨`pp.tagAppFns, true⟩,
  ⟨`pp.proofs, true⟩,
  ⟨`pp.proofs.withType, true⟩,
  ⟨`pp.mvars, true⟩,
  ⟨`pp.coercions, true⟩,
  ⟨`pp.coercions.types, true⟩,
  ⟨`pp.letVarTypes, true⟩,
  ⟨`pp.motives.all, true⟩,
  ⟨`pp.numericTypes, true⟩,
  ⟨`pp.raw.showInfo, true⟩,
  ⟨`pp.piBinderNames, true⟩,
  ⟨`pp.piBinderTypes, true⟩,
  ⟨`pp.instanceTypes, true⟩,
  ⟨`pp.showLetValues, true⟩,
  ⟨`pp.funBinderTypes, true⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`pp.structureInstanceTypes, true⟩,
  ⟨`pp.structureInstances.defaults, true⟩,
  ⟨`pp.beta, false⟩,
  ⟨`pp.notation, true⟩,
  ⟨`pp.fieldNotation, true⟩,
  ⟨`pp.structureInstances, true⟩,
  ⟨`pp.structureInstances.flatten, false⟩,
  ⟨`weak.diagnostics, true⟩,
  ⟨`weak.pp.numericProj.prod, true⟩,
  ⟨`weak.linter.style.show, true⟩,
  ⟨`weak.linter.unusedTactic, true⟩,
  ⟨`weak.linter.unusedVariables, true⟩,
  ⟨`weak.linter.unusedSectionVars, true⟩
]

/-- 既定（通常）ビルド用の最小オプション -/
def defaultLeanOptions : Array LeanOption := #[
  ⟨`doc.verso, true⟩,
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`pp.tagAppFns, true⟩,
  ⟨`pp.letVarTypes, true⟩,
  ⟨`pp.numericTypes, true⟩,
  ⟨`pp.instanceTypes, true⟩,
  ⟨`pp.showLetValues, true⟩,
  ⟨`pp.funBinderTypes, true⟩,
  ⟨`pp.structureInstanceTypes, true⟩,
  ⟨`pp.beta, false⟩,
  ⟨`pp.proofs, false⟩,
  ⟨`pp.proofs.withType, true⟩,
  ⟨`pp.notation, true⟩,
  ⟨`pp.fieldNotation, true⟩,
  ⟨`pp.structureInstances, true⟩,
]

@[default_target]
lean_lib «GasperBeaconChain» where
  leanOptions :=
    if (get_config? mode) == some "debug" then debugLeanOptions else defaultLeanOptions

lean_exe gasperbeaconchain where
  root := `Main
