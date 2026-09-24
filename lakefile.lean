import Lake
open Lake DSL

package «lattice-probability» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «LatticeProb» where
  globs := #[.andSubmodules `LatticeProb]

/-- The comparator audit surface (`Audit/LatticeProbAudit/`): Mathlib-only challenges, their
solutions, and the statement regression.  Not a default target: it builds only on demand
(`lake build LatticeProbAudit`), so the ordinary build of `LatticeProb`, and the build of every
repository that requires this library, is unchanged.  The modules live under the distinct root
`LatticeProbAudit` so that they cannot collide with the `Audit.*` modules of a dependent
repository. -/
lean_lib «LatticeProbAudit» where
  srcDir := "Audit"
  globs := #[.submodules `LatticeProbAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
