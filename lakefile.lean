import Lake
open Lake DSL

package «lattice-probability» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- On the `lean-v4.35` line the v4.32 modules of `LatticeProb` are not ported; this library is built only on demand. -/
lean_lib «LatticeProb» where
  globs := #[.andSubmodules `LatticeProb]

/-- The `lean-v4.35` line (Lean v4.35.0-rc2, the Mathlib of the harmonic-balls and mated-CRT formalizations): the LQG, GFF and
mated-CRT library, adapted from Leonardo Bonanno's lean-formalizations (each file names its source module). -/
@[default_target]
lean_lib «LatticeProbV435» where
  roots := #[`LatticeProb.V435]
  globs := #[.andSubmodules `LatticeProb.LQG, .andSubmodules `LatticeProb.MatedCRT, .andSubmodules `LatticeProb.Bonanno]

/-- The comparator audit surface (`LatticeProbAudit/`): Mathlib-only challenges, their
solutions, and the vocabulary and bridge modules the solutions use.  Not a default target: it
builds only on demand (`lake build LatticeProbAudit`), so the ordinary build of `LatticeProb`,
and the build of every repository that requires this library, is unchanged.  The modules live
under the distinct root `LatticeProbAudit` so that they cannot collide with the audit modules of
a dependent repository. -/
lean_lib «LatticeProbAudit» where
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
