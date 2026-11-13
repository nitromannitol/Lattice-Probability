/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.Frozen.DistExp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.Frozen.IsDistanceExponent

/-!
# Frozen definition: `distExp`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M7, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 50, 92–93; ruling M7: `Q(ξ)`, the exponent of `IsDistanceExponent` (`Classical.choose`; junk value
`0` if none exists). The frozen characterization `distExp_spec` states that for `d ≥ 2`, `ξ > 0`,
`IsDistanceExponent d ξ Q ↔ Q = distExp d ξ` (existence, kernel independence and uniqueness), so the
choice is canonical and the junk branch is never taken where the theorems use `distExp`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

open Classical in
/-- `Q(ξ)`: the kernel-independent LFPP distance exponent (junk `0` if it does not exist; excluded for
`d ≥ 2`, `ξ > 0` by `distExp_spec`). -/
def distExp (d : ℕ) (ξ : ℝ) : ℝ :=
  if hQ : ∃ Q : ℝ, IsDistanceExponent d ξ Q then hQ.choose else 0

end HigherDimLQGMetric
