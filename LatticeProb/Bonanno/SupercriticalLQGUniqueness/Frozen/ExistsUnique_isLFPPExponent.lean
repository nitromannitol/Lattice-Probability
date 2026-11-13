/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent at commit fdb5cad; only the module paths of local imports are changed. -/
-- FROZEN_ANCHOR_PREFIX_BEGIN
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Implementation.ExistsUnique_isLFPPExponent

/-! Scratch freeze split of SLURoots.lean:27. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont)

namespace SupercriticalLQGUniqueness

/-- DG l. 330–333: for every positive `ξ`, this asserts existence and uniqueness
of the exponent `Q` characterized by the LFPP asymptotic (1.5). DG20's
additional assertion `Q > 0` is not part of this declaration. This is the
first of the two A9 root anchors. -/
theorem existsUnique_isLFPPExponent :
    ∀ ξ : Set.Ioi (0 : ℝ), ∃! Q : ℝ, IsLFPPExponent ξ Q :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalLQGUniqueness.Implementation.existsUnique_isLFPPExponent_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalLQGUniqueness
-- FROZEN_ANCHOR_SUFFIX_END
