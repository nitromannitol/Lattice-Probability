/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPNormalizer at commit fdb5cad; only the module paths of local imports are changed. -/
-- FROZEN_ANCHOR_PREFIX_BEGIN
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Implementation.ExistsUnique_isLFPPNormalizer

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `existsUnique_isLFPPNormalizer`. Its proof body is the registered DRAFT_SORRY placeholder until the two-key seal. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- DG (1.4), l. 295–299: for every `ξ > 0` and `ε > 0` the LFPP normalizing factor `𝔞_ε` is
well defined, i.e. there is exactly one positive real that is a median of the left–right
crossing distance of `[0,1]²` for every realization of the normalized whole-plane GFF and every
continuous version of `h*_ε`. This is the well-definedness theorem of the characterized object
`𝔞_ε` ("the median"); with it, `IsLFPPNormalizer ξ ε` pins DG's `𝔞_ε`. -/
theorem existsUnique_isLFPPNormalizer :
    ∀ ξ ε : Set.Ioi (0 : ℝ), ∃! a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalLQGUniqueness.Implementation.existsUnique_isLFPPNormalizer_impl
-- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalLQGUniqueness
-- FROZEN_ANCHOR_SUFFIX_END
