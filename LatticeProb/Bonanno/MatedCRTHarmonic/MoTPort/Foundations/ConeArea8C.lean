/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea8C at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea8B
import Mathlib

/-!
# Cone area, part 23: the cone mass bounds; `IsQuantumCone` is self-guarding

**`coneMassBounds`**: `ConeArea7.ConeMassBounds γ W` for `0 < γ < 2`, `W > 0`; hence
**`coneScalePos`**, **`coneRefNonDirac`** and **`isQuantumCone_iff_unguarded'`** (the guard-free
characterization of `IsQuantumCone`, DMS Def. 4.10: the law identity alone).

Proof of the big-ball half (positive probability is enough). Off the origin the cone field is
`X + g`, `g(z) = Q s + A_s − R(|z|)`, `s = −log|z|` (ConeArea3B), so its area measure is
`e^{γ g} μ_X` (ConeArea3B `isVagueLimitOn_coneField_punctured` and uniqueness of vague limits).
On the support of the bump `bumpW` (ConeArea8B) we have `s ∈ [1/5, 3/2]`, hence if `A ≥ M` on
`[1/5, 3/2]`:

  `μ_cone(B(0,1)) ≥ ∫ bumpW dμ_cone ≥ e^{γM} massLat(X)`,

where `massLat γ x` is `massW` of the cone field with zero radial profile (the lateral part of `x`;
a measurable functional of `x` alone, a.s. positive by `ae_massW_pos`). The events
`{massLat(X) > 1/(n+1)}` (for some `n`, positive probability) and `{A ≥ log(n+1)/γ on
[1/5, 3/2] ∩ ℚ}` (positive probability: `B_{1/5}` is Gaussian and independent of the later
increments, mathlib `IsPreBrownianReal.indepFun_shift`) are independent (`X ⫫ A`), so their
intersection has positive probability, and on it some ball has cone mass `≥ 1`. The small-ball
half is `ae_exists_ball_lt_one` (ConeArea8).

Own argument (no published proof of this soft fact was found; DMS Def. 4.10 uses the unit-mass
circle-average embedding without comment). It needs only positive probability, so the
dyadic-scaling route of QZ `WedgeInfTotal` (a.s. infinite total mass) is not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea8

open QuantumZipper LQGMetric ConeArea4

/-! ## Brownian motion above a level on a compact time interval -/

section BM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

end BM

/-! ## Geometry of the bump support -/

/-! ## The lateral functional and the comparison -/

lemma measurable_expDens {a : ℝ → ℝ} (ha : Measurable a) (γ Q : ℝ) {R : ℝ → ℝ}
    (hR : Measurable R) :
    Measurable fun z => ENNReal.ofReal (Real.exp (γ * ConeArea3.coneShift a Q R z)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((ConeArea3.measurable_coneShift ha Q hR).const_mul γ))

/-! ## The mass bounds -/

end ConeArea8
end MatedCRTHarmonic.MoTPort
