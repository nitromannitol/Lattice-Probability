/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalCorrected at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalRegularitySpatial

/-!
# Source-corrected canonical Proposition 4.8 interface

The only remaining analytic input is the good-event second moment (4.38).
The regularity exponent is supplied by Proposition 4.5 before the radius;
The jointly measurable conditional mean and spatial Fubini statements are
checked independently. Source: [18, Proposition 4.8].
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- A bounded test's (4.38) rate implies the Chebyshev-ready rate whenever
The final exponent is at most one quarter of the source variance exponent. -/
theorem prop48_variance_rate_le_tail
    {ε α α₀ C N : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hα : 0 ≤ α) (hα₀ : 4 * α ≤ α₀) (hC : 0 ≤ C) :
    C * ε ^ α₀ * N ^ 2 ≤
      (ε ^ α * N) ^ 2 * (C * ε ^ α) := by
  have hpow : ε ^ α₀ ≤ ε ^ (3 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (by linarith)
  have hnonneg : 0 ≤ C * N ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hrpow : ε ^ (3 * α) = (ε ^ α) ^ 3 := by
    rw [pow_three, ← Real.rpow_add hε.1, ← Real.rpow_add hε.1]
    congr 1
    ring
  calc
    C * ε ^ α₀ * N ^ 2 = (C * N ^ 2) * ε ^ α₀ := by ring
    _ ≤ (C * N ^ 2) * ε ^ (3 * α) :=
      mul_le_mul_of_nonneg_left hpow hnonneg
    _ = (ε ^ α * N) ^ 2 * (C * ε ^ α) := by rw [hrpow]; ring

end MatedCRTHarmonic.GMS4.Canonical

