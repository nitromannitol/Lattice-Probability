/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalH3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalCorrected
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PointP48

/-!
# The corrected local factor of Proposition 4.8

The reconstruction reconstructs the geometric all-visit point factor from the small
thickened field. The conditioning circles are included separately at their
actual radius. the bundle construction already reconstructs the primed Lemma 4.3 event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- the factor supplies the entire repaired H3 from the GMC readers.
The circle-average condition remains outside the local factor. -/
def prop48_primedBorelLocalFactor_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ : ℝ)
    (H2 : ThickGMCReaders D) :
    Prop48PrimedBorelLocalFactorInput D hγ q ζ H2 := by
  refine ⟨?_⟩
  intro ε hε z
  obtain ⟨f, hf, heq⟩ :=
    GMS4cP.l43p_maskedUStarPrime_of_readers D hγ H2 hε q ζ z
  refine ⟨f, hf, ?_⟩
  change ∀ᵐ ω ∂P, maskedUStarPrime D hγ ε q ζ z ω =
    (if max |fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
        |igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
        2 * q * Real.log ε⁻¹ then f
      (((H2 (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q)
        (Real.rpow_pos_of_pos hε.1 q)).reconstruct
          (LQGMetric.restrictTo
            (GMS4c.thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q))
            (coneField (X₀ ω) (coneRadial γ 0
              (fun t => B₀ t ω) (fun t => B₀' t ω)))),
        LQGMetric.restrictTo
          (GMS4c.thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q))
          (coneField (X₀ ω) (coneRadial γ 0
            (fun t => B₀ t ω) (fun t => B₀' t ω)))),
        (LQGMetric.restrictTo
          (GMS4c.thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q))
          (hIG₀ ω), U ω)) else 0)
  filter_upwards [heq] with ω hω
  convert hω using 1
  by_cases hc : max |fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
      |igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
        2 * q * Real.log ε⁻¹
  · simp [GMS4cP.circleCond, hc]
  · simp [GMS4cP.circleCond, hc]

end MatedCRTHarmonic.GMS4.Canonical

