/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48FarProduct at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ProducerInterfaces

/-!
# The exterior conditioning identity in Proposition 4.8

The distant point is measurable for the exterior field sigma algebra. This
identity is the conditional-expectation step in [18] (4.36), with the global
good-event indicator absent as required by the unconditional second-moment expansion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MatedCRTHarmonic.GMS4

/-- The covariance identity in [18] (4.36). `A` is the local-circle
conditional mean; the exterior projection acts only on the uncentered
truncated observable `Y`. -/
theorem prop48_integral_centered_far_eq
    {Ω : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ m₀) {Y Z A : Ω → ℝ}
    (hY : Integrable Y P) (hYZ : Integrable (Y * Z) P)
    (hAZ : Integrable (A * Z) P)
    (hZ : StronglyMeasurable[m] Z) :
    ∫ ω, (Y ω - A ω) * Z ω ∂P =
      ∫ ω, (P[Y | m] ω - A ω) * Z ω ∂P := by
  have hpull : P[Y * Z | m] =ᵐ[P] P[Y | m] * Z :=
    condExp_mul_of_stronglyMeasurable_right hZ hYZ hY
  have hproj : ∫ ω, Y ω * Z ω ∂P =
      ∫ ω, P[Y | m] ω * Z ω ∂P := by
    calc
      _ = ∫ ω, P[Y * Z | m] ω ∂P :=
        (integral_condExp (μ := P) (f := Y * Z) hm).symm
      _ = _ := integral_congr_ae hpull
  have hCEYZ : Integrable (P[Y | m] * Z) P :=
    integrable_condExp.congr hpull
  have hleft : (fun ω => (Y ω - A ω) * Z ω) = Y * Z - A * Z := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hright : (fun ω => (P[Y | m] ω - A ω) * Z ω) =
      P[Y | m] * Z - A * Z := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hleft, hright]
  change (∫ ω, (Y * Z) ω - (A * Z) ω ∂P) =
    ∫ ω, (P[Y | m] * Z) ω - (A * Z) ω ∂P
  rw [integral_sub hYZ hAZ, integral_sub hCEYZ hAZ]
  simpa only [Pi.mul_apply] using
    congrArg (fun t : ℝ => t - ∫ ω, A ω * Z ω ∂P) hproj

/-- Hölder's inequality applied to the exterior projection difference. This
is the analytic core of [18] (4.36), before substituting the A.3 and Lemma
4.9 moment bounds. -/
theorem prop48_integral_centered_far_holder
    {Ω : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ m₀) {Y Z A : Ω → ℝ}
    (hY : Integrable Y P) (hYZ : Integrable (Y * Z) P)
    (hAZ : Integrable (A * Z) P)
    (hZ : StronglyMeasurable[m] Z) (hA : AEMeasurable A P)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ENNReal.ofReal |∫ ω, (Y ω - A ω) * Z ω ∂P| ≤
      (∫⁻ ω, ENNReal.ofReal |P[Y | m] ω - A ω| ^ p ∂P) ^ (1 / p) *
        (∫⁻ ω, ENNReal.ofReal |Z ω| ^ q ∂P) ^ (1 / q) := by
  have hcov := prop48_integral_centered_far_eq (P := P) (m := m) hm hY hYZ hAZ hZ
  have hF : AEMeasurable
      (fun ω => ENNReal.ofReal |P[Y | m] ω - A ω|) P :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable
        ((stronglyMeasurable_condExp.mono hm).measurable.aemeasurable.sub hA)))
  have hG : AEMeasurable (fun ω => ENNReal.ofReal |Z ω|) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable
        (hZ.mono hm).measurable.aemeasurable)
  calc
    ENNReal.ofReal |∫ ω, (Y ω - A ω) * Z ω ∂P| =
        ‖∫ ω, (Y ω - A ω) * Z ω ∂P‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
    _ = ‖∫ ω, (P[Y | m] ω - A ω) * Z ω ∂P‖ₑ := by rw [hcov]
    _ ≤ ∫⁻ ω, ‖(P[Y | m] ω - A ω) * Z ω‖ₑ ∂P :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ENNReal.ofReal |P[Y | m] ω - A ω| *
        ENNReal.ofReal |Z ω| ∂P := by
          apply lintegral_congr
          intro ω
          rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    _ ≤ (∫⁻ ω, ENNReal.ofReal |P[Y | m] ω - A ω| ^ p ∂P) ^ (1 / p) *
        (∫⁻ ω, ENNReal.ofReal |Z ω| ^ q ∂P) ^ (1 / q) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hF hG

end MatedCRTHarmonic.GMS4

