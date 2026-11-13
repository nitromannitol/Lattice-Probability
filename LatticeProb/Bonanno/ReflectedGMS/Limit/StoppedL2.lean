/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedL2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.FiniteStopping
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingApproximation
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedAdaptedness
import Mathlib.MeasureTheory.Function.L2Space

/-!
L² control for actual stopped values and stopped processes. Finite grid
approximations reuse the conditional-expectation estimate in `FiniteStopping`;
Fatou's lemma passes that uniform terminal second-moment bound to the actual
right-continuous stopped value. No optional-sampling or local-to-true-martingale
principle is reimplemented here.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Terminal L² integrability controls an actual bounded stopped value, including
stopping at zero and at the terminal horizon. -/
theorem bounded_stopping_memLp_two_and_second_moment_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (h2T : MemLp (M T) 2 P) :
    MemLp (stoppedValue M τ) 2 P ∧
      (∫ ω, (stoppedValue M τ ω) ^ 2 ∂P) ≤ ∫ ω, (M T ω) ^ 2 ∂P := by
  let Y : ℕ → Ω → ℝ := fun n => stoppedValue M (boundedGridApprox τ T n)
  let Z : Ω → ℝ := fun ω => (stoppedValue M τ ω) ^ 2
  have hYn (n : ℕ) : MemLp (Y n) 2 P :=
    finite_stopping_memLp_two hM
      (isStoppingTime_boundedGridApprox hτ T hτT n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2) h2T
  have hYle (n : ℕ) :
      (∫ ω, (Y n ω) ^ 2 ∂P) ≤ ∫ ω, (M T ω) ^ 2 ∂P :=
    finite_stopping_second_moment_le hM
      (isStoppingTime_boundedGridApprox hτ T hτT n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2) h2T
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => (Y n ω) ^ 2) atTop (𝓝 (Z ω)) :=
    hr.mono fun ω hω =>
      (boundedGridApprox_stoppedValue_tendsto M T hτT ω hω).pow 2
  have hmeas (n : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal ((Y n ω) ^ 2)) P :=
    by
      simpa only [pow_two, Pi.mul_apply] using
        ((hYn n).aestronglyMeasurable.mul
          (hYn n).aestronglyMeasurable).aemeasurable.ennreal_ofReal
  have hfatou :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P) ≤
        Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂P) atTop := by
    have hliminf : ∀ᵐ ω ∂P,
        Filter.liminf (fun n => ENNReal.ofReal ((Y n ω) ^ 2)) atTop =
          ENNReal.ofReal (Z ω) :=
      hconv.mono fun ω hω =>
        ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq
    rw [← lintegral_congr_ae hliminf]
    exact lintegral_liminf_le' hmeas
  have hbound (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂P) ≤
        ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hYn n).integrable_sq
      (Eventually.of_forall fun ω => sq_nonneg (Y n ω))]
    exact ENNReal.ofReal_le_ofReal (hYle n)
  have hlin :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P) ≤
        ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) :=
    hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
  have hZmeas : AEStronglyMeasurable Z P :=
    by
      apply aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (hYn n).aestronglyMeasurable.mul (hYn n).aestronglyMeasurable)
      simpa only [pow_two, Pi.mul_apply] using hconv
  have hZint : Integrable Z P := by
    refine ⟨hZmeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have htop : ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) < ⊤ := ENNReal.ofReal_lt_top
    calc
      (∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂P) = ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P := by
        apply lintegral_congr
        intro ω
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact sq_nonneg _
      _ ≤ ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := hlin
      _ < ⊤ := htop
  have hstopmeas : AEStronglyMeasurable (stoppedValue M τ) P := by
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hYn n).aestronglyMeasurable)
      (hr.mono fun ω hω => boundedGridApprox_stoppedValue_tendsto M T hτT ω hω)
  have hstop2 : MemLp (stoppedValue M τ) 2 P :=
    (memLp_two_iff_integrable_sq hstopmeas).2 hZint
  refine ⟨hstop2, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg (fun ω => sq_nonneg (M T ω)))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hZint
      (Eventually.of_forall fun ω => sq_nonneg (stoppedValue M τ ω))]
  exact hlin

/-- At each deterministic time, stopping at an arbitrary real stopping time
preserves L² and does not increase the terminal second moment. -/
theorem stoppedProcess_memLp_two_and_second_moment_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (t : ℝ≥0) (h2t : MemLp (M t) 2 P) :
    MemLp (stoppedProcess M τ t) 2 P ∧
      (∫ ω, (stoppedProcess M τ t ω) ^ 2 ∂P) ≤ ∫ ω, (M t ω) ^ 2 ∂P := by
  exact bounded_stopping_memLp_two_and_second_moment_le hM
    ((isStoppingTime_const F t).min hτ) t (fun _ => min_le_left _ _) hr h2t

end ReflectedGMS.MartingaleLimit
