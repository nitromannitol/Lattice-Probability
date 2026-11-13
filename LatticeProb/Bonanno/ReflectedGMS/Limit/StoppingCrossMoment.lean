/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppingCrossMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedGridL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
Cross moments at two bounded stopping times.  Optional sampling is first used on
common finite grids.  The resulting identity passes to the actual stopped
values through the checked L² convergence and continuity of the L² inner
product.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Rounding upward on a fixed grid is monotone in the stopping value. -/
theorem upperGrid_mono (n : ℕ) {x y : ℝ≥0} (hxy : x ≤ y) :
    upperGrid n x ≤ upperGrid n y := by
  unfold upperGrid
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.2 (Nat.ceil_mono (mul_le_mul_of_nonneg_right hxy zero_le))) zero_le

/-- Common bounded grids preserve a pointwise ordering of stopping times. -/
theorem boundedGridApprox_mono {σ τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hσT : ∀ ω, σ ω ≤ T) (hτT : ∀ ω, τ ω ≤ T)
    (hστ : ∀ ω, σ ω ≤ τ ω) (n : ℕ) (ω : Ω) :
    boundedGridApprox σ T n ω ≤ boundedGridApprox τ T n ω := by
  apply min_le_min_right
  norm_cast
  apply upperGrid_mono
  have hσne : σ ω ≠ ⊤ := ne_top_of_le_ne_top
    (WithTop.coe_ne_top : (T : WithTop ℝ≥0) ≠ ⊤) (hσT ω)
  have hτne : τ ω ≠ ⊤ := ne_top_of_le_ne_top
    (WithTop.coe_ne_top : (T : WithTop ℝ≥0) ≠ ⊤) (hτT ω)
  apply (WithTop.untopA_le_iff hσne).2
  simpa [WithTop.untopA_eq_untop hτne, WithTop.coe_untop] using hστ ω

private theorem inner_toLp_real_eq_integral_mul
    {P : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [RCLike.inner_apply, conj_trivial, hfω, hgω]
  exact mul_comm _ _

private theorem finite_stopping_cross_moment
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hσfin : (Set.range σ).Finite) (hτfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (h2T : MemLp (M T) 2 P) :
    (∫ ω, stoppedValue M σ ω * stoppedValue M τ ω ∂P) =
      ∫ ω, (stoppedValue M σ ω) ^ 2 ∂P := by
  let S := stoppedValue M σ
  let U := stoppedValue M τ
  have hS2 : MemLp S 2 P := finite_stopping_memLp_two hM hσ hσfin T
    (fun ω => (hστ ω).trans (hτT ω)) h2T
  have hU2 : MemLp U 2 P := finite_stopping_memLp_two hM hτ hτfin T hτT h2T
  have hSU : Integrable (S * U) P := hS2.integrable_mul hU2
  have hSS : Integrable (S * S) P := hS2.integrable_mul hS2
  have hU1 : Integrable U P := hU2.integrable one_le_two
  have he : S =ᵐ[P] P[U | hσ.measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ hσ hστ hτT
      hτfin.countable hσfin.countable
  have hc : AEStronglyMeasurable[hσ.measurableSpace]
      P[U | hσ.measurableSpace] P := stronglyMeasurable_condExp.aestronglyMeasurable
  have hSmeas : AEStronglyMeasurable[hσ.measurableSpace] S P := hc.congr he.symm
  calc
    (∫ ω, S ω * U ω ∂P) = ∫ ω, P[S * U | hσ.measurableSpace] ω ∂P :=
      (integral_condExp hσ.measurableSpace_le).symm
    _ = ∫ ω, S ω * P[U | hσ.measurableSpace] ω ∂P :=
      integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left hSmeas hSU hU1)
    _ = ∫ ω, S ω * S ω ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
    _ = ∫ ω, (S ω) ^ 2 ∂P := by simp only [pow_two]

/-- For `σ ≤ τ ≤ T`, the cross moment of the two actual stopped values equals
the second moment at the earlier stopping time.  The first component records
the L¹ integrability needed by later bracket calculations. -/
theorem bounded_stopping_cross_moment
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (h2T : MemLp (M T) 2 P) :
    Integrable (stoppedValue M σ * stoppedValue M τ) P ∧
      (∫ ω, stoppedValue M σ ω * stoppedValue M τ ω ∂P) =
        ∫ ω, (stoppedValue M σ ω) ^ 2 ∂P := by
  let S : ℕ → Ω → ℝ := fun n => stoppedValue M (boundedGridApprox σ T n)
  let U : ℕ → Ω → ℝ := fun n => stoppedValue M (boundedGridApprox τ T n)
  let s := stoppedValue M σ
  let u := stoppedValue M τ
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hστ ω).trans (hτT ω)
  have hs2 : MemLp s 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le hM hσ T hσT hr h2T).1
  have hu2 : MemLp u 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le hM hτ T hτT hr h2T).1
  have hS2 (n : ℕ) : MemLp (S n) 2 P := finite_stopping_memLp_two hM
    (isStoppingTime_boundedGridApprox hσ T hσT n)
    (finite_range_boundedGridApprox T hσT n) T
    (fun ω => (boundedGridApprox_bounds T hσT n ω).2) h2T
  have hU2 (n : ℕ) : MemLp (U n) 2 P := finite_stopping_memLp_two hM
    (isStoppingTime_boundedGridApprox hτ T hτT n)
    (finite_range_boundedGridApprox T hτT n) T
    (fun ω => (boundedGridApprox_bounds T hτT n ω).2) h2T
  have hSL2 := boundedGridApprox_stoppedValue_L2 hM hσ T hσT hr h2T
  have hUL2 := boundedGridApprox_stoppedValue_L2 hM hτ T hτT hr h2T
  have hSLp : Tendsto (fun n => (hS2 n).toLp (S n)) atTop (𝓝 (hs2.toLp s)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => S n) hS2 s hs2).2 hSL2
  have hULp : Tendsto (fun n => (hU2 n).toLp (U n)) atTop (𝓝 (hu2.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => U n) hU2 u hu2).2 hUL2
  have hcross : Tendsto (fun n => ∫ ω, S n ω * U n ω ∂P) atTop
      (𝓝 (∫ ω, s ω * u ω ∂P)) := by
    simpa only [inner_toLp_real_eq_integral_mul] using
      (hSLp.inner (𝕜 := ℝ) hULp)
  have hsquare : Tendsto (fun n => ∫ ω, (S n ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (s ω) ^ 2 ∂P)) := by
    simpa only [inner_toLp_real_eq_integral_mul, pow_two] using
      (hSLp.inner (𝕜 := ℝ) hSLp)
  have hfinite (n : ℕ) :
      (∫ ω, S n ω * U n ω ∂P) = ∫ ω, (S n ω) ^ 2 ∂P :=
    finite_stopping_cross_moment hM
      (isStoppingTime_boundedGridApprox hσ T hσT n)
      (isStoppingTime_boundedGridApprox hτ T hτT n)
      (finite_range_boundedGridApprox T hσT n)
      (finite_range_boundedGridApprox T hτT n) T
      (boundedGridApprox_mono T hσT hτT hστ n) 
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2) h2T
  refine ⟨hs2.integrable_mul hu2, ?_⟩
  exact tendsto_nhds_unique hcross
    (hsquare.congr' (Eventually.of_forall fun n => (hfinite n).symm))

/-- The stopped increment has the expected orthogonal-increment second-moment
identity. -/
theorem bounded_stopping_sq_increment_integral
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (h2T : MemLp (M T) 2 P) :
    (∫ ω, (stoppedValue M τ ω - stoppedValue M σ ω) ^ 2 ∂P) =
      (∫ ω, (stoppedValue M τ ω) ^ 2 ∂P) -
        ∫ ω, (stoppedValue M σ ω) ^ 2 ∂P := by
  let s := stoppedValue M σ
  let u := stoppedValue M τ
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hστ ω).trans (hτT ω)
  have hs2 : MemLp s 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le hM hσ T hσT hr h2T).1
  have hu2 : MemLp u 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le hM hτ T hτT hr h2T).1
  have hcross := (bounded_stopping_cross_moment hM hσ hτ T hστ hτT hr h2T).2
  have huu : Integrable (u * u) P := hu2.integrable_mul hu2
  have hss : Integrable (s * s) P := hs2.integrable_mul hs2
  have hus : Integrable (u * s) P := hu2.integrable_mul hs2
  change (∫ ω, (u ω - s ω) ^ 2 ∂P) = (∫ ω, (u ω) ^ 2 ∂P) - ∫ ω, (s ω) ^ 2 ∂P
  change Integrable (fun ω => u ω * u ω) P at huu
  change Integrable (fun ω => s ω * s ω) P at hss
  change Integrable (fun ω => u ω * s ω) P at hus
  have hiadd :
      (∫ ω, (u ω * u ω - 2 * (u ω * s ω)) + s ω * s ω ∂P) =
        (∫ ω, u ω * u ω - 2 * (u ω * s ω) ∂P) + ∫ ω, s ω * s ω ∂P :=
    integral_add (huu.sub (hus.const_mul 2)) hss
  have hisub :
      (∫ ω, u ω * u ω - 2 * (u ω * s ω) ∂P) =
        (∫ ω, u ω * u ω ∂P) - ∫ ω, 2 * (u ω * s ω) ∂P :=
    integral_sub huu (hus.const_mul 2)
  calc
    (∫ ω, (u ω - s ω) ^ 2 ∂P) =
        ∫ ω, (u ω * u ω - 2 * (u ω * s ω)) + s ω * s ω ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      ring
    _ = (∫ ω, u ω * u ω ∂P) - 2 * (∫ ω, u ω * s ω ∂P) +
        ∫ ω, s ω * s ω ∂P := by
      rw [hiadd, hisub, integral_const_mul]
    _ = (∫ ω, u ω * u ω ∂P) - 2 * (∫ ω, s ω * u ω ∂P) +
        ∫ ω, s ω * s ω ∂P := by
      congr 2
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      exact mul_comm _ _
    _ = (∫ ω, u ω * u ω ∂P) - ∫ ω, s ω * s ω ∂P := by
      rw [show (∫ ω, s ω * u ω ∂P) = ∫ ω, s ω * s ω ∂P by
        simpa only [s, u, pow_two] using hcross]
      ring
    _ = (∫ ω, (u ω) ^ 2 ∂P) - ∫ ω, (s ω) ^ 2 ∂P := by
      simp only [pow_two]

end ReflectedGMS.MartingaleLimit
