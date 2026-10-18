/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/Limit/{FiniteStopping,StoppingApproximation,BoundedStopping}.lean.
-/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Nonneg.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LeftRight
import LatticeProb.Prob.StoppingDyadic

/-!
Optional stopping at finitely valued stopping times on actual nonnegative-real
time. Mathlib already supplies the stronger bounded countable-range conditional-
expectation identity, so no finite-atom decomposition is reimplemented. The
second-moment estimate reuses its conditional-expectation contraction inequality.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Finite-valued optional stopping: the stopped expectation equals the terminal
expectation. The finite deterministic upper bound excludes the `WithTop` value
infinity; no path continuity or completed filtration is required. -/
theorem finite_stopping_integral_eq_terminal
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (∫ ω, stoppedValue M τ ω ∂P) = ∫ ω, M T ω ∂P := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hfin.countable
  exact (integral_congr_ae he).trans (integral_condExp hτ.measurableSpace_le)

/-- Terminal L² integrability alone suffices at a bounded finite-valued stopping
time, by its existing conditional-expectation representation. -/
theorem finite_stopping_memLp_two
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (h2T : MemLp (M T) 2 P) :
    MemLp (stoppedValue M τ) 2 P := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hfin.countable
  exact (memLp_congr_ae he).2 (h2T.condExp one_le_two)

/-- Finite-valued optional stopping for second moments. No square-integrability
at every time is added: the terminal second moment controls the stopped one. -/
theorem finite_stopping_second_moment_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (h2T : MemLp (M T) 2 P) :
    (∫ ω, (stoppedValue M τ ω) ^ 2 ∂P) ≤ ∫ ω, (M T ω) ^ 2 ∂P := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hfin.countable
  calc
    _ = ∫ ω, (P[M T | hτ.measurableSpace] ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω using congrArg (fun x : ℝ => x ^ 2) hω
    _ ≤ _ := by
      have hint : Integrable (fun ω => ‖M T ω‖ ^ (2 : ℝ)) P := by
        simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h2T.integrable_sq
      have h := integral_norm_condExp_rpow_le (m := hτ.measurableSpace)
        (show (1 : ℝ) ≤ 2 from one_le_two) hint
      simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

/-!
Finite-grid approximation from above of a bounded nonnegative-real stopping
time. LP’s dyadic rounding supplies the stopping events;
`IsStoppingTime.min_const` caps the grid at the original horizon, including zero.
-/

/-- Round a stopping time upward on LP’s dyadic grid, then cap it at `T`.
The lifted rounding sends infinity to infinity, so an infinite input gives `T`.
For times bounded by `T`, this agrees with rounding the finite time and capping. -/
noncomputable def boundedDyadicApprox (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min ((τ ω).map (dyUp n)) T

@[simp] theorem boundedDyadicApprox_zero (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    boundedDyadicApprox τ 0 n ω = 0 := by
  exact min_eq_right bot_le

private theorem finite_time_ne_top {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) : τ ω ≠ ⊤ :=
  (lt_of_le_of_lt (hτT ω) (WithTop.coe_lt_top T)).ne

private theorem boundedDyadicApprox_eq {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) (ω : Ω) :
    boundedDyadicApprox τ T n ω = min (dyUp n (τ ω).untopA : WithTop ℝ≥0) T := by
  have hx : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop (finite_time_ne_top hτT ω), WithTop.coe_untop]
  have hm : (τ ω).map (dyUp n) = (dyUp n (τ ω).untopA : WithTop ℝ≥0) := by
    nth_rw 1 [← hx]
    exact WithTop.map_coe _ _
  exact congrArg (fun x : WithTop ℝ≥0 => min x T) hm

@[simp] theorem boundedDyadicApprox_top (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    boundedDyadicApprox (fun _ => ⊤) T n ω = T := by
  simp only [boundedDyadicApprox, WithTop.map_top, min_eq_right le_top]

/-- Each grid approximation is an actual stopping time for the original
filtration; no right-continuity assumption on that filtration is needed. -/
theorem isStoppingTime_boundedDyadicApprox
    {F : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) :
    IsStoppingTime F (boundedDyadicApprox τ T n) := by
  have he : (fun ω => ((τ ω).untopA : WithTop ℝ≥0)) = τ := by
    funext ω
    rw [WithTop.untopA_eq_untop (finite_time_ne_top hτT ω), WithTop.coe_untop]
  have hτ' : IsStoppingTime F (fun ω => ((τ ω).untopA : WithTop ℝ≥0)) := he.symm ▸ hτ
  have heapprox : boundedDyadicApprox τ T n =
      fun ω => min (dyUp n (τ ω).untopA : WithTop ℝ≥0) T :=
    funext (boundedDyadicApprox_eq T hτT n)
  rw [heapprox]
  exact (isStoppingTime_dyUp hτ' n).min_const T

/-- The approximation lies between the original stopping time and the same
finite horizon, with no exception at zero or at a grid point. -/
theorem boundedDyadicApprox_bounds {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) (ω : Ω) :
    τ ω ≤ boundedDyadicApprox τ T n ω ∧ boundedDyadicApprox τ T n ω ≤ T := by
  rw [boundedDyadicApprox_eq T hτT n ω]
  refine ⟨le_min ?_ (hτT ω), min_le_right _ _⟩
  exact (WithTop.untopA_le_iff (finite_time_ne_top hτT ω)).1 (le_dyUp n _)

/-- Boundedness of the original stopping time bounds the integer numerator,
so every approximating stopping time has finite range. -/
theorem finite_range_boundedDyadicApprox {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) : (Set.range (boundedDyadicApprox τ T n)).Finite := by
  let K := Nat.ceil ((2 ^ n : ℝ≥0) * T)
  refine ((Set.finite_Iic K).image (fun j : ℕ =>
    min (((j : ℝ≥0) / (2 ^ n : ℝ≥0)) : WithTop ℝ≥0) T)).subset ?_
  rintro y ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((2 ^ n : ℝ≥0) * (τ ω).untopA), ?_, ?_⟩
  · apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left
      ((WithTop.untopA_le_iff (finite_time_ne_top hτT ω)).2 (hτT ω)) zero_le
  · exact (boundedDyadicApprox_eq T hτT n ω).symm

/-- Pointwise convergence from the right in the actual WithTop time space.
The filter includes equality, as needed when a stopping time is already on a
grid or equals the terminal horizon. -/
theorem boundedDyadicApprox_tendsto_right {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    Tendsto (fun n => boundedDyadicApprox τ T n ω) atTop (𝓝[≥] τ ω) := by
  have hcoe : Tendsto (fun n => (dyUp n (τ ω).untopA : WithTop ℝ≥0))
      atTop (𝓝 ((τ ω).untopA : WithTop ℝ≥0)) :=
    WithTop.continuous_coe.continuousAt.tendsto.comp (tendsto_dyUp _)
  have hx : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop (finite_time_ne_top hτT ω), WithTop.coe_untop]
  have hcap : Tendsto (fun n => boundedDyadicApprox τ T n ω) atTop (𝓝 (τ ω)) := by
    simp only [boundedDyadicApprox_eq T hτT]
    simpa only [hx, min_eq_left (hτT ω)] using
      hcoe.min (tendsto_const_nhds (x := (T : WithTop ℝ≥0)))
  exact tendsto_nhdsWithin_iff.mpr
    ⟨hcap, Eventually.of_forall fun n => (boundedDyadicApprox_bounds T hτT n ω).1⟩

/-!
Bounded continuous-time expectation sampling. The checked finite grids converge
from above; right-continuity gives stopped-value convergence. Existing optional
sampling identifies the approximants as conditional expectations of one terminal
value, so existing uniform-integrability and L¹-limit theorems pass expectations
to the actual bounded stopping time. No completion or filtration right-continuity
is required, and no conditional stopping-stability conclusion is asserted here.
-/

/-- Evaluation of a right-continuous path along the actual bounded grid stopping
times converges to its actual stopped value, including zero and the horizon. -/
theorem boundedDyadicApprox_stoppedValue_tendsto
    {E : Type*} [TopologicalSpace E] (X : ℝ≥0 → Ω → E)
    {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (ω : Ω) (hr : ∀ t, ContinuousWithinAt (fun s => X s ω) (Ioi t) t) :
    Tendsto (fun n => stoppedValue X (boundedDyadicApprox τ T n) ω)
      atTop (𝓝 (stoppedValue X τ ω)) := by
  have hne : τ ω ≠ ⊤ := (lt_of_le_of_lt (hτT ω) (WithTop.coe_lt_top T)).ne
  have htime : Tendsto (fun n => (boundedDyadicApprox τ T n ω).untopA)
      atTop (𝓝[≥] (τ ω).untopA) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (WithTop.tendsto_untopA hne).comp
        (tendsto_nhds_of_tendsto_nhdsWithin (boundedDyadicApprox_tendsto_right T hτT ω))
    · exact Eventually.of_forall fun n => by
        have hn : boundedDyadicApprox τ T n ω ≠ ⊤ :=
          (lt_of_le_of_lt (boundedDyadicApprox_bounds T hτT n ω).2 (WithTop.coe_lt_top T)).ne
        exact WithTop.untopA_mono hn (boundedDyadicApprox_bounds T hτT n ω).1
  exact Filter.Tendsto.comp (continuousWithinAt_Ioi_iff_Ici.mp (hr _)) htime

/-- The finite stopped approximants converge in L¹ to the actual bounded
stopped value. Uniform integrability is obtained directly from mathlib's family
of conditional expectations of the terminal value. -/
theorem bounded_stopping_L1
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun s => M s ω) (Ioi t) t) :
    (∀ n, Integrable (stoppedValue M (boundedDyadicApprox τ T n)) P) ∧
    Integrable (stoppedValue M τ) P ∧
    Tendsto (fun n => eLpNorm (stoppedValue M (boundedDyadicApprox τ T n) -
      stoppedValue M τ) 1 P) atTop (𝓝 0) := by
  let Y := fun n => stoppedValue M (boundedDyadicApprox τ T n)
  have hσ (n : ℕ) : IsStoppingTime F (boundedDyadicApprox τ T n) :=
    isStoppingTime_boundedDyadicApprox hτ T hτT n
  have he (n : ℕ) : Y n =ᵐ[P] P[M T | (hσ n).measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hσ n)
      (fun ω => (boundedDyadicApprox_bounds T hτT n ω).2)
      (finite_range_boundedDyadicApprox T hτT n).countable
  have hui : UniformIntegrable Y 1 P :=
    ((hM.integrable T).uniformIntegrable_condExp
      (fun n : ℕ => (hσ n).measurableSpace_le)).ae_eq (fun n => (he n).symm)
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (stoppedValue M τ ω)) :=
    hr.mono fun ω hω => boundedDyadicApprox_stoppedValue_tendsto M T hτT ω hω
  have hg : MemLp (stoppedValue M τ) 1 P := hui.memLp_of_ae_tendsto hconv
  refine ⟨fun n => memLp_one_iff_integrable.mp (hui.memLp n),
    memLp_one_iff_integrable.mp hg, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hui.1 hg hui.2.1 hconv

/-- Optional stopping of expectations at an arbitrary bounded real-time
stopping time. The stopped value is proved integrable as part of the conclusion.
Only almost-sure right continuity of the actual martingale paths is needed. -/
theorem bounded_stopping_integrable_and_integral_eq_terminal
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun s => M s ω) (Ioi t) t) :
    Integrable (stoppedValue M τ) P ∧
      (∫ ω, stoppedValue M τ ω ∂P) = ∫ ω, M T ω ∂P := by
  obtain ⟨hFi, hg, hL1⟩ := bounded_stopping_L1 hM hτ T hτT hr
  have hlim := tendsto_integral_of_L1' (stoppedValue M τ) hg.1
    (Eventually.of_forall hFi) hL1
  have he : (fun n : ℕ => ∫ ω, stoppedValue M (boundedDyadicApprox τ T n) ω ∂P) =
      (fun _ : ℕ => ∫ ω, M T ω ∂P) := by
    funext n
    exact finite_stopping_integral_eq_terminal hM (isStoppingTime_boundedDyadicApprox hτ T hτT n)
      (finite_range_boundedDyadicApprox T hτT n) T
      (fun ω => (boundedDyadicApprox_bounds T hτT n ω).2)
  rw [he] at hlim
  exact ⟨hg, tendsto_nhds_unique hlim tendsto_const_nhds⟩

end LatticeProb

/-! ## Nonvacuity checks

Use a nonzero probability measure on a nonempty sample space, a nonzero
martingale, and a positive stopping time strictly below its horizon. The zero
horizon is also checked. These are applications of the public theorems to
explicit data, so the stopping, integrability, and continuity premises are all
supplied by terms.
-/
namespace LatticeProb

private noncomputable def exampleMeasure : Measure Unit := Measure.dirac ()
private def exampleFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
  Filtration.const ℝ≥0 _ le_rfl
private instance : IsProbabilityMeasure exampleMeasure := by
  unfold exampleMeasure
  infer_instance

example : Nonempty Unit ∧ exampleMeasure Set.univ = 1 := ⟨⟨()⟩, measure_univ⟩

example : Martingale (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ)) exampleFiltration exampleMeasure ∧
    IsStoppingTime exampleFiltration (fun (_ : Unit) => (1 : WithTop ℝ≥0)) ∧
    (Set.range (fun (_ : Unit) => (1 : WithTop ℝ≥0))).Finite ∧
    (∀ (_ : Unit), (1 : WithTop ℝ≥0) ≤ (2 : ℝ≥0)) ∧
    MemLp (fun (_ : Unit) => (1 : ℝ)) 2 exampleMeasure ∧
    (∀ᵐ (_ : Unit) ∂exampleMeasure,
      ∀ t : ℝ≥0, ContinuousWithinAt (fun (_ : ℝ≥0) => (1 : ℝ)) (Ioi t) t) := by
  refine ⟨martingale_const _ _ _, isStoppingTime_const _ 1, Set.finite_range_const,
    fun _ => by norm_num, memLp_const _, Filter.Eventually.of_forall fun _ _ => ?_⟩
  exact continuous_const.continuousWithinAt

example :
    (∫ ω, stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (1 : WithTop ℝ≥0)) ω ∂exampleMeasure) =
    ∫ (_ : Unit), (1 : ℝ) ∂exampleMeasure :=
  finite_stopping_integral_eq_terminal (martingale_const exampleFiltration exampleMeasure 1)
    (isStoppingTime_const _ 1) Set.finite_range_const 2 (fun _ => by norm_num)

example : MemLp (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
    (fun _ => (1 : WithTop ℝ≥0))) 2 exampleMeasure :=
  finite_stopping_memLp_two (martingale_const exampleFiltration exampleMeasure 1)
    (isStoppingTime_const _ 1) Set.finite_range_const 2 (fun _ => by norm_num) (memLp_const _)

example :
    (∫ ω, (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (1 : WithTop ℝ≥0)) ω) ^ 2 ∂exampleMeasure) ≤
    ∫ (_ : Unit), (1 : ℝ) ^ 2 ∂exampleMeasure :=
  finite_stopping_second_moment_le (martingale_const exampleFiltration exampleMeasure 1)
    (isStoppingTime_const _ 1) Set.finite_range_const 2 (fun _ => by norm_num) (memLp_const _)

example :
    Integrable (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (1 : WithTop ℝ≥0))) exampleMeasure ∧
    (∫ ω, stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (1 : WithTop ℝ≥0)) ω ∂exampleMeasure) =
    ∫ (_ : Unit), (1 : ℝ) ∂exampleMeasure :=
  bounded_stopping_integrable_and_integral_eq_terminal
    (martingale_const exampleFiltration exampleMeasure 1) (isStoppingTime_const _ 1) 2
    (fun _ => by norm_num)
    (Filter.Eventually.of_forall fun _ _ => continuous_const.continuousWithinAt)

example :
    Integrable (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (0 : WithTop ℝ≥0))) exampleMeasure ∧
    (∫ ω, stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (0 : WithTop ℝ≥0)) ω ∂exampleMeasure) =
    ∫ (_ : Unit), (1 : ℝ) ∂exampleMeasure :=
  bounded_stopping_integrable_and_integral_eq_terminal
    (martingale_const exampleFiltration exampleMeasure 1) (isStoppingTime_const _ 0) 0
    (fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ _ => continuous_const.continuousWithinAt)

example : IsStoppingTime exampleFiltration
    (boundedDyadicApprox (fun (_ : Unit) => (1 : WithTop ℝ≥0)) 2 0) :=
  isStoppingTime_boundedDyadicApprox (isStoppingTime_const _ 1) 2
    (fun _ => by norm_num) 0

example : Tendsto
    (fun n => boundedDyadicApprox (fun (_ : Unit) => (1 : WithTop ℝ≥0)) 2 n ())
    atTop (𝓝[≥] (1 : WithTop ℝ≥0)) :=
  boundedDyadicApprox_tendsto_right 2 (fun _ => by norm_num) ()

example :
    (∀ n, Integrable (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (boundedDyadicApprox (fun _ => (1 : WithTop ℝ≥0)) 2 n)) exampleMeasure) ∧
    Integrable (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
      (fun _ => (1 : WithTop ℝ≥0))) exampleMeasure ∧
    Tendsto (fun n => eLpNorm
      (stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
        (boundedDyadicApprox (fun _ => (1 : WithTop ℝ≥0)) 2 n) -
      stoppedValue (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
        (fun _ => (1 : WithTop ℝ≥0))) 1 exampleMeasure) atTop (𝓝 0) :=
  bounded_stopping_L1 (martingale_const exampleFiltration exampleMeasure 1)
    (isStoppingTime_const _ 1) 2 (fun _ => by norm_num)
    (Filter.Eventually.of_forall fun _ _ => continuous_const.continuousWithinAt)

end LatticeProb
