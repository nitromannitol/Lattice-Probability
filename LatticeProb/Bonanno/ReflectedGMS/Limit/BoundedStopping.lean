/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BoundedStopping at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.FiniteStopping
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingApproximation
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRight

/-!
Bounded continuous-time expectation sampling. The checked finite grids converge
from above; right-continuity gives stopped-value convergence. Existing optional
sampling identifies the approximants as conditional expectations of one terminal
value, so existing uniform-integrability and L¹-limit theorems pass expectations
to the actual bounded stopping time. No completion or filtration right-continuity
is required, and no conditional stopping-stability conclusion is asserted here.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Evaluation of a right-continuous path along the actual bounded grid stopping
times converges to its actual stopped value, including zero and the horizon. -/
theorem boundedGridApprox_stoppedValue_tendsto
    {E : Type*} [TopologicalSpace E] (X : ℝ≥0 → Ω → E)
    {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (ω : Ω) (hr : IsRightContinuous (fun t => X t ω)) :
    Tendsto (fun n => stoppedValue X (boundedGridApprox τ T n) ω)
      atTop (𝓝 (stoppedValue X τ ω)) := by
  have hne : τ ω ≠ ⊤ := (lt_of_le_of_lt (hτT ω) (WithTop.coe_lt_top T)).ne
  have htime : Tendsto (fun n => (boundedGridApprox τ T n ω).untopA)
      atTop (𝓝[≥] (τ ω).untopA) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (WithTop.tendsto_untopA hne).comp
        (tendsto_nhds_of_tendsto_nhdsWithin (boundedGridApprox_tendsto_right T hτT ω))
    · exact Eventually.of_forall fun n => by
        have hn : boundedGridApprox τ T n ω ≠ ⊤ :=
          (lt_of_le_of_lt (boundedGridApprox_bounds T hτT n ω).2 (WithTop.coe_lt_top T)).ne
        exact WithTop.untopA_mono hn (boundedGridApprox_bounds T hτT n ω).1
  exact Filter.Tendsto.comp (continuousWithinAt_Ioi_iff_Ici.mp (hr _)) htime

/-- The finite stopped approximants converge in L¹ to the actual bounded
stopped value. Uniform integrability is obtained directly from mathlib's family
of conditional expectations of the terminal value. -/
theorem bounded_stopping_L1
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    (∀ n, Integrable (stoppedValue M (boundedGridApprox τ T n)) P) ∧
    Integrable (stoppedValue M τ) P ∧
    Tendsto (fun n => eLpNorm (stoppedValue M (boundedGridApprox τ T n) -
      stoppedValue M τ) 1 P) atTop (𝓝 0) := by
  let Y := fun n => stoppedValue M (boundedGridApprox τ T n)
  have hσ (n : ℕ) : IsStoppingTime F (boundedGridApprox τ T n) :=
    isStoppingTime_boundedGridApprox hτ T hτT n
  have he (n : ℕ) : Y n =ᵐ[P] P[M T | (hσ n).measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hσ n)
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2)
      (finite_range_boundedGridApprox T hτT n).countable
  have hui : UniformIntegrable Y 1 P :=
    ((hM.integrable T).uniformIntegrable_condExp
      (fun n : ℕ => (hσ n).measurableSpace_le)).ae_eq (fun n => (he n).symm)
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (stoppedValue M τ ω)) :=
    hr.mono fun ω hω => boundedGridApprox_stoppedValue_tendsto M T hτT ω hω
  have hg : MemLp (stoppedValue M τ) 1 P := hui.memLp_of_ae_tendsto hconv
  refine ⟨fun n => memLp_one_iff_integrable.mp (hui.memLp n),
    memLp_one_iff_integrable.mp hg, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun n => (hui.memLp n).aestronglyMeasurable) hg hui.1 hconv

/-- Optional stopping of expectations at an arbitrary bounded real-time
stopping time. The stopped value is proved integrable as part of the conclusion.
Only almost-sure right continuity of the actual martingale paths is needed. -/
theorem bounded_stopping_integrable_and_integral_eq_terminal
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    Integrable (stoppedValue M τ) P ∧
      (∫ ω, stoppedValue M τ ω ∂P) = ∫ ω, M T ω ∂P := by
  obtain ⟨hFi, hg, hL1⟩ := bounded_stopping_L1 hM hτ T hτT hr
  have hlim := tendsto_integral_of_L1' (stoppedValue M τ)
    (Eventually.of_forall hFi) hL1
  have he : (fun n : ℕ => ∫ ω, stoppedValue M (boundedGridApprox τ T n) ω ∂P) =
      (fun _ : ℕ => ∫ ω, M T ω ∂P) := by
    funext n
    exact finite_stopping_integral_eq_terminal hM (isStoppingTime_boundedGridApprox hτ T hτT n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2)
  rw [he] at hlim
  exact ⟨hg, tendsto_nhds_unique hlim tendsto_const_nhds⟩

end ReflectedGMS.MartingaleLimit
