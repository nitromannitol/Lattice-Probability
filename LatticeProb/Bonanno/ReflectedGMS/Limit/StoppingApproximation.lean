/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppingApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Nonneg.Floor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Finite-grid approximation from above of a bounded nonnegative-real stopping
time. Existing natural ceil/floor inequalities identify the stopping events;
`IsStoppingTime.min_const` caps the grid at the original horizon, including zero.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

/-- Rounding upward to the grid with spacing `1/(n+1)`. -/
noncomputable def upperGrid (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  (Nat.ceil (x * ((n : ℝ≥0) + 1)) : ℝ≥0) / ((n : ℝ≥0) + 1)

/-- The largest grid point at or below a test time. -/
noncomputable def lowerGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.floor (t * ((n : ℝ≥0) + 1)) : ℝ≥0) / ((n : ℝ≥0) + 1)

theorem le_upperGrid (n : ℕ) (x : ℝ≥0) : x ≤ upperGrid n x := by
  rw [upperGrid, le_div_iff₀ (by positivity : 0 < (n : ℝ≥0) + 1)]
  exact Nat.le_ceil _

theorem upperGrid_le_add_mesh (n : ℕ) (x : ℝ≥0) :
    upperGrid n x ≤ x + 1 / ((n : ℝ≥0) + 1) := by
  have hn : 0 < (n : ℝ≥0) + 1 := by positivity
  rw [upperGrid, div_le_iff₀ hn, add_mul, div_mul_cancel₀ _ hn.ne']
  exact (Nat.ceil_lt_add_one (show 0 ≤ x * ((n : ℝ≥0) + 1) from zero_le)).le

theorem lowerGrid_le (n : ℕ) (t : ℝ≥0) : lowerGrid n t ≤ t := by
  rw [lowerGrid, div_le_iff₀ (by positivity : 0 < (n : ℝ≥0) + 1)]
  exact Nat.floor_le zero_le

/-- The ceil/floor adjunction gives the exact sublevel set used for stopping. -/
theorem upperGrid_le_iff (n : ℕ) (x t : ℝ≥0) :
    upperGrid n x ≤ t ↔ x ≤ lowerGrid n t := by
  have hn : 0 < (n : ℝ≥0) + 1 := by positivity
  rw [upperGrid, lowerGrid, div_le_iff₀ hn, ← Nat.le_floor_iff (show 0 ≤ t *
    ((n : ℝ≥0) + 1) from zero_le), Nat.ceil_le, le_div_iff₀ hn]

theorem upperGrid_tendsto (x : ℝ≥0) :
    Tendsto (fun n => upperGrid n x) atTop (𝓝 x) := by
  have hu : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 x) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := x)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => le_upperGrid n x) (fun n => upperGrid_le_add_mesh n x)

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The upward grid approximation capped at the original finite horizon.
Its values retain mathlib's actual WithTop stopping-time type. -/
noncomputable def boundedGridApprox (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (upperGrid n (τ ω).untopA : WithTop ℝ≥0) T

@[simp] theorem boundedGridApprox_zero (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    boundedGridApprox τ 0 n ω = 0 := by
  exact min_eq_right (show (0 : WithTop ℝ≥0) ≤ ↑(upperGrid n (τ ω).untopA) from bot_le)

private theorem finite_time_ne_top {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) : τ ω ≠ ⊤ :=
  (lt_of_le_of_lt (hτT ω) (WithTop.coe_lt_top T)).ne

/-- Each grid approximation is an actual stopping time for the original
filtration; no right-continuity assumption on that filtration is needed. -/
theorem isStoppingTime_boundedGridApprox
    {F : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) :
    IsStoppingTime F (boundedGridApprox τ T n) := by
  have hu : IsStoppingTime F (fun ω => (upperGrid n (τ ω).untopA : WithTop ℝ≥0)) := by
    intro t
    have he : {ω | (upperGrid n (τ ω).untopA : WithTop ℝ≥0) ≤ t} =
        {ω | τ ω ≤ lowerGrid n t} := by
      ext ω
      change ((upperGrid n (τ ω).untopA : WithTop ℝ≥0) ≤ t) ↔ τ ω ≤ lowerGrid n t
      rw [WithTop.coe_le_coe, upperGrid_le_iff,
        WithTop.untopA_le_iff (finite_time_ne_top hτT ω)]
    rw [he]
    exact F.mono (lowerGrid_le n t) _ (hτ (lowerGrid n t))
  exact hu.min_const T

/-- The approximation lies between the original stopping time and the same
finite horizon, with no exception at zero or at a grid point. -/
theorem boundedGridApprox_bounds {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) (ω : Ω) :
    τ ω ≤ boundedGridApprox τ T n ω ∧ boundedGridApprox τ T n ω ≤ T := by
  refine ⟨le_min ?_ (hτT ω), min_le_right _ _⟩
  exact (WithTop.untopA_le_iff (finite_time_ne_top hτT ω)).1 (le_upperGrid n _)

/-- Boundedness of the original stopping time bounds the integer numerator,
so every approximating stopping time has finite range. -/
theorem finite_range_boundedGridApprox {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) : (Set.range (boundedGridApprox τ T n)).Finite := by
  let K := Nat.ceil (T * ((n : ℝ≥0) + 1))
  refine ((Set.finite_Iic K).image (fun j : ℕ =>
    min (((j : ℝ≥0) / ((n : ℝ≥0) + 1)) : WithTop ℝ≥0) T)).subset ?_
  rintro y ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((τ ω).untopA * ((n : ℝ≥0) + 1)), ?_, rfl⟩
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_right
    ((WithTop.untopA_le_iff (finite_time_ne_top hτT ω)).2 (hτT ω)) zero_le

/-- Pointwise convergence from the right in the actual WithTop time space.
The filter includes equality, as needed when a stopping time is already on a
grid or equals the terminal horizon. -/
theorem boundedGridApprox_tendsto_right {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    Tendsto (fun n => boundedGridApprox τ T n ω) atTop (𝓝[≥] τ ω) := by
  have hcoe : Tendsto (fun n => (upperGrid n (τ ω).untopA : WithTop ℝ≥0))
      atTop (𝓝 ((τ ω).untopA : WithTop ℝ≥0)) :=
    WithTop.continuous_coe.continuousAt.tendsto.comp (upperGrid_tendsto _)
  have hx : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop (finite_time_ne_top hτT ω), WithTop.coe_untop]
  have hcap : Tendsto (fun n => boundedGridApprox τ T n ω) atTop (𝓝 (τ ω)) := by
    change Tendsto (fun n => min (upperGrid n (τ ω).untopA : WithTop ℝ≥0) T)
      atTop (𝓝 (τ ω))
    simpa only [hx, min_eq_left (hτT ω)] using
      hcoe.min (tendsto_const_nhds (x := (T : WithTop ℝ≥0)))
  exact tendsto_nhdsWithin_iff.mpr
    ⟨hcap, Eventually.of_forall fun n => (boundedGridApprox_bounds T hτT n ω).1⟩

end ReflectedGMS.MartingaleLimit
