/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationarySpeedMeasure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupProbabilityKernel
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexCarreDuChamp
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! The atomic speed measure is invariant for the full-form semigroup.  Its
ordinary-edge carré-du-champ integral has exactly the full energy mass. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS
open FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V]

/-- Speed masses on the original discrete vertex space. -/
noncomputable def vertexSpeedMeasure (m : V → ℝ) : Measure V :=
  Measure.sum (fun x => ENNReal.ofReal (m x) • Measure.dirac x)

@[simp] theorem vertexSpeedMeasure_singleton (m : V → ℝ) (x : V) :
    vertexSpeedMeasure m {x} = ENNReal.ofReal (m x) := by
  simp [vertexSpeedMeasure, Measure.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Pi.single_apply]

theorem vertexSpeedMeasure_isFinite (m : V → ℝ) (hmsum : Summable m) :
    IsFiniteMeasure (vertexSpeedMeasure m) := by
  constructor
  simpa [vertexSpeedMeasure, Measure.sum_apply] using hmsum.tsum_ofReal_lt_top

/-- Detailed balance and conservativity give stationarity of the entire
speed measure, rather than only the mass identity at one vertex. -/
theorem semigroupProbabilityKernel_comp_vertexSpeedMeasure
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) :
    semigroupProbabilityKernel G m hm hmsum t ∘ₘ vertexSpeedMeasure m =
      vertexSpeedMeasure m := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (measurableSet_singleton y)]
  simp only [vertexSpeedMeasure_singleton, Measure.smul_apply, smul_eq_mul,
    semigroupProbabilityKernel_apply_singleton]
  calc
    ∑' x, ENNReal.ofReal (m x) * ENNReal.ofReal (semigroupKernel G m t x y) =
        ∑' x, ENNReal.ofReal (m y) * ENNReal.ofReal (semigroupKernel G m t y x) := by
      apply tsum_congr
      intro x
      rw [← ENNReal.ofReal_mul (hm x).le, ← ENNReal.ofReal_mul (hm y).le,
        semigroupKernel_detailedBalance G m hm t x y]
    _ = ENNReal.ofReal (m y) * ∑' x, ENNReal.ofReal (semigroupKernel G m t y x) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (m y) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (semigroupKernel_nonneg G m hm t y) (summable_semigroupKernel G m hm t y),
        tsum_semigroupKernel_eq_one G m hm hmsum t y]
      simp

/-- The full finite-energy hypothesis supplies all required summability. -/
theorem lintegral_vertexCarreDuChamp_vertexSpeedMeasure
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    (∫⁻ x, ENNReal.ofReal (vertexCarreDuChamp G m u x) ∂vertexSpeedMeasure m) =
      ENNReal.ofReal (2 * G.Energy u) := by
  rw [lintegral_countable']
  simp only [vertexSpeedMeasure_singleton]
  calc
    ∑' x, ENNReal.ofReal (vertexCarreDuChamp G m u x) * ENNReal.ofReal (m x) =
        ∑' x, ENNReal.ofReal (m x * vertexCarreDuChamp G m u x) := by
      apply tsum_congr
      intro x
      rw [mul_comm, ENNReal.ofReal_mul (hm x).le]
    _ = ENNReal.ofReal (∑' x, m x * vertexCarreDuChamp G m u x) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun x => mul_nonneg (hm x).le (vertexCarreDuChamp_nonneg G m hm u x))
        (summable_speed_mul_vertexCarreDuChamp G m hm hu)).symm
    _ = ENNReal.ofReal (2 * G.Energy u) := by
      rw [tsum_speed_mul_vertexCarreDuChamp G m hm hu]

end ReflectedGMS
