/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.FiniteTimeMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.OptionalStopping

/-! Finite time-sample maximal bounds, reusing mathlib's Doob inequality.
This is a prerequisite for continuous-time localization, not a tightness or
functional central limit theorem. -/

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal NNReal

namespace ReflectedGMS.MartingaleLimit

variable {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}

/-- Restrict an existing filtration to an increasing sequence of times. -/
def sampledFiltration (F : Filtration ι m) (t : ℕ → ι) (ht : Monotone t) :
    Filtration ℕ m where
  seq n := F (t n)
  mono' := fun _ _ hij => F.mono (ht hij)
  le' n := F.le (t n)

theorem submartingale_sample {P : Measure Ω} {F : Filtration ι m}
    {X : ι → Ω → ℝ} (hX : Submartingale X F P) (t : ℕ → ι) (ht : Monotone t) :
    Submartingale (fun n => X (t n)) (sampledFiltration F t ht) P :=
  ⟨fun n => hX.1 (t n), fun _ _ hij => hX.2.1 _ _ (ht hij),
    fun n => hX.2.2 (t n)⟩

/-- A finite grid of observation times is controlled by the terminal mean.
The threshold and measure remain in ENNReal, avoiding default real integrals
of nonintegrable processes: integrability is supplied by Submartingale. -/
theorem finite_time_maximal {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ι m} {X : ι → Ω → ℝ} (hX : Submartingale X F P)
    (h0 : ∀ t ω, 0 ≤ X t ω) (t : ℕ → ι) (ht : Monotone t)
    (ε : ℝ≥0) (n : ℕ) :
    ε * P {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one
      (fun k => X (t k) ω)} ≤ ENNReal.ofReal (∫ ω, X (t n) ω ∂P) := by
  exact (maximal_ineq (submartingale_sample hX t ht) (fun k ω => h0 (t k) ω) n).trans
    (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hX.integrable (t n))
      (Filter.Eventually.of_forall (h0 (t n)))))

end ReflectedGMS.MartingaleLimit
