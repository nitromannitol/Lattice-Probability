/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppingIncrementProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedBracketIncrement

/-!
Probability bounds for increments at two bounded stopping times.  These are
conditional tightness inputs: this file does not assert path-space tightness
or a functional central limit theorem.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The analytic Chebyshev step, separated from the stopping argument so that
it also applies to the exact common-localizer specialization. -/
theorem measure_abs_ge_le_of_sq_integral_eq
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : Integrable (fun ω => (X ω) ^ 2) P)
    (hid : (∫ ω, (X ω) ^ 2 ∂P) = ∫ ω, Y ω ∂P)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |X ω|} ≤ ENNReal.ofReal ((∫ ω, Y ω ∂P) / ε ^ 2) := by
  let f : Ω → ℝ := fun ω => (X ω) ^ 2 / ε ^ 2
  have hf : Integrable f P := hX.div_const (ε ^ 2)
  have hf0 : 0 ≤ᵐ[P] f := Eventually.of_forall fun ω =>
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmarkov : P {ω | ε ≤ |X ω|} ≤ ENNReal.ofReal (∫ ω, f ω ∂P) := by
    apply hf.measure_le_integral hf0
    intro ω hω
    change ε ≤ |X ω| at hω
    dsimp only [f]
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    simpa only [one_mul] using
      ((sq_le_sq).2 (by simpa only [abs_of_pos hε] using hω))
  refine hmarkov.trans_eq ?_
  congr 1
  rw [integral_div, hid]

/-- Chebyshev's inequality for a bounded stopping-time increment, with its
second moment identified by the compensated-square martingale.  Initial
values need not vanish. -/
theorem bounded_stopping_increment_probability_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |stoppedValue M τ ω - stoppedValue M σ ω|} ≤
      ENNReal.ofReal
        ((∫ ω, stoppedValue B τ ω - stoppedValue B σ ω ∂P) / ε ^ 2) := by
  have hid := bounded_stopping_bracket_increment_integral
    hM hC hσ hτ T hστ hτT hrM hrC h2T
  exact measure_abs_ge_le_of_sq_integral_eq hid.1 hid.2.2 hε

end ReflectedGMS.MartingaleLimit
