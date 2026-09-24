/-
Chebyshev's inequality, in the second-moment/tail-measure form a martingale negligibility
bound needs. `Ω` is an arbitrary measurable space, `μ` an arbitrary finite measure, and
`f : Ω → ℝ` an arbitrary function with a square-integrable square.

The proof applies `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` at the squared function and
converts the tail event `{a < |f|}` to `{a² ≤ f²}`; the whole argument uses Mathlib only.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory

noncomputable section
namespace LatticeProb.Scaling.Chebyshev

/-- **Chebyshev's inequality**, real tail-measure form: for a finite measure `μ` and a
function `f` whose square is integrable, `μ{|f| > a} ≤ (∫f²dμ)/a²` for every `a > 0`. -/
theorem measure_gt_le_integral_sq_div_sq {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → ℝ) {a : ℝ} (ha : 0 < a)
    (hint : Integrable (fun ω => (f ω) ^ 2) μ) :
    (μ {ω | a < |f ω|}).toReal ≤ (∫ ω, (f ω) ^ 2 ∂μ) / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun ω => sq_nonneg (f ω)) hint (a ^ 2)
  have hsub : (μ {ω | a < |f ω|}) ≤ (μ {ω | a ^ 2 ≤ (f ω) ^ 2}) :=
    measure_mono fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω ⊢
      nlinarith [sq_abs (f ω)]
  have hfin : (μ {ω | a ^ 2 ≤ (f ω) ^ 2}) ≠ ⊤ := measure_ne_top _ _
  have hle : (μ {ω | a < |f ω|}).toReal ≤ (μ {ω | a ^ 2 ≤ (f ω) ^ 2}).toReal :=
    ENNReal.toReal_mono hfin hsub
  have hreal : (μ {ω | a ^ 2 ≤ (f ω) ^ 2}).toReal = μ.real {ω | a ^ 2 ≤ (f ω) ^ 2} := rfl
  rw [hreal] at hle
  have hM' : a ^ 2 * μ.real {ω | a ^ 2 ≤ (f ω) ^ 2} ≤ ∫ ω, (f ω) ^ 2 ∂μ := hM
  rw [le_div_iff₀ ha2]
  calc (μ {ω | a < |f ω|}).toReal * a ^ 2
      ≤ μ.real {ω | a ^ 2 ≤ (f ω) ^ 2} * a ^ 2 := mul_le_mul_of_nonneg_right hle ha2.le
    _ = a ^ 2 * μ.real {ω | a ^ 2 ≤ (f ω) ^ 2} := by ring
    _ ≤ ∫ ω, (f ω) ^ 2 ∂μ := hM'

end LatticeProb.Scaling.Chebyshev
end
