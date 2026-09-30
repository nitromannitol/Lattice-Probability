/-
A measurable choice of derivative representative for a family of real functions, built from
forward difference quotients, agreeing with the classical derivative wherever one exists.

`LatticeProb.Scaling.TimeDerivative` uses `limsup`, sufficient when the quotients are already
known nonnegative; `LatticeProb.Scaling.MeasurableTimeDerivative` uses `limUnder`, giving a
canonical measurable value even without a sign hypothesis.

Moved from Parking-Sharpness.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.Scaling.TimeDerivative

/-- The upper limit of forward difference quotients along `1 / (n + 1)`. -/
def value (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  limsup (fun n : ℕ => (f (s + 1 / ((n : ℝ) + 1)) - f s) / (1 / ((n : ℝ) + 1))) atTop

/-- Forward difference quotients of a monotone function are nonnegative. -/
theorem forward_difference_nonneg {f : ℝ → ℝ} (hf : Monotone f)
    (s : ℝ) {h : ℝ} (hh : 0 < h) : 0 ≤ (f (s + h) - f s) / h :=
  div_nonneg (sub_nonneg.mpr (hf (le_add_of_nonneg_right hh.le))) hh.le

/-- Coordinate measurability suffices for measurability of the derivative representative. -/
theorem measurable_value {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : ∀ s, Measurable fun ω => f ω s) (s : ℝ) :
    Measurable fun ω => value (f ω) s := by
  exact Measurable.limsup fun n => ((hf _).sub (hf s)).div_const _

/-- At differentiability points the upper limit is the actual derivative. -/
theorem value_eq_of_hasDerivAt {f : ℝ → ℝ} {s a : ℝ} (hf : HasDerivAt f a s) :
    value f s = a := by
  have hstep : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall ?_⟩
    intro n
    show 0 < 1 / ((n : ℝ) + 1)
    positivity
  have hlim := hf.tendsto_slope_zero_right.comp hstep
  simpa only [value, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim.limsup_eq

end LatticeProb.Scaling.TimeDerivative

namespace LatticeProb.Scaling.MeasurableTimeDerivative

/-- Forward difference quotients with positive step size `1 / (n + 1)`. -/
def quotient (f : ℝ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  (f (s + 1 / ((n : ℝ) + 1)) - f s) / (1 / ((n : ℝ) + 1))

/-- The limit of the countable forward difference quotients, with the default
value of `limUnder` at points where the sequence does not converge. -/
def value (f : ℝ → ℝ) (s : ℝ) : ℝ := limUnder atTop (quotient f s)

/-- Coordinate measurability of a field suffices for measurability of each
difference quotient. No topology on the sample space is needed. -/
theorem measurable_quotient {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : ∀ t, Measurable fun ω => f ω t) (s : ℝ) (n : ℕ) :
    Measurable fun ω => quotient (f ω) s n :=
  ((hf _).sub (hf _)).div_const _

/-- The canonical derivative is measurable even when some paths are not
differentiable. Its mathematical value is identified wherever a derivative exists. -/
theorem measurable_value {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : ∀ t, Measurable fun ω => f ω t) (s : ℝ) :
    Measurable fun ω => value (f ω) s :=
  (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_quotient hf s n).stronglyMeasurable)).measurable

/-- At every differentiability point the sequence converges to the derivative. -/
theorem tendsto_quotient {f : ℝ → ℝ} {s a : ℝ} (hf : HasDerivAt f a s) :
    Tendsto (quotient f s) atTop (𝓝 a) := by
  have hstep : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by simp only [Set.mem_Ioi]; positivity)⟩
  change Tendsto (fun n : ℕ =>
    (f (s + 1 / ((n : ℝ) + 1)) - f s) / (1 / ((n : ℝ) + 1))) atTop (𝓝 a)
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm]
    using hf.tendsto_slope_zero_right.comp hstep

/-- The measurable choice agrees with every existing classical derivative. -/
theorem value_eq {f : ℝ → ℝ} {s a : ℝ} (hf : HasDerivAt f a s) :
    value f s = a := (tendsto_quotient hf).limUnder_eq

/-- The forward quotients of a time-monotone function are nonnegative. -/
theorem quotient_nonneg {f : ℝ → ℝ} (hf : Monotone f) (s : ℝ) (n : ℕ) :
    0 ≤ quotient f s n := by
  apply div_nonneg
  · exact sub_nonneg.mpr (hf (le_add_of_nonneg_right (by positivity)))
  · positivity

end LatticeProb.Scaling.MeasurableTimeDerivative
