import Mathlib
import LatticeProb.Prob.UpcrossLaplace

/-!
# Uniqueness for the Laplace weight `e^{-q τ}` of an a.s. finite time

If two `[0, 1]`-valued functions `g`, `h` have the same integral against `e^{-q τ}` for every
`q > 0`, with `τ` a.s. finite, then they have the same integral: let `q → 0` along `1/(n+1)` and use
dominated convergence (`e^{-q τ} → 1` where `τ < ∞`).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace LatticeProb

/-- For finite `r`, `e^{-(1/(n+1)) r} → 1` as `n → ∞`. -/
lemma tendsto_expNeg_one_div_succ {r : ℝ≥0∞} (hr : r < ⊤) :
    Tendsto (fun n : ℕ => expNeg (1 / ((n : ℝ) + 1)) r) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)) * r.toReal) atTop (𝓝 (-0 * r.toReal)) :=
    h0.neg.mul_const _
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp
    ((Real.continuous_exp.tendsto _).comp h1)
  have h3 : ENNReal.ofReal (Real.exp (-0 * r.toReal)) = 1 := by simp
  rw [h3] at h2
  refine h2.congr fun n => ?_
  simp [expNeg, hr.ne]

/-- Laplace uniqueness for a probability measure and an a.s. finite time `τ`: if
`∫ e^{-q τ} g = ∫ e^{-q τ} h` for all `q > 0` and `g, h` are measurable with values in `[0, 1]`,
then `∫ g = ∫ h`. -/
theorem lintegral_eq_of_expNeg_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {τ : Ω → ℝ≥0∞} (hτm : Measurable τ) (hτ : ∀ᵐ ω ∂P, τ ω < ⊤)
    {g h : Ω → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) (hg1 : ∀ ω, g ω ≤ 1)
    (hh1 : ∀ ω, h ω ≤ 1)
    (hq : ∀ q : ℝ, 0 < q →
      ∫⁻ ω, expNeg q (τ ω) * g ω ∂P = ∫⁻ ω, expNeg q (τ ω) * h ω ∂P) :
    ∫⁻ ω, g ω ∂P = ∫⁻ ω, h ω ∂P := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have key : ∀ {f : Ω → ℝ≥0∞}, Measurable f → (∀ ω, f ω ≤ 1) →
      Tendsto (fun n : ℕ => ∫⁻ ω, expNeg (1 / ((n : ℝ) + 1)) (τ ω) * f ω ∂P) atTop
        (𝓝 (∫⁻ ω, f ω ∂P)) := by
    intro f hf hf1
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (fun n => ?_)
      (by simp) ?_
    · exact ((measurable_expNeg _).comp hτm).mul hf
    · refine Filter.Eventually.of_forall fun ω => ?_
      calc expNeg (1 / ((n : ℝ) + 1)) (τ ω) * f ω ≤ 1 * 1 :=
            mul_le_mul' (expNeg_le_one (hpos n).le _) (hf1 ω)
        _ = 1 := one_mul 1
    · filter_upwards [hτ] with ω hω
      have := ENNReal.Tendsto.mul_const (tendsto_expNeg_one_div_succ hω) (Or.inl one_ne_zero)
        (b := f ω)
      simpa using this
  exact tendsto_nhds_unique (key hg hg1)
    ((key hh hh1).congr fun n => (hq _ (hpos n)).symm)

end LatticeProb
