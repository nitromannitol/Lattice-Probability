import Mathlib

/-!
# First absolute moment of a shifted centred Gaussian law

For the centred Gaussian law `N(0, t)` on `ℝ` and a real shift `c`, the first absolute moment of `x + c`
is at most `(1 + t)/2 + |c|`. The proof combines the pointwise bound `|x| ≤ (1 + x²)/2` with the second
moment `t` of `N(0, t)`. The Gaussian setting is that of circle averages of a log-correlated Gaussian field
(Duplantier-Sheffield, arXiv:0808.1560, Section 3.1, p. 17: the circle average `h_ε(z)` has variance
`-log ε + log C(z;D)`, eq. (12)).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LatticeProb

/-- For the centred Gaussian law `N(0, t)` and `c ∈ ℝ`: `∫⁻ |x + c| dN(0, t) ≤ (1 + t)/2 + |c|`. -/
lemma lintegral_enorm_add_const_gaussianReal_le (t : ℝ≥0) (c : ℝ) :
    ∫⁻ x, ‖x + c‖ₑ ∂(gaussianReal 0 t) ≤ ENNReal.ofReal ((1 + (t : ℝ)) / 2 + |c|) := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 t) :=
    (memLp_id_gaussianReal (μ := 0) (v := t) 2).integrable_sq
  have hmean : ∫ x, x ∂(gaussianReal 0 t) = 0 := integral_id_gaussianReal
  have hvar : ∫ x, x ^ 2 ∂(gaussianReal 0 t) = (t : ℝ) := by
    have h := variance_id_gaussianReal (μ := 0) (v := t)
    rw [variance_eq_integral aemeasurable_id] at h
    simpa [hmean] using h
  have hA : Integrable (fun x : ℝ => 1 + x ^ 2) (gaussianReal 0 t) := (integrable_const 1).add hsq
  have hB : Integrable (fun x : ℝ => (1 + x ^ 2) / 2) (gaussianReal 0 t) := hA.div_const 2
  have hint : Integrable (fun x : ℝ => (1 + x ^ 2) / 2 + |c|) (gaussianReal 0 t) :=
    hB.add (integrable_const _)
  have hnn : 0 ≤ᵐ[gaussianReal 0 t] fun x : ℝ => (1 + x ^ 2) / 2 + |c| :=
    Filter.Eventually.of_forall fun x => by positivity
  calc ∫⁻ x, ‖x + c‖ₑ ∂(gaussianReal 0 t)
      ≤ ∫⁻ x, ENNReal.ofReal ((1 + x ^ 2) / 2 + |c|) ∂(gaussianReal 0 t) := by
        refine lintegral_mono fun x => ?_
        rw [Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hx : |x| ≤ (1 + x ^ 2) / 2 := by
          nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
        linarith [abs_add_le x c]
    _ = ENNReal.ofReal (∫ x, ((1 + x ^ 2) / 2 + |c|) ∂(gaussianReal 0 t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal ((1 + (t : ℝ)) / 2 + |c|) := by
        congr 1
        rw [integral_add hB (integrable_const _), integral_div,
          integral_add (integrable_const 1) hsq, hvar]
        simp

end LatticeProb
