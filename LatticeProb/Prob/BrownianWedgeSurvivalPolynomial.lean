import LatticeProb.Prob.BrownianWedgeSurvivalExponential
import LatticeProb.Analysis.ExponentialInversePower

/-! # Polynomial bounds for Brownian wedge survival -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The wedge survival estimate with an arbitrary polynomial remainder. -/
theorem brownian_wedge_survival_polynomial :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : Euc 2}
      {B : ℝ≥0 → Ω → Euc 2} (_hB : IsBrownianSpace 2 x B P)
      {θ p r : ℝ} (_hθ0 : 0 < θ) (_hθπ : θ < Real.pi)
      (_hp : 0 < p) (_hpθ : p * θ < Real.pi) (_hr : 0 < r)
      (t : ℝ≥0) (_ht : 4 * r ^ 2 ≤ (t : ℝ)) (_hxr : ‖x‖ ≤ r)
      (n : ℕ),
      let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
      let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
        CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
      x ∈ closure W →
      P.real {ω | ∀ s ≤ t, B s ω ∈ W} ≤
        (Real.cos (p * (θ / 2)))⁻¹ * (‖x‖ / r) ^ p +
          C * ((n.factorial : ℝ) / c ^ n) * (4 * r ^ 2 / (t : ℝ)) ^ n := by
  obtain ⟨C, c, hC, hc, hbound⟩ := brownian_wedge_survival_exponential
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω mΩ P x B hB θ p r hθ0 hθπ hp hpθ hr t ht hxr n
  dsimp only
  intro hx
  have hcos : 0 < Real.cos (p * (θ / 2)) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr _
  have htpos : 0 < (t : ℝ) := by nlinarith [sq_pos_of_pos hr]
  have hu : 0 < 4 * r ^ 2 / (t : ℝ) := by positivity
  have hexp := exp_neg_inv_rpow_le hc hu n (a := (1 : ℝ))
  have hexp' : Real.exp (-(c * ((t : ℝ) / (4 * r ^ 2)))) ≤
      ((n.factorial : ℝ) / c ^ n) * (4 * r ^ 2 / (t : ℝ)) ^ n := by
    convert hexp using 1 <;> simp only [one_mul, Real.rpow_neg hu.le,
      Real.rpow_one, Real.rpow_natCast]
    congr 2
    field_simp
  have hprofile :
      ((Complex.orthonormalBasisOneI.repr.symm x) ^ (p : ℂ)).re ≤ ‖x‖ ^ p := by
    calc
      _ ≤ ‖(Complex.orthonormalBasisOneI.repr.symm x) ^ (p : ℂ)‖ := Complex.re_le_norm _
      _ = ‖x‖ ^ p := by rw [Complex.norm_cpow_real, LinearIsometryEquiv.norm_map]
  have h := hbound hB hθ0 hθπ hp hpθ hr t ht hxr hx
  have hcoef : 0 < Real.cos (p * (θ / 2)) * r ^ p := mul_pos hcos hrp
  have hdiv : ‖x‖ ^ p / (Real.cos (p * (θ / 2)) * r ^ p) =
      (Real.cos (p * (θ / 2)))⁻¹ * (‖x‖ / r) ^ p := by
    rw [Real.div_rpow (norm_nonneg _) hr.le]
    ring
  have hmain := add_le_add hprofile
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp' hC.le) hcoef.le)
  calc
    _ ≤ (‖x‖ ^ p + (Real.cos (p * (θ / 2)) * r ^ p) *
        (C * (((n.factorial : ℝ) / c ^ n) * (4 * r ^ 2 / (t : ℝ)) ^ n))) /
        (Real.cos (p * (θ / 2)) * r ^ p) := by
          apply (le_div_iff₀ hcoef).2
          nlinarith [h, hmain]
    _ = _ := by
      rw [add_div, hdiv]
      rw [mul_div_cancel_left₀ _ hcoef.ne']
      ring

end LatticeProb
