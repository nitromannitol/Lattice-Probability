import LatticeProb.Analysis.WedgeArcSineCore
import LatticeProb.Analysis.WedgeArcWeakEigenfunction

/-! # Weak Dirichlet equation for angular sine core modes -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- Each mode of the finite sine core satisfies the weak Dirichlet equation. -/
theorem wedgeArcSineCore_mode_weak {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt g (g' x) x)
    (hgc : Continuous g) (hg'c : Continuous g')
    (ha : g (-θ / 2) = 0) (hb : g (θ / 2) = 0) :
    (∫ z, g' (Complex.arg z) *
      deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x)
        (Complex.arg z) ∂wedgeArcSurfaceMeasure θ) =
      ∫ z, g (Complex.arg z) *
        (wedgeArcSineCore hθ hθ'
          ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩ z).re
        ∂wedgeArcSurfaceMeasure θ := by
  rw [wedgeArcSineCore_apply_mode]
  have hae : (fun z : Metric.sphere (0 : ℂ) 1 => g (Complex.arg z) *
      Complex.re (((((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) • wedgeArcSineLp θ n) z))
      =ᵐ[wedgeArcSurfaceMeasure θ] fun z =>
        (Real.pi * (n + 1 : ℕ) / θ) ^ 2 *
          (g (Complex.arg z) * (Real.sqrt (2 / θ) *
            sinMode (-θ / 2) θ (n + 1) (Complex.arg z))) := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul
      (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) (wedgeArcSineLp θ n),
      (wedgeArcSineMode_memLp θ n).coeFn_toLp] with z hz hn
    change wedgeArcSineLp θ n z = _ at hn
    rw [hz]
    simp only [Pi.smul_apply]
    rw [hn]
    simp only [wedgeArcSineMode, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [integral_congr_ae hae, integral_const_mul]
  exact wedgeArc_sine_weak_eigenfunction hθ hθ' n hg hgc hg'c ha hb

end LatticeProb
