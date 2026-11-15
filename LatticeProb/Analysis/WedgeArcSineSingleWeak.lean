import LatticeProb.Analysis.WedgeArcSineFiniteWeak
import LatticeProb.Analysis.WedgeArcAngularIntegrable

/-! # Weak equation for finite angular sine combinations -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

open LQGMetric.HeatSq

/-- A finite complex sine combination satisfies the weak Dirichlet equation. -/
theorem wedgeArcSineCore_finset_single_weak {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (s : Finset ℕ) (c : ℕ → ℂ) {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt g (g' x) x)
    (hgc : Continuous g) (hg'c : Continuous g')
    (ha : g (-θ / 2) = 0) (hb : g (θ / 2) = 0) :
    (∫ z, ∑ n ∈ s, c n * ((g' (Complex.arg z) *
      deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x)
        (Complex.arg z) : ℝ) : ℂ) ∂wedgeArcSurfaceMeasure θ) =
    ∫ z, (g (Complex.arg z) : ℂ) *
      wedgeArcSineCore hθ hθ'
        (∑ n ∈ s, c n • ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩) z
        ∂wedgeArcSurfaceMeasure θ := by
  have hd (n : ℕ) : Continuous (deriv (fun x => Real.sqrt (2 / θ) *
      sinMode (-θ / 2) θ (n + 1) x)) := by
    have he : deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x) =
        fun x => Real.sqrt (2 / θ) * (Real.pi * (n + 1 : ℕ) / θ *
          Real.cos (Real.pi * (n + 1 : ℕ) / θ * (x - (-θ / 2)))) := by
      funext x
      exact (hasDerivAt_const_mul_sinMode _ _ _ _ x).deriv
    rw [he]
    fun_prop
  have hf (n : ℕ) : Continuous (fun x => Real.sqrt (2 / θ) *
      sinMode (-θ / 2) θ (n + 1) x) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_const_mul_sinMode _ _ _ _ x).continuousAt
  have hleft (n : ℕ) : Integrable (fun z : sphere (0 : ℂ) 1 =>
      c n * ((g' (Complex.arg z) * deriv (fun x => Real.sqrt (2 / θ) *
        sinMode (-θ / 2) θ (n + 1) x) (Complex.arg z) : ℝ) : ℂ))
      (wedgeArcSurfaceMeasure θ) :=
    ((integrable_arg_wedgeArcSurfaceMeasure hθ' (hg'c.mul (hd n))).ofReal).const_mul _
  have hright (n : ℕ) : Integrable (fun z : sphere (0 : ℂ) 1 =>
      c n * (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
        ((g (Complex.arg z) * (Real.sqrt (2 / θ) *
          sinMode (-θ / 2) θ (n + 1) (Complex.arg z)) : ℝ) : ℂ))
      (wedgeArcSurfaceMeasure θ) :=
    ((integrable_arg_wedgeArcSurfaceMeasure hθ' (hgc.mul (hf n))).ofReal).const_mul _
  have hae := wedgeArcSineCore_finset_ae hθ hθ' s c
  calc
    _ = ∑ n ∈ s, c n * Complex.ofReal (∫ z, g' (Complex.arg z) *
        deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x)
          (Complex.arg z) ∂wedgeArcSurfaceMeasure θ) := by
      rw [integral_finsetSum s (fun n _ => hleft n)]
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_complex_ofReal]
    _ = ∑ n ∈ s, c n * (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
        Complex.ofReal (∫ z, g (Complex.arg z) * (Real.sqrt (2 / θ) *
          sinMode (-θ / 2) θ (n + 1) (Complex.arg z)) ∂wedgeArcSurfaceMeasure θ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [wedgeArc_sine_weak_eigenfunction hθ hθ' n hg hgc hg'c ha hb]
      push_cast
      ring
    _ = ∫ z, ∑ n ∈ s, c n * (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
        ((g (Complex.arg z) * (Real.sqrt (2 / θ) *
          sinMode (-θ / 2) θ (n + 1) (Complex.arg z)) : ℝ) : ℂ)
          ∂wedgeArcSurfaceMeasure θ := by
      rw [integral_finsetSum s (fun n _ => hright n)]
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_complex_ofReal]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      rw [hz, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [wedgeArcSineMode, Complex.ofReal_mul]
      ring

end LatticeProb
