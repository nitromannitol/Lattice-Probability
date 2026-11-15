import LatticeProb.Analysis.WedgeArcSineSingleWeak

/-! # Representatives of finite angular sine combinations -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

open LQGMetric.HeatSq

/-- A finite sine-core input is represented by the corresponding pointwise sum. -/
theorem wedgeArcSine_input_finset_ae (θ : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    (fun z => (∑ n ∈ s, c n • wedgeArcSineLp θ n) z)
      =ᵐ[wedgeArcSurfaceMeasure θ] fun z =>
        ∑ n ∈ s, c n * wedgeArcSineMode θ n z := by
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun n => c n • wedgeArcSineLp θ n),
    ae_all_iff.mpr (fun n : ℕ => Lp.coeFn_smul (c n) (wedgeArcSineLp θ n)),
    ae_all_iff.mpr (fun n : ℕ => (wedgeArcSineMode_memLp θ n).coeFn_toLp)]
      with z hsum hc hn
  rw [hsum]
  apply Finset.sum_congr rfl
  intro n hnmem
  rw [hc n]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hmode : wedgeArcSineLp θ n z = wedgeArcSineMode θ n z := hn n
  rw [hmode]

/-- The angular derivative of a finite complex sine combination is the sum of the
mode derivatives. -/
theorem hasDerivAt_wedgeArcSine_finset (θ : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑ n ∈ s, c n *
      ((Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) y : ℝ) : ℂ))
      (∑ n ∈ s, c n * ((deriv (fun y => Real.sqrt (2 / θ) *
        sinMode (-θ / 2) θ (n + 1) y) x : ℝ) : ℂ)) x := by
  apply HasDerivAt.fun_sum
  intro n hn
  exact ((hasDerivAt_const_mul_sinMode (-θ / 2) θ (Real.sqrt (2 / θ))
    (n + 1) x).ofReal_comp.const_mul (c n)).congr_deriv (by
      rw [(hasDerivAt_const_mul_sinMode (-θ / 2) θ (Real.sqrt (2 / θ))
        (n + 1) x).deriv])

/-- The finite sine-core weak equation written using the derivative of its explicit
angular representative. -/
theorem wedgeArcSineCore_finset_deriv_weak {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (s : Finset ℕ) (c : ℕ → ℂ) {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt g (g' x) x)
    (hgc : Continuous g) (hg'c : Continuous g')
    (ha : g (-θ / 2) = 0) (hb : g (θ / 2) = 0) :
    (∫ z, (g' (Complex.arg z) : ℂ) *
      deriv (fun y : ℝ => ∑ n ∈ s, c n *
        ((Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) y : ℝ) : ℂ))
        (Complex.arg z) ∂wedgeArcSurfaceMeasure θ) =
    ∫ z, (g (Complex.arg z) : ℂ) *
      wedgeArcSineCore hθ hθ'
        (∑ n ∈ s, c n • ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩) z
        ∂wedgeArcSurfaceMeasure θ := by
  convert wedgeArcSineCore_finset_single_weak hθ hθ' s c hg hgc hg'c ha hb using 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [(hasDerivAt_wedgeArcSine_finset θ s c (Complex.arg z)).deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.ofReal_mul]
  ring

end LatticeProb
