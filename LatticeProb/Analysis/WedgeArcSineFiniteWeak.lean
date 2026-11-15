import LatticeProb.Analysis.WedgeArcSineCoreWeak

/-! # Finite angular sine combinations -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- The angular core acts diagonally on finite complex linear combinations. -/
theorem wedgeArcSineCore_apply_finset {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (s : Finset ℕ) (c : ℕ → ℂ) :
    wedgeArcSineCore hθ hθ'
      (∑ n ∈ s, c n • ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩) =
      ∑ n ∈ s, c n •
        ((((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) • wedgeArcSineLp θ n) := by
  simp only [map_sum, map_smul, wedgeArcSineCore_apply_mode]

/-- The core output has the explicit finite sine sum as an almost-everywhere representative. -/
theorem wedgeArcSineCore_finset_ae {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (s : Finset ℕ) (c : ℕ → ℂ) :
    (fun z => wedgeArcSineCore hθ hθ'
      (∑ n ∈ s, c n • ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩) z)
      =ᵐ[wedgeArcSurfaceMeasure θ] fun z =>
        ∑ n ∈ s, c n * (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
          wedgeArcSineMode θ n z := by
  rw [wedgeArcSineCore_apply_finset]
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun n => c n •
      ((((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) • wedgeArcSineLp θ n)),
    ae_all_iff.mpr (fun n : ℕ => Lp.coeFn_smul (c n)
      ((((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) • wedgeArcSineLp θ n)),
    ae_all_iff.mpr (fun n : ℕ => Lp.coeFn_smul
      (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) (wedgeArcSineLp θ n)),
    ae_all_iff.mpr (fun n : ℕ => (wedgeArcSineMode_memLp θ n).coeFn_toLp)]
      with z hsum hc hl hn
  rw [hsum]
  apply Finset.sum_congr rfl
  intro n hnmem
  rw [hc n]
  simp only [Pi.smul_apply]
  rw [hl n]
  simp only [Pi.smul_apply]
  have hmode : wedgeArcSineLp θ n z = wedgeArcSineMode θ n z := hn n
  rw [hmode]
  simp only [smul_eq_mul, mul_assoc]

/-- A finite linear combination inherits the weak equation mode by mode. -/
theorem wedgeArcSineCore_finset_weak {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (s : Finset ℕ) (c : ℕ → ℂ) {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt g (g' x) x)
    (hgc : Continuous g) (hg'c : Continuous g')
    (ha : g (-θ / 2) = 0) (hb : g (θ / 2) = 0) :
    (∑ n ∈ s, c n * Complex.ofReal (∫ z, g' (Complex.arg z) *
      deriv (fun x => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) x)
        (Complex.arg z) ∂wedgeArcSurfaceMeasure θ)) =
    ∑ n ∈ s, c n * Complex.ofReal (∫ z, g (Complex.arg z) *
      (wedgeArcSineCore hθ hθ'
        ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩ z).re
        ∂wedgeArcSurfaceMeasure θ) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [wedgeArcSineCore_mode_weak hθ hθ' n hg hgc hg'c ha hb]

end LatticeProb
