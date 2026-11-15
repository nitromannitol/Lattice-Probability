import LatticeProb.Analysis.WedgeArcSineBasis

/-! # Completeness of the sine modes on a circular arc -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal ComplexConjugate

namespace LatticeProb

/-- The positive angular sine modes have trivial orthogonal complement. -/
theorem wedgeArcSineLp_orthogonal_eq_bot {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    (Submodule.span ℂ (Set.range (wedgeArcSineLp θ)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    apply Lp.ext
    have hcoeff : ∀ n : ℕ, (∫ z : sphere (0 : ℂ) 1,
        (Real.sin (Real.pi * (n : ℝ) * (Complex.arg z - (-θ / 2)) / θ) : ℂ) * f z
        ∂(wedgeArcSurfaceMeasure θ)) = 0 := by
      intro n
      cases n with
      | zero => simp
      | succ n =>
        have hi : inner ℂ (wedgeArcSineLp θ n) f = 0 :=
          (Submodule.mem_orthogonal _ f).mp hf _
            (Submodule.subset_span ⟨n, rfl⟩)
        rw [MeasureTheory.L2.inner_def] at hi
        have heq : (fun z => inner ℂ (wedgeArcSineLp θ n z) (f z)) =ᵐ[wedgeArcSurfaceMeasure θ]
            (fun z : sphere (0 : ℂ) 1 => (Real.sqrt (2 / θ) : ℂ) *
              ((Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) *
                (Complex.arg z - (-θ / 2)) / θ) : ℂ) * f z)) := by
          filter_upwards [(wedgeArcSineMode_memLp θ n).coeFn_toLp] with z hz
          change wedgeArcSineLp θ n z = _ at hz
          rw [hz]
          simp only [wedgeArcSineMode, LQGMetric.HeatSq.sinMode, RCLike.inner_apply',
            Complex.ofReal_mul, map_mul, Complex.conj_ofReal, mul_assoc]
        rw [integral_congr_ae heq, integral_const_mul] at hi
        have hs : (Real.sqrt (2 / θ) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (div_pos (by norm_num) hθ)))
        exact (mul_eq_zero.mp hi).resolve_left hs
    have hz := ae_eq_zero_of_wedge_arc_sine_integrals_eq_zero hθ hθ'
      (Lp.memLp f) hcoeff
    exact hz.trans (Lp.coeFn_zero ℂ 2 (wedgeArcSurfaceMeasure θ)).symm
  · exact bot_le

/-- The normalized positive sine modes form a Hilbert basis of the arc. -/
noncomputable def wedgeArcSineHilbertBasis {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_wedgeArcSineLp hθ hθ')
    (wedgeArcSineLp_orthogonal_eq_bot hθ hθ')

@[simp] theorem wedgeArcSineHilbertBasis_apply {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) :
    wedgeArcSineHilbertBasis hθ hθ' n = wedgeArcSineLp θ n := by
  rw [wedgeArcSineHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

end LatticeProb
