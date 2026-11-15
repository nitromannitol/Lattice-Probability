import LatticeProb.Analysis.ClassicalIntervalGradientDense
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen5
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Sine Hilbert basis on an interval -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- The normalized positive sine modes on an interval. -/
noncomputable def intervalNormalizedSineLp (a b : ℝ) (n : ℕ) :
    Lp ℂ 2 (volume.restrict (Ioo a b)) :=
  (Real.sqrt (2 / (b - a)) : ℂ) •
    (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)

/-- The normalized positive sine modes are orthonormal. -/
theorem orthonormal_intervalNormalizedSineLp {a b : ℝ} (hab : a < b) :
    Orthonormal ℂ (intervalNormalizedSineLp a b) := by
  rw [orthonormal_iff_ite]
  intro j k
  have hL : 0 < b - a := by linarith
  have he : a + (b - a) = b := by ring
  have hi := integral_sinMode_mul_sinMode (a := a) (L := b - a) hL
    (j := j + 1) (k := k + 1) (by omega)
  rw [he] at hi
  rw [intervalNormalizedSineLp, intervalNormalizedSineLp, inner_smul_left, inner_smul_right]
  rw [MeasureTheory.L2.inner_def]
  have heq : (fun x => inner ℂ
      (((intervalSineMode_memLp a b j).toLp (intervalSineMode a (b - a) j)) x)
      (((intervalSineMode_memLp a b k).toLp (intervalSineMode a (b - a) k)) x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => ((sinMode a (b - a) (j + 1) x * sinMode a (b - a) (k + 1) x : ℝ) : ℂ)) := by
    filter_upwards [(intervalSineMode_memLp a b j).coeFn_toLp,
      (intervalSineMode_memLp a b k).coeFn_toLp] with x hj hk
    rw [hj, hk]
    simp only [intervalSineMode, RCLike.inner_apply', Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_congr_ae heq, integral_complex_ofReal, hi]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← mul_assoc, ← sq, Real.sq_sqrt (show 0 ≤ 2 / (b - a) by positivity)]
  have hn : 2 / (b - a) * ((b - a) / 2) = (1 : ℝ) := by
    field_simp
  by_cases h : j = k
  · subst j
    simp [hn]
  · simp [h]

/-- The positive sine modes have trivial orthogonal complement. -/
theorem intervalNormalizedSineLp_orthogonal_eq_bot {a b : ℝ} (hab : a < b) :
    (Submodule.span ℂ (Set.range (intervalNormalizedSineLp a b)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    apply Lp.ext
    have hcoeff : ∀ n : ℕ, (∫ x in a..b,
        (Real.sin (Real.pi * (n : ℝ) * (x - a) / (b - a)) : ℂ) * f x) = 0 := by
      intro n
      cases n with
      | zero => simp
      | succ n =>
        have hi : inner ℂ (intervalNormalizedSineLp a b n) f = 0 :=
          (Submodule.mem_orthogonal _ f).mp hf _ (Submodule.subset_span ⟨n, rfl⟩)
        rw [intervalNormalizedSineLp, inner_smul_left, Complex.conj_ofReal] at hi
        have hs : (Real.sqrt (2 / (b - a)) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (div_pos (by norm_num) (by linarith))))
        have hi := (mul_eq_zero.mp hi).resolve_left hs
        rw [MeasureTheory.L2.inner_def] at hi
        have heq : (fun x => inner ℂ (((intervalSineMode_memLp a b n).toLp
            (intervalSineMode a (b - a) n)) x) (f x)) =ᵐ[volume.restrict (Ioo a b)]
            (fun x : ℝ => (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) *
              (x - a) / (b - a)) : ℂ) * f x) := by
          filter_upwards [(intervalSineMode_memLp a b n).coeFn_toLp] with x hx
          rw [hx]
          simp only [intervalSineMode, sinMode, RCLike.inner_apply', Complex.conj_ofReal]
        rw [integral_congr_ae heq] at hi
        rw [intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact hi
    have hends : a + (b - a) = b := by ring
    have hz := ae_eq_zero_of_translated_interval_sine_integrals_eq_zero
      (a := a) (θ := b - a) (by linarith) (f := f)
      (by simpa only [hends] using Lp.memLp f)
      (by simpa only [hends] using hcoeff)
    rw [hends] at hz
    exact hz.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo a b))).symm
  · exact bot_le

/-- The normalized positive sine modes form a Hilbert basis. -/
noncomputable def intervalSineHilbertBasis {a b : ℝ} (hab : a < b) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Ioo a b))) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_intervalNormalizedSineLp hab)
    (intervalNormalizedSineLp_orthogonal_eq_bot hab)

@[simp] theorem intervalSineHilbertBasis_apply {a b : ℝ} (hab : a < b) (n : ℕ) :
    intervalSineHilbertBasis hab n = intervalNormalizedSineLp a b n := by
  rw [intervalSineHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

end LatticeProb
