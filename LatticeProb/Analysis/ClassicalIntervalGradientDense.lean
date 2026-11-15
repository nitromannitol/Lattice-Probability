import LatticeProb.Analysis.ClassicalIntervalGradientDensity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Density of the classical interval gradient domain -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ComplexConjugate

namespace LatticeProb

open LQGMetric.HeatSq

/-- The classical zero-boundary gradient has dense domain on a nonempty interval. -/
theorem classicalIntervalGradient_domain_dense {a b : ℝ} (hab : a < b) :
    (classicalIntervalGradient a b).domain.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
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
        have hi : inner ℂ ((intervalSineMode_memLp a b n).toLp
            (intervalSineMode a (b - a) n)) f = 0 :=
          (Submodule.mem_orthogonal _ f).mp hf _
            (intervalSineMode_mem_classicalIntervalGradient_domain hab n)
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

end LatticeProb
