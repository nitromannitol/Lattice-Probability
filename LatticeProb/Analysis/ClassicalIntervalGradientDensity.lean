import LatticeProb.Analysis.ClassicalIntervalGradient
import LatticeProb.Analysis.IntervalSineEigenmodes
import LatticeProb.Analysis.TranslatedIntervalSineUniqueness
import Mathlib.Analysis.Complex.RealDeriv

/-! # Sine modes in the classical interval gradient domain -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- A differentiable zero-boundary representative with square-integrable
function and derivative belongs to the classical gradient domain. -/
theorem mem_classicalIntervalGradient_domain_of_representative {a b : ℝ}
    {f g : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hc : ContinuousOn f (Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    hf.toLp f ∈ (classicalIntervalGradient a b).domain := by
  apply LinearPMap.mem_domain_of_mem_graph
  rw [classicalIntervalGradient_graph]
  exact ⟨f, g, hf.coeFn_toLp, hg.coeFn_toLp, hc, ha, hb, hd⟩

/-- The unnormalized sine mode on an interval. -/
noncomputable def intervalSineMode (a L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (sinMode a L (n + 1) x : ℂ)

/-- The derivative of the unnormalized sine mode. -/
noncomputable def intervalSineDerivative (a L : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.pi * (n + 1 : ℕ) / L *
    Real.cos (Real.pi * (n + 1 : ℕ) / L * (x - a)) : ℝ) : ℂ)

theorem intervalSineMode_memLp (a b : ℝ) (n : ℕ) :
    MemLp (intervalSineMode a (b - a) n) 2 (volume.restrict (Ioo a b)) := by
  have hm : Continuous (intervalSineMode a (b - a) n) := by
    unfold intervalSineMode sinMode
    fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with x
  change ‖(sinMode a (b - a) (n + 1) x : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

theorem intervalSineDerivative_memLp (a b : ℝ) (n : ℕ) :
    MemLp (intervalSineDerivative a (b - a) n) 2 (volume.restrict (Ioo a b)) := by
  have hm : Continuous (intervalSineDerivative a (b - a) n) := by
    unfold intervalSineDerivative
    fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable |Real.pi * (n + 1 : ℕ) / (b - a)|
  filter_upwards [] with x
  simp only [intervalSineDerivative, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |Real.pi * (n + 1 : ℕ) / (b - a)| * 1 := by
      gcongr
      exact Real.abs_cos_le_one _
    _ = _ := mul_one _

/-- Each interval sine mode lies in the classical gradient domain. -/
theorem intervalSineMode_mem_classicalIntervalGradient_domain {a b : ℝ}
    (hab : a < b) (n : ℕ) :
    (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n) ∈
      (classicalIntervalGradient a b).domain := by
  apply mem_classicalIntervalGradient_domain_of_representative
    (intervalSineMode_memLp a b n) (intervalSineDerivative_memLp a b n)
  · have hc : Continuous (intervalSineMode a (b - a) n) := by
      unfold intervalSineMode sinMode
      fun_prop
    exact hc.continuousOn
  · have h := (sinMode_const_mul_endpoints a (b - a) 1 (n + 1) (by linarith)).1
    simpa [intervalSineMode] using congrArg (fun x : ℝ => (x : ℂ)) h
  · have h := (sinMode_const_mul_endpoints a (b - a) 1 (n + 1) (by linarith)).2
    have he : a + (b - a) = b := by ring
    rw [he] at h
    simpa [intervalSineMode] using congrArg (fun x : ℝ => (x : ℂ)) h
  · intro x hx
    convert (hasDerivAt_const_mul_sinMode a (b - a) 1 (n + 1) x).ofReal_comp using 1 <;>
      simp only [intervalSineDerivative, one_mul]
    funext y
    rfl

end LatticeProb
