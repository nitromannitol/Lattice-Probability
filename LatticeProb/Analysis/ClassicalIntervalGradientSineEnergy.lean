import LatticeProb.Analysis.ClassicalIntervalGradientClosure

/-! # Sine energy identities for the interval gradient -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ComplexConjugate

namespace LatticeProb

open LQGMetric.HeatSq

/-- The sine eigenvalue times the sine mode is square integrable. -/
theorem intervalSineEigenvalueMode_memLp (a b : ℝ) (n : ℕ) :
    MemLp (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
      intervalSineMode a (b - a) n x) 2 (volume.restrict (Ioo a b)) := by
  exact (intervalSineMode_memLp a b n).const_mul _

/-- The sine energy identity holds for every classical gradient graph pair. -/
theorem classicalIntervalGradientGraph_sine_energy {a b : ℝ} (hab : a < b)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) × Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ classicalIntervalGradientGraph a b) (n : ℕ) :
    inner ℂ ((intervalSineEigenvalueMode_memLp a b n).toLp
      (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
        intervalSineMode a (b - a) n x)) p.1 =
    inner ℂ ((intervalSineDerivative_memLp a b n).toLp
      (intervalSineDerivative a (b - a) n)) p.2 := by
  let e : ℝ → ℂ := fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
    intervalSineMode a (b - a) n x
  have hv : Continuous (intervalSineDerivative a (b - a) n) := by
    unfold intervalSineDerivative
    fun_prop
  have he : Continuous e := by
    dsimp [e, intervalSineMode, sinMode]
    fun_prop
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (intervalSineDerivative a (b - a) n) (-e x) x := by
    intro x hx
    convert (hasDerivAt_deriv_const_mul_sinMode a (b - a) 1 (n + 1) x).ofReal_comp using 1
    · funext y
      have hh := (hasDerivAt_const_mul_sinMode a (b - a) 1 (n + 1) y).deriv
      simp only [one_mul] at hh
      simp only [intervalSineDerivative, one_mul]
      exact congrArg (fun z : ℝ => (z : ℂ)) hh.symm
    · simp [e, intervalSineMode]
  obtain ⟨f, g, hf, hg, hparts⟩ := classicalIntervalGradientGraph_parts hab p hp
    hv.continuousOn hd (he.neg.intervalIntegrable a b)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : (fun x => inner ℂ (((intervalSineEigenvalueMode_memLp a b n).toLp e) x)
      (p.1 x)) =ᵐ[volume.restrict (Ioo a b)] (fun x => f x * e x) := by
    filter_upwards [(intervalSineEigenvalueMode_memLp a b n).coeFn_toLp, hf] with x hx hy
    rw [hx, hy]
    simp only [e, intervalSineMode, sinMode, RCLike.inner_apply', map_mul,
      Complex.conj_ofReal, mul_comm]
  have h2 : (fun x => inner ℂ (((intervalSineDerivative_memLp a b n).toLp
      (intervalSineDerivative a (b - a) n)) x) (p.2 x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => g x * intervalSineDerivative a (b - a) n x) := by
    filter_upwards [(intervalSineDerivative_memLp a b n).coeFn_toLp, hg] with x hx hy
    rw [hx, hy]
    simp only [intervalSineDerivative, RCLike.inner_apply', Complex.conj_ofReal, mul_comm]
  change (∫ x, inner ℂ (((intervalSineEigenvalueMode_memLp a b n).toLp e) x) (p.1 x)
      ∂volume.restrict (Ioo a b)) = _
  rw [integral_congr_ae h1, integral_congr_ae h2]
  rw [intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hparts
  simp only [mul_neg, integral_neg] at hparts
  exact neg_injective hparts

/-- The sine energy identity extends to the closure of the classical graph. -/
theorem classicalIntervalGradientGraph_closure_sine_energy {a b : ℝ} (hab : a < b)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) × Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ (classicalIntervalGradientGraph a b).topologicalClosure) (n : ℕ) :
    inner ℂ ((intervalSineEigenvalueMode_memLp a b n).toLp
      (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
        intervalSineMode a (b - a) n x)) p.1 =
    inner ℂ ((intervalSineDerivative_memLp a b n).toLp
      (intervalSineDerivative a (b - a) n)) p.2 := by
  let e := (intervalSineEigenvalueMode_memLp a b n).toLp _
  let d := (intervalSineDerivative_memLp a b n).toLp _
  have hc : IsClosed {q : _ × _ | inner ℂ e q.1 = inner ℂ d q.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (s := (classicalIntervalGradientGraph a b : Set (_ × _))) ?_ hc hp
  intro q hq
  exact classicalIntervalGradientGraph_sine_energy hab q hq n

end LatticeProb
