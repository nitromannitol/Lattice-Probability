import LatticeProb.Analysis.ClassicalIntervalGradientFiniteSines

/-! # Orthogonality to the interval sine graph -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- A vector in the closed gradient graph orthogonal to every sine graph
vector is zero. The sum of the two inner products is the Hilbert product
pairing on the graph. -/
theorem classicalIntervalGradient_closure_sine_graph_orthogonal_eq_zero {a b : ℝ}
    (hab : a < b)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) × Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ (classicalIntervalGradient a b).closure.graph)
    (horth : ∀ n : ℕ,
      inner ℂ ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)) p.1 +
      inner ℂ ((intervalSineDerivative_memLp a b n).toLp
        (intervalSineDerivative a (b - a) n)) p.2 = 0) : p = 0 := by
  have hp' : p ∈ (classicalIntervalGradientGraph a b).topologicalClosure := by
    rwa [← (classicalIntervalGradient_isClosable hab).graph_closure_eq_closure_graph,
      classicalIntervalGradient_graph] at hp
  have hcoeff : ∀ n : ℕ, (∫ x in a..b,
      (Real.sin (Real.pi * (n : ℝ) * (x - a) / (b - a)) : ℂ) * p.1 x) = 0 := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
      let s := (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)
      let d := (intervalSineDerivative_memLp a b n).toLp
        (intervalSineDerivative a (b - a) n)
      let eig : ℝ := (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2
      have he : ((intervalSineEigenvalueMode_memLp a b n).toLp
          (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
            intervalSineMode a (b - a) n x)) = (eig : ℂ) • s := by
        apply Lp.ext
        filter_upwards [(intervalSineEigenvalueMode_memLp a b n).coeFn_toLp,
          (intervalSineMode_memLp a b n).coeFn_toLp,
          Lp.coeFn_smul (eig : ℂ) s] with x hx hy hz
        change s x = _ at hy
        rw [hx, hz]
        change (eig : ℂ) * intervalSineMode a (b - a) n x = (eig : ℂ) * s x
        rw [hy]
      have henergy := classicalIntervalGradientGraph_closure_sine_energy hab p hp' n
      rw [he, inner_smul_left] at henergy
      have hpos : 0 ≤ eig := sq_nonneg _
      have hne : (1 + (eig : ℂ)) ≠ 0 := by
        have hr : (1 + eig : ℝ) ≠ 0 := by linarith
        exact_mod_cast hr
      have hi : inner ℂ s p.1 = 0 := by
        have hh := horth n
        change inner ℂ s p.1 + inner ℂ d p.2 = 0 at hh
        have hh' : (1 + (eig : ℂ)) * inner ℂ s p.1 = 0 := by
          rw [← henergy] at hh
          simpa [Complex.conj_ofReal, add_mul] using hh
        exact (mul_eq_zero.mp hh').resolve_left hne
      rw [MeasureTheory.L2.inner_def] at hi
      have heq : (fun x => inner ℂ (s x) (p.1 x)) =ᵐ[volume.restrict (Ioo a b)]
          (fun x : ℝ => (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) *
            (x - a) / (b - a)) : ℂ) * p.1 x) := by
        filter_upwards [(intervalSineMode_memLp a b n).coeFn_toLp] with x hx
        change s x = _ at hx
        rw [hx]
        simp only [intervalSineMode, sinMode, RCLike.inner_apply', Complex.conj_ofReal]
      rw [integral_congr_ae heq] at hi
      rw [intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact hi
  have hends : a + (b - a) = b := by ring
  have hz := ae_eq_zero_of_translated_interval_sine_integrals_eq_zero
    (a := a) (θ := b - a) (by linarith) (f := p.1)
    (by simpa only [hends] using Lp.memLp p.1)
    (by simpa only [hends] using hcoeff)
  rw [hends] at hz
  have hf : p.1 = 0 := by
    apply Lp.ext
    exact hz.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo a b))).symm
  obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff _).mp hp
  have hv0 : v = 0 := by
    apply Subtype.ext
    simpa [hf] using hv
  have hg : p.2 = 0 := by
    rw [← hw, hv0, LinearPMap.map_zero]
  exact Prod.ext hf hg

end LatticeProb
