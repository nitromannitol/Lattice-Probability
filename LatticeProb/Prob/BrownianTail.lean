/-
The Gaussian tail of pre-Brownian motion at a single time, by the Chernoff
argument with the exact moment generating function of the normal law.

For `B` a pre-Brownian motion on a probability space, `0 < T`, `0 < a`:

    P {ω | a ≤ B T ω} ≤ exp (- a² / (2 T)).

The proof is the classical Chernoff route: on `{a ≤ B T}` the random variable
`exp (λ B T - λ a)` is at least `1`, so the indicator of the event is bounded
by it; integrating and evaluating the moment generating function of the
`N(0, T)` law at `λ = a / T` gives `exp (-λ a + T λ² / 2) = exp (- a² / (2 T))`.

This is the single-time building block of the maximal estimate
`LatticeProb.IsBrownianReal.measure_exists_le_abs_le` (the reflection
principle / dyadic chaining bound), which the sandpile paper's localization
lemma quotes.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The Gaussian tail of pre-Brownian motion at a single time.**  The
Chernoff bound with the exact moment generating function of the `N(0, T)`
law: for `0 < T`, `0 < a`, the probability that `B T` reaches `a` is at most
`exp (- a² / (2 T))`, read through `ENNReal.ofReal`. -/
theorem measure_ge_le_exp (hB : IsPreBrownianReal B P)
    {T : ℝ≥0} (hT : 0 < T) {a : ℝ} (ha : 0 < a) :
    P {ω | a ≤ B T ω} ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
  set lam := a / T with hlam
  have hlampos : 0 < lam := div_pos ha hT
  set s : Set Ω := {ω | a ≤ B T ω} with hs
  set f : Ω → ℝ := fun ω => Real.exp (-lam * a) * Real.exp (B T ω * lam) with hf
  have hpt : ∀ ω ∈ s, (1:ℝ) ≤ f ω := by
    intro ω hω
    rw [hf]
    have h1 : (1:ℝ) ≤ Real.exp (-lam * a) * Real.exp (B T ω * lam) := by
      rw [← Real.exp_add]
      have h2 : 0 ≤ -lam * a + B T ω * lam := by
        have : lam * a ≤ B T ω * lam := by
          nth_rewrite 1 [mul_comm (lam:ℝ) a]
          exact mul_le_mul_of_nonneg_right hω hlampos.le
        linarith
      exact Real.one_le_exp h2
    exact h1
  have hmeas : AEStronglyMeasurable f P := by
    obtain ⟨g, hg, hge⟩ := hB.aemeasurable T
    have hmeas' : AEStronglyMeasurable
        ((fun x => Real.exp (-lam * a) * Real.exp (x * lam)) ∘ g) P := by
      have h1 : Measurable (fun ω : Ω => Real.exp (-lam * a)) := measurable_const
      have h2 : Measurable (fun ω : Ω => Real.exp (g ω * lam)) :=
        hg.mul_const lam |>.exp
      exact (h1.mul h2).aestronglyMeasurable
    have hcomp : (fun ω => Real.exp (-lam * a) * Real.exp (B T ω * lam))
        =ᵐ[P] (fun x => Real.exp (-lam * a) * Real.exp (x * lam)) ∘ g :=
      hge.fun_comp (fun x => Real.exp (-lam * a) * Real.exp (x * lam))
    exact AEStronglyMeasurable.congr hmeas' hcomp.symm
  have hint2 : Integrable (fun ω => Real.exp (B T ω * lam)) P := by
    have hlaw : HasLaw (B T) (gaussianReal 0 T) P := hB.hasLaw_eval T
    have hint3 : Integrable (fun x => Real.exp (x * lam)) (gaussianReal 0 T) := by
      have h4 := integrable_exp_mul_gaussianReal (μ := (0:ℝ)) (v := T) lam
      exact h4.congr (ae_of_all _ fun x => by simp [mul_comm])
    rw [← hlaw.map_eq] at hint3
    exact hint3.comp_aemeasurable hlaw.aemeasurable
  have hmeas : NullMeasurableSet s P := by
    have := hB.aemeasurable T
    obtain ⟨g, hg, hge⟩ := this
    have h1 : NullMeasurableSet {ω | a ≤ g ω} P :=
      (measurableSet_le (measurable_const : Measurable fun _ : Ω => a) hg).nullMeasurableSet
    refine NullMeasurableSet.congr h1 ?_
    filter_upwards [hge] with ω hω
    show (a ≤ g ω) = (a ≤ B T ω)
    rw [hω]
  have hint : Integrable f P := by
    have h5 : f = fun ω => Real.exp (-lam * a) * Real.exp (B T ω * lam) := by rfl
    rw [h5]
    exact hint2.smul (Real.exp (-lam * a))
  -- P s ≤ ∫⁻ ofReal f
  have h6 : P s ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂P := by
    rw [← lintegral_indicator_one₀ hmeas]
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ s
    · have h1 : (1:ℝ) ≤ f ω := by
        have h4 : a * lam ≤ B T ω * lam :=
          mul_le_mul_of_nonneg_right hω hlampos.le
        have h5 : 0 ≤ -lam * a + B T ω * lam := by
          have h6' : lam * a = a * lam := by ring
          linarith
        have h6 : (1:ℝ) ≤ Real.exp (-lam * a + B T ω * lam) :=
          Real.one_le_exp_iff.mpr h5
        show (1:ℝ) ≤ Real.exp (-lam * a) * Real.exp (B T ω * lam)
        rw [← Real.exp_add]
        exact h6
      show s.indicator 1 ω ≤ ENNReal.ofReal (f ω)
      rw [Set.indicator_of_mem hω 1]
      simp only [Pi.one_apply]
      simpa using ENNReal.ofReal_le_ofReal h1
    · show s.indicator 1 ω ≤ ENNReal.ofReal (f ω)
      calc s.indicator 1 ω = 0 := Set.indicator_of_notMem hω _
        _ ≤ ENNReal.ofReal (f ω) := by norm_num

  refine le_trans h6 ?_
  have hL : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P
      = ENNReal.ofReal (∫ ω, f ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by
      apply mul_nonneg <;> exact Real.exp_pos _ |>.le)).symm
  rw [hL]
  have hint15 : ∫ ω, Real.exp (lam * B T ω) ∂P
      = Real.exp ((T:ℝ) * lam ^ 2 / 2) := by
    have hm : ProbabilityTheory.mgf (B T) P lam
        = Real.exp (0 * lam + (T:ℝ) * lam ^ 2 / 2) :=
      ProbabilityTheory.mgf_gaussianReal (hB.hasLaw_eval T).map_eq lam
    have hm2 : ProbabilityTheory.mgf (B T) P lam
        = ∫ ω, Real.exp (lam * B T ω) ∂P := rfl
    rw [hm2] at hm
    simpa using hm
  have h7 : ∫ ω, f ω ∂P = Real.exp (-lam * a) * Real.exp ((T:ℝ) * lam ^ 2 / 2) := by
    rw [hf]
    have hord : ∫ (ω : Ω), Real.exp (-lam * a) * Real.exp (B T ω * lam) ∂P
        = ∫ (ω : Ω), Real.exp (-lam * a) * Real.exp (lam * B T ω) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp only [mul_comm lam (B T ω)])
    rw [hord, integral_const_mul, hint15]
  rw [h7]
  have h8 : Real.exp (-lam * a) * Real.exp ((T:ℝ) * lam ^ 2 / 2)
      = Real.exp (-(a ^ 2 / (2 * (T:ℝ)))) := by
    rw [← Real.exp_add, hlam]
    congr 1
    field_simp
    ring
  rw [h8]


end LatticeProb
end
