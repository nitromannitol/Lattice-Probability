/-
The two steps of Gaussian concentration that do not need the logarithmic Sobolev
inequality, and the invariance of the standard Gaussian product law under a
coordinate permutation.

`LatticeProb.measure_ge_le_of_mgf_bound` is the Chernoff step of the Herbst
argument: a bound `∫ exp (λ (f - m)) ≤ exp (λ² σ² / 2)` for every positive `λ`
gives the Gaussian tail `γ.real {f - m ≥ t} ≤ exp (-t² / (2 σ²))`.  It is the
last step of every route to Gaussian concentration, whatever produces the
exponential moment bound.

`LatticeProb.map_perm_pi_gaussianReal` records that the standard Gaussian
product law on `Fin n → ℝ` is invariant under a coordinate permutation, which is
what lets a symmetric functional be handled by conditioning on one coordinate.
-/
import Mathlib
import LatticeProb.Prob.EfronStein
import LatticeProb.Prob.SubGaussian

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- The standard Gaussian product law on `Fin n → ℝ` is a probability measure. -/
theorem isProbabilityMeasure_pi_gaussianReal (n : ℕ) :
    IsProbabilityMeasure (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
  inferInstance

/-- The standard Gaussian product law on `Fin n → ℝ` is invariant under every
coordinate permutation. -/
theorem map_perm_pi_gaussianReal (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).map
        (fun x : Fin n → ℝ => fun k => x (e k))
      = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
  have h := Measure.pi_map_piCongrLeft e.symm (fun _ : Fin n => gaussianReal 0 1)
  rw [show (fun x : Fin n → ℝ => fun k => x (e k))
      = (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e.symm : (Fin n → ℝ) → (Fin n → ℝ)) by
    ext x k
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]]
  simpa [Function.comp_def] using h

/-- **The Chernoff step of the Herbst argument.**  If the exponential moment of
`f - m` is bounded by `exp (λ ^ 2 * σ ^ 2 / 2)` for every positive `λ`, then
`f - m` exceeds `t` with probability at most `exp (-(t ^ 2) / (2 * σ ^ 2))`. -/
theorem measure_ge_le_of_mgf_bound {Ω : Type*} [MeasurableSpace Ω] (γ : Measure Ω)
    [IsProbabilityMeasure γ] (f : Ω → ℝ) (m σ t : ℝ) (hσ : 0 < σ) (ht : 0 < t)
    (hint : ∀ lam : ℝ, 0 < lam → Integrable (fun x => Real.exp (lam * (f x - m))) γ)
    (hmgf : ∀ lam : ℝ, 0 < lam →
      ∫ x, Real.exp (lam * (f x - m)) ∂γ ≤ Real.exp (lam ^ 2 * σ ^ 2 / 2)) :
    γ.real {x | t ≤ f x - m} ≤ Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
  set lam : ℝ := t / σ ^ 2 with hlam
  have hlampos : 0 < lam := by positivity
  have hsub : {x | t ≤ f x - m} ⊆ {x | Real.exp (lam * t) ≤ Real.exp (lam * (f x - m))} := by
    intro x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hlampos.le)
  have h1 : γ.real {x | t ≤ f x - m}
      ≤ γ.real {x | Real.exp (lam * t) ≤ Real.exp (lam * (f x - m))} :=
    measureReal_mono hsub
  have h2 : γ.real {x | Real.exp (lam * t) ≤ Real.exp (lam * (f x - m))}
      ≤ (∫ x, Real.exp (lam * (f x - m)) ∂γ) / Real.exp (lam * t) := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      (hint lam hlampos) (Real.exp (lam * t))
    rw [le_div_iff₀ (Real.exp_pos _)]
    linarith [h]
  have h3 : (∫ x, Real.exp (lam * (f x - m)) ∂γ) / Real.exp (lam * t)
      ≤ Real.exp (lam ^ 2 * σ ^ 2 / 2) / Real.exp (lam * t) := by
    gcongr
    exact hmgf lam hlampos
  have h4 : Real.exp (lam ^ 2 * σ ^ 2 / 2) / Real.exp (lam * t)
      = Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
    rw [← Real.exp_sub]
    congr 1
    rw [hlam]
    field_simp
    ring
  linarith [h1, h2, h3, h4.le, h4.ge]

theorem integrable_exp_lipschitz_gaussian (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (L : ℝ) (hL : 0 < L) (hf : LipschitzWith ⟨L, hL.le⟩ f) (lam : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (lam * (f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hθ : 0 < |lam| * L + 1 := by positivity
  have hexp : Integrable (fun z : ℝ => Real.exp ((|lam| * L + 1) * |z|)) (gaussianReal 0 1) := by
    refine Integrable.mono'
      ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (|lam| * L + 1)).add
        (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-(|lam| * L + 1))))
      ((Real.measurable_exp.comp ((measurable_id.abs).const_mul _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      have h : Real.exp ((|lam| * L + 1) * z) ≤ Real.exp ((|lam| * L + 1) * z)
          + Real.exp (-(|lam| * L + 1) * z) := le_add_of_nonneg_right (Real.exp_pos _).le
      simpa using h
    · rw [abs_of_nonpos hz]
      rw [show (|lam| * L + 1) * -z = -(|lam| * L + 1) * z by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  refine integrable_exp_lip (gaussianReal 0 1) (|lam| * L + 1) hexp f
    hf.continuous.measurable (fun _ => L) ?_ lam ?_ _
  · intro ξ i y
    have hd : dist ξ (Function.update ξ i y) ≤ |ξ i - y| := by
      rw [dist_pi_le_iff (abs_nonneg _)]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Real.dist_eq]
      · rw [Function.update_of_ne hj, Real.dist_eq, sub_self, abs_zero]
        positivity
    have h := hf.dist_le_mul ξ (Function.update ξ i y)
    rw [Real.dist_eq] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hd hL.le)
  · intro i
    linarith


end LatticeProb
