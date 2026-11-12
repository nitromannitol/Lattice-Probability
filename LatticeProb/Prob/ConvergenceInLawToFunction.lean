import Mathlib

/-!
# Convergence in law to a function of the data is convergence in probability

Let `X` be a random element of a pseudo-metrizable space `S`, let `u : S → ℝ` be a bounded measurable function
and let `R n` be uniformly bounded real random variables on the same probability space. If the pairs
`(X, R n)` converge in law to `(X, u X)`, then `R n → u X` in probability.

This is the elementary fact that convergence in distribution to a constant implies convergence in
probability, relative to the fixed first coordinate `X`: the limit law is carried by the graph of `u`.
Since `u` is only measurable, the graph is approximated through the density of bounded continuous
functions in `L¹` of the law of `X`.

* `tendstoInMeasure_of_tendsto_integral_graph`: the statement, with convergence in law expressed by
  convergence of the integrals of bounded continuous functions of `S × ℝ`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace LatticeProb

variable {Ω S : Type*} [MeasurableSpace Ω] [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- **Convergence in law of `(X, R n)` to `(X, u X)` gives convergence in probability of `R n` to `u X`.**
The random variables `R n` and the function `u` are bounded by `C`, `u` is measurable, and for every bounded
continuous `f : S × ℝ → ℝ` the integrals `∫ f (X, R n) dP` converge to `∫ f (X, u X) dP`. -/
theorem tendstoInMeasure_of_tendsto_integral_graph (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → S} (hX : Measurable X) {R : ℕ → Ω → ℝ} (hR : ∀ n, Measurable (R n)) {u : S → ℝ}
    (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C) (hRC : ∀ n ω, |R n ω| ≤ C) (huC : ∀ x, |u x| ≤ C)
    (hlaw : ∀ f : (S × ℝ) →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (X ω, R n ω) ∂P) atTop
      (𝓝 (∫ ω, f (X ω, u (X ω)) ∂P))) :
    TendstoInMeasure P R atTop (fun ω => u (X ω)) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  suffices h : Tendsto (fun n => (P {ω | ε ≤ ‖R n ω - u (X ω)‖}).toReal) atTop (𝓝 0) by
    exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) ENNReal.zero_ne_top).1 h
  rw [Metric.tendsto_atTop]
  intro η hη
  have : IsProbabilityMeasure (P.map X) := ⟨by rw [Measure.map_apply hX MeasurableSet.univ]; simp⟩
  have huL : MemLp u (ENNReal.ofReal 1) (P.map X) :=
    MemLp.of_bound hu.aestronglyMeasurable C (ae_of_all _ fun x => by simpa using huC x)
  obtain ⟨g, hg, -⟩ := huL.exists_boundedContinuous_integral_rpow_sub_le (p := 1) one_pos
    (ε := η * ε / 4) (by positivity)
  -- clip the approximant to `[-C, C]`
  set cl : ℝ → ℝ := fun y => max (-C) (min C y) with hcl
  have hclc : Continuous cl := by fun_prop
  have hclb : ∀ y, |cl y| ≤ C := fun y => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hcl_id : ∀ y, |y| ≤ C → cl y = y := fun y hy => by
    rw [abs_le] at hy
    simp only [hcl, min_eq_right hy.2, max_eq_right hy.1]
  have hcl_lip : ∀ y z, |z| ≤ C → |cl y - z| ≤ |y - z| := by
    intro y z hz
    rw [abs_le] at hz
    simp only [hcl]
    rcases le_total y (-C) with h1 | h1
    · rw [min_eq_right (by linarith), max_eq_left h1, abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
    · rcases le_total y C with h2 | h2
      · rw [min_eq_right h2, max_eq_right h1]
      · rw [min_eq_left h2, max_eq_right (by linarith), abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        linarith
  set gcl : S → ℝ := fun x => cl (g x) with hgcl
  have hgclc : Continuous gcl := hclc.comp g.continuous
  have hXm : Measurable (fun ω => gcl (X ω)) := hgclc.measurable.comp hX
  have hgm : Measurable (fun ω => g (X ω)) := g.continuous.measurable.comp hX
  have hum : Measurable (fun ω => u (X ω)) := hu.comp hX
  have hbd : ∀ {F : Ω → ℝ}, Measurable F → ∀ K : ℝ, (∀ ω, ‖F ω‖ ≤ K) → Integrable F P :=
    fun hF K hK => Integrable.of_bound hF.aestronglyMeasurable K (ae_of_all _ hK)
  let f : (S × ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => ‖cl p.2 - gcl p.1‖) (by fun_prop) (2 * C) (fun p => by
      obtain ⟨a1, a2⟩ := abs_le.mp (hclb p.2)
      obtain ⟨b1, b2⟩ := abs_le.mp (hclb (g p.1))
      rw [norm_norm, Real.norm_eq_abs, abs_le]
      exact ⟨by simp only [hgcl]; linarith, by simp only [hgcl]; linarith⟩)
  set A : ℕ → ℝ := fun n => ∫ ω, ‖R n ω - gcl (X ω)‖ ∂P with hA
  set B : ℝ := ∫ ω, ‖u (X ω) - gcl (X ω)‖ ∂P with hB
  have hlim : Tendsto A atTop (𝓝 B) := by
    have h1 : ∀ n, ∫ ω, f (X ω, R n ω) ∂P = A n := fun n => by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      show ‖cl (R n ω) - gcl (X ω)‖ = ‖R n ω - gcl (X ω)‖
      rw [hcl_id _ (hRC n ω)]
    have h2 : ∫ ω, f (X ω, u (X ω)) ∂P = B := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      show ‖cl (u (X ω)) - gcl (X ω)‖ = ‖u (X ω) - gcl (X ω)‖
      rw [hcl_id _ (huC _)]
    have h3 := hlaw f
    simpa only [h1, h2] using h3
  have hgbd : ∀ ω, ‖g (X ω)‖ ≤ ‖g‖ := fun ω => g.norm_coe_le_norm _
  have hBle : B ≤ η * ε / 4 := by
    have h4 : ∫ x, ‖u x - g x‖ ∂(P.map X) ≤ η * ε / 4 := by simpa only [Real.rpow_one] using hg
    rw [integral_map (f := fun x => ‖u x - g x‖) hX.aemeasurable
      ((hu.sub g.continuous.measurable).norm.aestronglyMeasurable)] at h4
    refine le_trans ?_ h4
    refine integral_mono (hbd (hum.sub hXm).norm (2 * C) fun ω => ?_)
      (hbd (hum.sub hgm).norm (C + ‖g‖) fun ω => ?_) fun ω => ?_
    · obtain ⟨a1, a2⟩ := abs_le.mp (huC (X ω))
      obtain ⟨b1, b2⟩ := abs_le.mp (hclb (g (X ω)))
      rw [norm_norm, Real.norm_eq_abs, abs_le]
      exact ⟨by simp only [hgcl]; linarith, by simp only [hgcl]; linarith⟩
    · have := huC (X ω)
      have := hgbd ω
      rw [norm_norm, Real.norm_eq_abs]
      calc |u (X ω) - g (X ω)| ≤ |u (X ω)| + |g (X ω)| := abs_sub _ _
        _ ≤ C + ‖g‖ := by rw [← Real.norm_eq_abs (g (X ω))] at *; linarith
    · simp only [Real.norm_eq_abs]
      rw [abs_sub_comm (u (X ω)) (gcl (X ω)), abs_sub_comm (u (X ω)) (g (X ω))]
      exact hcl_lip _ _ (huC _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (η * ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hAn : A n < B + η * ε / 4 := by
    have := hN n hn
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hb1 : ∀ ω, ‖‖R n ω - gcl (X ω)‖‖ ≤ 2 * C := fun ω => by
    obtain ⟨a1, a2⟩ := abs_le.mp (hRC n ω)
    obtain ⟨b1, b2⟩ := abs_le.mp (hclb (g (X ω)))
    rw [norm_norm, Real.norm_eq_abs, abs_le]
    exact ⟨by simp only [hgcl]; linarith, by simp only [hgcl]; linarith⟩
  have hb2 : ∀ ω, ‖‖u (X ω) - gcl (X ω)‖‖ ≤ 2 * C := fun ω => by
    obtain ⟨a1, a2⟩ := abs_le.mp (huC (X ω))
    obtain ⟨b1, b2⟩ := abs_le.mp (hclb (g (X ω)))
    rw [norm_norm, Real.norm_eq_abs, abs_le]
    exact ⟨by simp only [hgcl]; linarith, by simp only [hgcl]; linarith⟩
  have hi1 : Integrable (fun ω => ‖R n ω - gcl (X ω)‖) P := hbd ((hR n).sub hXm).norm _ hb1
  have hi2 : Integrable (fun ω => ‖u (X ω) - gcl (X ω)‖) P := hbd (hum.sub hXm).norm _ hb2
  have hsub : {ω | ε ≤ ‖R n ω - u (X ω)‖} ⊆
      {ω | ε ≤ ‖R n ω - gcl (X ω)‖ + ‖u (X ω) - gcl (X ω)‖} := fun ω hω => by
    have := norm_sub_le_norm_sub_add_norm_sub (R n ω) (gcl (X ω)) (u (X ω))
    rw [norm_sub_rev (gcl (X ω))] at this
    exact le_trans hω this
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => ‖R n ω - gcl (X ω)‖ + ‖u (X ω) - gcl (X ω)‖)
    (ae_of_all _ fun ω => by positivity) (hi1.add hi2) ε
  rw [integral_add hi1 hi2] at hmk
  have hle : (P {ω | ε ≤ ‖R n ω - u (X ω)‖}).toReal ≤
      (P {ω | ε ≤ ‖R n ω - gcl (X ω)‖ + ‖u (X ω) - gcl (X ω)‖}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  simp only [measureReal_def] at hmk
  have h5 : ε * (P {ω | ε ≤ ‖R n ω - u (X ω)‖}).toReal < ε * η := by
    have := mul_le_mul_of_nonneg_left hle hε.le
    nlinarith [hmk, hAn, hBle, mul_pos hη hε]
  exact lt_of_mul_lt_mul_left h5 hε.le

end LatticeProb
