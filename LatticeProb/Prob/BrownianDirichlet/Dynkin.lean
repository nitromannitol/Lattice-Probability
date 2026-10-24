import LatticeProb.Prob.BrownianDirichlet.TaylorError
import LatticeProb.Prob.BrownianPathHarmonicExit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Dynkin identity at deterministic times

The compensated Taylor bound controls finite telescoping sums with generator
`(σ² / 2) Δ` on the Euclidean path carrier. It also gives a right derivative
for the expectation, so the fundamental theorem of calculus yields Dynkin’s identity.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- Continuous compactly supported observables of a scaled Brownian position are integrable. -/
lemma integrable_brownian_position {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (x : Euc d) (σ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ f (x + σ • ω t)) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hf
  have hm : Measurable (fun ω : BrownianPath d ↦ x + σ • ω t) :=
    measurable_const.add ((continuous_eval_const t).measurable.const_smul σ)
  exact (integrable_const M).mono' (hf.measurable.comp hm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ hM (x + σ • ω t)))

/-- The Laplacian of a compactly supported C² function is continuous and compactly supported. -/
lemma continuous_compactSupport_laplacian {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Continuous (Δ f) ∧ HasCompactSupport (Δ f) := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have heq : Δ f = fun x ↦ ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
    funext x
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    apply Finset.sum_congr rfl
    intro i _
    exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv f x _ _).symm
  rw [heq]
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hH : Continuous (fderiv ℝ (fderiv ℝ f)) := hD.continuous_fderiv (by norm_num)
  constructor
  · exact continuous_finsetSum _ (fun i _ ↦ by fun_prop)
  · have hentries (i : Fin d) :
        HasCompactSupport (fun x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b i)) := by
      exact ((hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left
        (g := fun Q : Euc d →L[ℝ] Euc d →L[ℝ] ℝ ↦ Q (b i) (b i)) (by simp)
    have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b i)) (fun i _ ↦ hentries i)
    have heqsum : (∑ i : Fin d, fun x : Euc d ↦
        fderiv ℝ (fderiv ℝ f) x (b i) (b i)) =
        (fun x ↦ ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i)) := by
      funext x
      exact Finset.sum_apply _ _ _
    rw [heqsum] at hsum
    exact hsum

/-- The expected value of a continuous compactly supported observable varies continuously
with the deterministic observation time. -/
lemma continuous_brownian_expectation {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (x : Euc d) (σ : ℝ) :
    Continuous (fun t : ℝ≥0 ↦ ∫ ω, f (x + σ • ω t) ∂μ) := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hf
  apply continuous_of_dominated (bound := fun _ ↦ M)
  · intro t
    exact (integrable_brownian_position hμ hf hc x σ t).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (fun ω ↦ hM (x + σ • ω t))
  · exact integrable_const M
  · apply Filter.Eventually.of_forall
    intro ω
    exact hf.comp (continuous_const.add (ω.continuous.const_smul σ))

/-- A scaled Brownian position is measurable with respect to its own deterministic past. -/
lemma measurable_brownian_position_past {d : ℕ} (x : Euc d) (σ : ℝ) (t : ℝ≥0) :
    Measurable[brownianNaturalFiltration d t]
      (fun ω : BrownianPath d ↦ x + σ • ω t) := by
  have hev : Measurable[brownianNaturalFiltration d t]
      (fun ω : BrownianPath d ↦ ω t) := by
    exact (comap_measurable (fun ω : BrownianPath d ↦ ω t)).mono
      (le_iSup₂_of_le t le_rfl le_rfl) le_rfl
  exact measurable_const.add (hev.const_smul σ)

/-- The predictable Taylor estimate bounds the actual difference of deterministic expectations,
with precisely the covariance-normalized Laplacian. -/
lemma brownian_expectation_increment_error {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (x : Euc d) (t s : ℝ≥0),
      |(∫ ω, f (x + σ • ω (t + s)) ∂μ) - (∫ ω, f (x + σ • ω t) ∂μ) -
        (s : ℝ) * (∫ ω, σ ^ 2 / 2 * Δ f (x + σ • ω t) ∂μ)| ≤
          ε * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := taylor_increment_error hμ hf hc hσ hε
  refine ⟨C, hC, fun x t s ↦ ?_⟩
  have he := h t s (fun ω ↦ x + σ • ω t) univ
    (measurable_brownian_position_past x σ t) MeasurableSet.univ
  have hi := integrable_brownian_position hμ hf.continuous hc x σ t
  have hj := integrable_brownian_position hμ hf.continuous hc x σ (t + s)
  obtain ⟨hLc, hLs⟩ := continuous_compactSupport_laplacian hf hc
  have hL := (integrable_brownian_position hμ hLc hLs x σ t).const_mul (σ ^ 2 / 2)
  have hp (ω : BrownianPath d) :
      x + σ • ω t + σ • (ω (t + s) - ω t) = x + σ • ω (t + s) := by
    rw [smul_sub]
    abel
  simp only [indicator_univ, hp] at he
  have hdiff : Integrable (fun ω : BrownianPath d ↦
      f (x + σ • ω (t + s)) - f (x + σ • ω t)) μ := hj.sub hi
  rw [integral_sub hdiff (hL.const_mul (s : ℝ)), integral_sub hj hi,
    integral_const_mul] at he
  exact he

/-- Uniform-step telescoping retains the sum of the generator expectations and bounds
its error by the number of steps times the one-step Taylor error. -/
lemma brownian_expectation_grid_error {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (x : Euc d) (s : ℝ≥0) (n : ℕ),
      |(∫ ω, f (x + σ • ω (n • s)) ∂μ) - f x -
        ∑ k ∈ Finset.range n, (s : ℝ) *
          (∫ ω, σ ^ 2 / 2 * Δ f (x + σ • ω (k • s)) ∂μ)| ≤
        (n : ℝ) * (ε * (s : ℝ) + C * (s : ℝ) ^ 2) := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨C, hC, h⟩ := brownian_expectation_increment_error hμ hf hc hσ hε
  refine ⟨C, hC, fun x s n ↦ ?_⟩
  let F : ℕ → ℝ := fun k ↦ ∫ ω, f (x + σ • ω (k • s)) ∂μ
  let G : ℕ → ℝ := fun k ↦ (s : ℝ) *
    (∫ ω, σ ^ 2 / 2 * Δ f (x + σ • ω (k • s)) ∂μ)
  have hzero : F 0 = f x := by
    dsimp only [F]
    simp only [zero_nsmul]
    calc
      _ = ∫ _ : BrownianPath d, f x ∂μ := integral_congr_ae
        ((standardBrownianLaw_eval_zero_ae hμ).mono (fun ω hω ↦ by
          rw [hω, smul_zero, add_zero]))
      _ = f x := by simp
  have hstep (k : ℕ) : |F (k + 1) - F k - G k| ≤
      ε * (s : ℝ) + C * (s : ℝ) ^ 2 := by
    simpa only [F, G, add_nsmul, one_nsmul] using h x (k • s) s
  have htel : F n - f x - ∑ k ∈ Finset.range n, G k =
      ∑ k ∈ Finset.range n, (F (k + 1) - F k - G k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub, hzero]
  change |F n - f x - ∑ k ∈ Finset.range n, G k| ≤ _
  rw [htel]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |F (k + 1) - F k - G k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (ε * (s : ℝ) + C * (s : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun k _ ↦ hstep k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Arbitrarily small linear error with a uniform quadratic remainder gives a right derivative. -/
private lemma hasDerivWithinAt_of_quadratic_increment
    {F G : ℝ → ℝ} {a : ℝ}
    (h : ∀ ε > 0, ∃ C ≥ 0, ∀ y > a,
      |F y - F a - (y - a) * G a| ≤ ε * (y - a) + C * (y - a) ^ 2) :
    HasDerivWithinAt F (G a) (Ioi a) a := by
  rw [hasDerivWithinAt_iff_tendsto]
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h (ε / 2) (by positivity)
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hnear : ∀ᶠ y in nhdsWithin a (Ioi a), y < a + δ :=
    (eventually_lt_nhds (show a < a + δ by linarith)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with y hy hya
  have hp : 0 < y - a := sub_pos.mpr hy
  have he := hbound y hy
  have hsmall : C * (y - a) < ε / 2 := by
    have hc : C < C + 1 := by linarith
    have hmul : C * (y - a) < (C + 1) * δ := by
      calc
        _ ≤ C * δ := mul_le_mul_of_nonneg_left (by linarith : y - a ≤ δ) hC
        _ < (C + 1) * δ := mul_lt_mul_of_pos_right hc hδ
    have hd : (C + 1) * δ = ε / 2 := by
      dsimp [δ]
      have hcne : C + 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hcne]
    linarith
  rw [Real.dist_eq]
  simp only [sub_zero, Real.norm_eq_abs, abs_of_pos hp, smul_eq_mul]
  rw [abs_mul, abs_inv, abs_abs, abs_of_pos hp]
  calc
    _ ≤ (y - a)⁻¹ * (ε / 2 * (y - a) + C * (y - a) ^ 2) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
    _ = ε / 2 + C * (y - a) := by field_simp
    _ < ε := by linarith

/-- Dynkin's identity at deterministic times for compactly supported C² functions,
with Brownian covariance `t I` and generator `(σ² / 2) Δ`. -/
theorem brownian_dynkin {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) (x : Euc d) (t : ℝ≥0) :
    (∫ ω, f (x + σ • ω t) ∂μ) = f x +
      ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, σ ^ 2 / 2 * Δ f (x + σ • ω s.toNNReal) ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  let F : ℝ → ℝ := fun s ↦ ∫ ω, f (x + σ • ω s.toNNReal) ∂μ
  let G : ℝ → ℝ := fun s ↦ ∫ ω, σ ^ 2 / 2 * Δ f (x + σ • ω s.toNNReal) ∂μ
  have hF : Continuous F :=
    (continuous_brownian_expectation hμ hf.continuous hc x σ).comp
      continuous_real_toNNReal
  obtain ⟨hLc, hLs⟩ := continuous_compactSupport_laplacian hf hc
  have hG : Continuous G := by
    have heq : G = fun s ↦ σ ^ 2 / 2 *
        (∫ ω, Δ f (x + σ • ω s.toNNReal) ∂μ) := by
      funext s
      exact integral_const_mul _ _
    rw [heq]
    exact continuous_const.mul
      ((continuous_brownian_expectation hμ hLc hLs x σ).comp continuous_real_toNNReal)
  have hderiv (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivWithinAt F (G a) (Ioi a) a := by
    apply hasDerivWithinAt_of_quadratic_increment
    intro ε hε
    obtain ⟨C, hC, h⟩ := brownian_expectation_increment_error hμ hf hc hσ hε
    refine ⟨C, hC, fun y hy ↦ ?_⟩
    have hadd : a.toNNReal + (y - a).toNNReal = y.toNNReal := by
      rw [← Real.toNNReal_add ha.1.le (sub_pos.mpr hy).le]
      congr 1
      ring
    have he := h x a.toNNReal (y - a).toNNReal
    simpa only [hadd, Real.coe_toNNReal _ (sub_pos.mpr hy).le] using he
  have hint := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    t.coe_nonneg hF.continuousOn hderiv (hG.intervalIntegrable _ _)
  have hzero : F 0 = f x := by
    dsimp only [F]
    rw [Real.toNNReal_zero]
    calc
      _ = ∫ _ : BrownianPath d, f x ∂μ := integral_congr_ae
        ((standardBrownianLaw_eval_zero_ae hμ).mono (fun ω hω ↦ by
          rw [hω, smul_zero, add_zero]))
      _ = f x := by simp
  rw [hzero] at hint
  have hfinal : F (t : ℝ) = f x + ∫ s in (0 : ℝ)..(t : ℝ), G s := by linarith
  simpa only [F, G, Real.toNNReal_coe] using hfinal

/-- An existing one-dimensional Brownian law satisfies Dynkin's identity for a nonzero
smooth bump at time one and scale one. -/
theorem exists_brownian_bump_dynkin :
    let b : ContDiffBump (0 : Euc 1) := ⟨1, 2, one_pos, one_lt_two⟩
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧ b (0 : Euc 1) = 1 ∧
      (∫ ω, b (ω 1) ∂μ) = 1 +
        ∫ s in (0 : ℝ)..1, ∫ ω, (1 / 2 : ℝ) * Δ (⇑b) (ω s.toNNReal) ∂μ := by
  intro b
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  have hb : b (0 : Euc 1) = 1 := b.one_of_mem_closedBall (by simp [b])
  refine ⟨μ, hμ, hb, ?_⟩
  have h := brownian_dynkin hμ b.contDiff b.hasCompactSupport
    (σ := 1) zero_lt_one (0 : Euc 1) 1
  simpa only [one_smul, zero_add, one_pow, one_div, hb, NNReal.coe_one] using h

end LatticeProb
