import Mathlib
import LatticeProb.Walk.ContinuousHeat

/-!
# The planar potential kernel in Fourier form

`fourierPotential x = (2π)^{-2} ∫_{[-π,π]²} (1 - cos θ·x) / (1 - φ(θ)) dθ`. The
partial sums `G_M(0) - G_M(x) = ∑_{j<M} [P^j(0,0) - P^j(0,x)]` are the torus integrals of
`(∑_{n<M} φⁿ)(1 - cos θ·x)`, which are dominated by `π²|x|²` because
`1 - φ(θ) ≥ |θ|²/π²` on the torus, and converge almost everywhere since `|φ| < 1` off a
null set; dominated convergence gives `G_M(0) - G_M(x) → fourierPotential x`
(`tendsto_srwGreen_sub_fourierPotential`). Tonelli then writes the limit as the time
integral `∫_0^∞ [q_t(0) - q_t(x)] dt` of the continuous-time kernel
(`fourierPotential_eq_integral_ctHeat`).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.ContinuousTime

/-- The Fourier form of the planar potential kernel,
`(2π)^{-2} ∫_{[-π,π]²} (1 - cos θ·x) / (1 - φ(θ)) dθ`. -/
def fourierPotential (x : Site 2) : ℝ :=
  (∫ θ in LocalCLT.torusBox 2, (1 - Real.cos (dotSite θ x)) / (1 - charFn 2 θ))
    / (2 * Real.pi) ^ 2

/-- The pointwise identity rewriting the summed difference of character terms. -/
private lemma sum_charFn_mul (M : ℕ) (x : Site 2) (θ : Fin 2 → ℝ) :
    ∑ n ∈ Finset.range M, (Real.cos (dotSite θ 0) * charFn 2 θ ^ n
        - Real.cos (dotSite θ x) * charFn 2 θ ^ n)
      = (∑ n ∈ Finset.range M, charFn 2 θ ^ n) * (1 - Real.cos (dotSite θ x)) := by
  have h0 : dotSite θ (0 : Site 2) = 0 := by simp [dotSite]
  rw [h0, Real.cos_zero]
  calc
    ∑ n ∈ Finset.range M,
        (1 * charFn 2 θ ^ n - Real.cos (dotSite θ x) * charFn 2 θ ^ n)
        = ∑ n ∈ Finset.range M, charFn 2 θ ^ n * (1 - Real.cos (dotSite θ x)) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (∑ n ∈ Finset.range M, charFn 2 θ ^ n) * (1 - Real.cos (dotSite θ x)) := by
          rw [Finset.sum_mul]

/-- The planar partial sums in Fourier form:
`G_M(0) - G_M(x) = (2π)^{-2} ∫ (∑_{n<M} φⁿ)(1 - cos θ·x) dθ`. -/
theorem srwGreen_sub_eq_integral (M : ℕ) (x : Site 2) :
    srwGreen 2 M 0 - srwGreen 2 M x
      = (∫ θ in LocalCLT.torusBox 2,
          (∑ n ∈ Finset.range M, charFn 2 θ ^ n) * (1 - Real.cos (dotSite θ x)))
        / (2 * Real.pi) ^ 2 := by
  have hc : ∀ y : Site 2, ∀ n : ℕ, Continuous
      (fun θ : Fin 2 → ℝ => Real.cos (dotSite θ y) * charFn 2 θ ^ n) := by
    intro y n
    unfold charFn dotSite
    fun_prop
  have hi : ∀ y : Site 2, ∀ n : ℕ,
      Integrable (fun θ : Fin 2 → ℝ => Real.cos (dotSite θ y) * charFn 2 θ ^ n)
        (volume.restrict (LocalCLT.torusBox 2)) :=
    fun y n => (hc y n).integrableOn_Icc (μ := volume)
      (a := fun _ => -Real.pi) (b := fun _ => Real.pi)
  calc
    srwGreen 2 M 0 - srwGreen 2 M x
        = ∑ n ∈ Finset.range M, (srwHeat 2 n 0 - srwHeat 2 n x) := by
          simp only [srwGreen]
          rw [← Finset.sum_sub_distrib]
    _ = ∑ n ∈ Finset.range M,
          ((∫ θ in LocalCLT.torusBox 2, Real.cos (dotSite θ 0) * charFn 2 θ ^ n)
            - ∫ θ in LocalCLT.torusBox 2, Real.cos (dotSite θ x) * charFn 2 θ ^ n)
            / (2 * Real.pi) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [srwHeat_eq_integral_cos (by norm_num : 1 ≤ 2),
              srwHeat_eq_integral_cos (by norm_num : 1 ≤ 2), sub_div]
    _ = ∑ n ∈ Finset.range M,
          (∫ θ in LocalCLT.torusBox 2, (Real.cos (dotSite θ 0) * charFn 2 θ ^ n
            - Real.cos (dotSite θ x) * charFn 2 θ ^ n)) / (2 * Real.pi) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [integral_sub (hi 0 n) (hi x n)]
    _ = (∑ n ∈ Finset.range M,
          ∫ θ in LocalCLT.torusBox 2, (Real.cos (dotSite θ 0) * charFn 2 θ ^ n
            - Real.cos (dotSite θ x) * charFn 2 θ ^ n)) / (2 * Real.pi) ^ 2 := by
          rw [Finset.sum_div]
    _ = (∫ θ in LocalCLT.torusBox 2, ∑ n ∈ Finset.range M,
          (Real.cos (dotSite θ 0) * charFn 2 θ ^ n
            - Real.cos (dotSite θ x) * charFn 2 θ ^ n)) / (2 * Real.pi) ^ 2 := by
          rw [integral_finsetSum]
          intro n hn
          exact (hi 0 n).sub (hi x n)
    _ = (∫ θ in LocalCLT.torusBox 2,
          (∑ n ∈ Finset.range M, charFn 2 θ ^ n) * (1 - Real.cos (dotSite θ x)))
          / (2 * Real.pi) ^ 2 := by
          congr 1
          apply integral_congr_ae
          filter_upwards with θ
          exact sum_charFn_mul M x θ

/-- On the torus `1 - φ(θ) ≥ |θ|²/π²`. -/
theorem one_sub_charFn_two_ge {θ : Fin 2 → ℝ} (hθ : θ ∈ LocalCLT.torusBox 2) :
    (θ 0 ^ 2 + θ 1 ^ 2) / Real.pi ^ 2 ≤ 1 - charFn 2 θ := by
  simp only [LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at hθ
  have hb0 : |θ 0| ≤ Real.pi := abs_le.mpr ⟨hθ.1 0, hθ.2 0⟩
  have hb1 : |θ 1| ≤ Real.pi := abs_le.mpr ⟨hθ.1 1, hθ.2 1⟩
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hc0 : 2 * θ 0 ^ 2 ≤ (1 - Real.cos (θ 0)) * Real.pi ^ 2 := by
    have h1 : 2 / Real.pi ^ 2 * θ 0 ^ 2 ≤ 1 - Real.cos (θ 0) := by
      linarith [Real.cos_le_one_sub_mul_cos_sq hb0]
    have h2 : 2 * θ 0 ^ 2 = (2 / Real.pi ^ 2 * θ 0 ^ 2) * Real.pi ^ 2 := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 hpi2.le
  have hc1 : 2 * θ 1 ^ 2 ≤ (1 - Real.cos (θ 1)) * Real.pi ^ 2 := by
    have h1 : 2 / Real.pi ^ 2 * θ 1 ^ 2 ≤ 1 - Real.cos (θ 1) := by
      linarith [Real.cos_le_one_sub_mul_cos_sq hb1]
    have h2 : 2 * θ 1 ^ 2 = (2 / Real.pi ^ 2 * θ 1 ^ 2) * Real.pi ^ 2 := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 hpi2.le
  rw [charFn, Fin.sum_univ_two, div_le_iff₀ hpi2]
  nlinarith [hc0, hc1]

/-- `1 - cos(θ·x) ≤ |θ|² |x|²/2`. -/
theorem one_sub_cos_dotSite_le (θ : Fin 2 → ℝ) (x : Site 2) :
    1 - Real.cos (dotSite θ x) ≤ (θ 0 ^ 2 + θ 1 ^ 2) * euclidNorm x ^ 2 / 2 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := dotSite θ x)
  have hcs : dotSite θ x ^ 2
      ≤ (θ 0 ^ 2 + θ 1 ^ 2) * ((x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2) := by
    have h := sq_nonneg (θ 0 * (x 1 : ℝ) - θ 1 * (x 0 : ℝ))
    simp only [dotSite, Fin.sum_univ_two]
    nlinarith [h]
  have hnorm : euclidNorm x ^ 2 = (x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  rw [hnorm]
  nlinarith [hcos, hcs]

/-- The partial geometric sums are dominated on the torus:
`|(∑_{n<M} φⁿ)(1 - cos θ·x)| ≤ π² |x|²`. -/
theorem abs_geom_mul_le {θ : Fin 2 → ℝ} (hθ : θ ∈ LocalCLT.torusBox 2) (M : ℕ)
    (x : Site 2) :
    |(∑ n ∈ Finset.range M, charFn 2 θ ^ n) * (1 - Real.cos (dotSite θ x))|
      ≤ Real.pi ^ 2 * euclidNorm x ^ 2 := by
  by_cases hq : θ 0 ^ 2 + θ 1 ^ 2 = 0
  · have h0 : θ 0 = 0 := by nlinarith [sq_nonneg (θ 0), sq_nonneg (θ 1)]
    have h1 : θ 1 = 0 := by nlinarith [sq_nonneg (θ 0), sq_nonneg (θ 1)]
    have hdot : dotSite θ x = 0 := by
      simp only [dotSite, Fin.sum_univ_two, h0, h1, zero_mul, add_zero]
    rw [hdot, Real.cos_zero, sub_self, mul_zero, abs_zero]
    positivity
  · have hqpos : 0 < θ 0 ^ 2 + θ 1 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hq)
    have hpi2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
    have h1c := one_sub_charFn_two_ge hθ
    have hge : 0 < 1 - charFn 2 θ := by
      have : 0 < (θ 0 ^ 2 + θ 1 ^ 2) / Real.pi ^ 2 := div_pos hqpos hpi2pos
      linarith
    have hne : charFn 2 θ ≠ 1 := by linarith
    have hgeom := geom_sum_eq hne M
    have hcabs : |charFn 2 θ| ≤ 1 := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · rw [charFn]
        simp only [Fin.sum_univ_two]
        linarith [Real.neg_one_le_cos (θ 0), Real.neg_one_le_cos (θ 1)]
      · rw [charFn]
        simp only [Fin.sum_univ_two]
        linarith [Real.cos_le_one (θ 0), Real.cos_le_one (θ 1)]
    have hnum : |charFn 2 θ ^ M - 1| ≤ 2 := by
      have hsum : |charFn 2 θ ^ M - 1| ≤ |charFn 2 θ ^ M| + 1 := by
        simpa only [sub_eq_add_neg, abs_neg, abs_one] using
          abs_add_le (charFn 2 θ ^ M) (-1 : ℝ)
      have hpow : |charFn 2 θ ^ M| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hcabs
      linarith
    have hden : |charFn 2 θ - 1| = 1 - charFn 2 θ := by
      rw [abs_of_neg (by linarith : charFn 2 θ - 1 < 0)]
      ring
    have hS : |∑ n ∈ Finset.range M, charFn 2 θ ^ n| ≤ 2 / (1 - charFn 2 θ) := by
      rw [hgeom, abs_div, hden]
      rw [div_le_iff₀ hge]
      rw [div_mul_cancel₀ 2 hge.ne']
      exact hnum
    have hqle : θ 0 ^ 2 + θ 1 ^ 2 ≤ (1 - charFn 2 θ) * Real.pi ^ 2 := by
      calc θ 0 ^ 2 + θ 1 ^ 2
            = ((θ 0 ^ 2 + θ 1 ^ 2) / Real.pi ^ 2) * Real.pi ^ 2 := by field_simp
        _ ≤ (1 - charFn 2 θ) * Real.pi ^ 2 :=
              mul_le_mul_of_nonneg_right h1c hpi2pos.le
    have hinv : 1 / (1 - charFn 2 θ) ≤ Real.pi ^ 2 / (θ 0 ^ 2 + θ 1 ^ 2) := by
      rw [div_le_div_iff₀ hge hqpos, one_mul]
      linarith
    have hSbound : |∑ n ∈ Finset.range M, charFn 2 θ ^ n|
        ≤ 2 * Real.pi ^ 2 / (θ 0 ^ 2 + θ 1 ^ 2) := by
      calc |∑ n ∈ Finset.range M, charFn 2 θ ^ n| ≤ 2 / (1 - charFn 2 θ) := hS
        _ = 2 * (1 / (1 - charFn 2 θ)) := by ring
        _ ≤ 2 * (Real.pi ^ 2 / (θ 0 ^ 2 + θ 1 ^ 2)) := by gcongr
        _ = 2 * Real.pi ^ 2 / (θ 0 ^ 2 + θ 1 ^ 2) := by ring
    have hcosu := one_sub_cos_dotSite_le θ x
    have hcosu_nonneg : 0 ≤ 1 - Real.cos (dotSite θ x) := by
      linarith [Real.cos_le_one (dotSite θ x)]
    rw [abs_mul, abs_of_nonneg hcosu_nonneg]
    calc |∑ n ∈ Finset.range M, charFn 2 θ ^ n| * (1 - Real.cos (dotSite θ x))
        ≤ (2 * Real.pi ^ 2 / (θ 0 ^ 2 + θ 1 ^ 2))
            * ((θ 0 ^ 2 + θ 1 ^ 2) * euclidNorm x ^ 2 / 2) :=
          mul_le_mul hSbound hcosu hcosu_nonneg (by positivity)
      _ = Real.pi ^ 2 * euclidNorm x ^ 2 := by
          field_simp [hqpos.ne']

/-- Almost every point of the planar torus has `|φ(θ)| < 1`. -/
theorem ae_abs_charFn_lt_one :
    ∀ᵐ θ ∂(volume.restrict (LocalCLT.torusBox 2)), |charFn 2 θ| < 1 := by
  rw [MeasureTheory.ae_restrict_iff' (LocalCLT.torusBox_measurable 2)]
  have hae_c (c : ℝ) : ∀ᵐ θ ∂(volume : Measure (Fin 2 → ℝ)), θ 0 ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using LocalCLT.volume_hyperplane_eq_zero 2 0 c
  have hall : ∀ᵐ θ ∂(volume : Measure (Fin 2 → ℝ)),
      θ 0 ≠ -Real.pi ∧ θ 0 ≠ 0 ∧ θ 0 ≠ Real.pi :=
    (hae_c (-Real.pi)).and ((hae_c 0).and (hae_c Real.pi))
  filter_upwards [hall] with θ hθ
  intro hbox
  have hle1 : -Real.pi ≤ θ 0 := (Set.mem_Icc.mp hbox).1 0
  have hle2 : θ 0 ≤ Real.pi := (Set.mem_Icc.mp hbox).2 0
  have hlt1 : -Real.pi < θ 0 := lt_of_le_of_ne hle1 (Ne.symm hθ.1)
  have hlt2 : θ 0 < Real.pi := lt_of_le_of_ne hle2 hθ.2.2
  have hsin : Real.sin (θ 0) ≠ 0 := by
    intro h0
    exact hθ.2.1 ((Real.sin_eq_zero_iff_of_lt_of_lt hlt1 hlt2).mp h0)
  have hcos_lt : |Real.cos (θ 0)| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]
    have hsin2 : 0 < Real.sin (θ 0) ^ 2 := sq_pos_of_ne_zero hsin
    have hcs := Real.sin_sq_add_cos_sq (θ 0)
    nlinarith
  have hcos1 : |Real.cos (θ 1)| ≤ 1 := Real.abs_cos_le_one (θ 1)
  rw [charFn, Fin.sum_univ_two, abs_div]
  norm_num
  have h := abs_add_le (Real.cos (θ 0)) (Real.cos (θ 1))
  linarith

/-- The planar partial sums converge to the Fourier form of the potential kernel, by
dominated convergence. -/
theorem tendsto_srwGreen_sub_fourierPotential (x : Site 2) :
    Tendsto (fun M : ℕ => srwGreen 2 M 0 - srwGreen 2 M x) atTop (𝓝 (fourierPotential x)) := by
  set μ := volume.restrict (LocalCLT.torusBox 2) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; exact isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top.ne)
  simp_rw [srwGreen_sub_eq_integral]
  unfold fourierPotential
  refine Tendsto.div_const ?_ _
  have hcont : ∀ M : ℕ, Continuous fun θ : Fin 2 → ℝ =>
      (∑ n ∈ Finset.range M, charFn 2 θ ^ n) * (1 - Real.cos (dotSite θ x)) := by
    intro M
    unfold charFn dotSite
    fun_prop
  refine tendsto_integral_of_dominated_convergence (fun _ => Real.pi ^ 2 * euclidNorm x ^ 2)
    (fun M => (hcont M).aestronglyMeasurable) (integrable_const _) (fun M => ?_) ?_
  · refine (ae_restrict_iff' (LocalCLT.torusBox_measurable 2)).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact abs_geom_mul_le hθ M x
  · filter_upwards [ae_abs_charFn_lt_one] with θ hθ
    have h := (hasSum_geometric_of_abs_lt_one hθ).tendsto_sum_nat
    have h2 := h.mul_const (1 - Real.cos (dotSite θ x))
    convert h2 using 2
    rw [div_eq_mul_inv, mul_comm]

/-- The Fourier form of the potential kernel is the time integral
`∫_0^∞ [q_t(0) - q_t(x)] dt`, by Tonelli and `∫_0^∞ e^{-t(1-φ)} dt = 1/(1 - φ)`. -/
theorem fourierPotential_eq_integral_ctHeat (x : Site 2) :
    fourierPotential x = ∫ t in Set.Ioi 0, (ctHeat 2 t 0 - ctHeat 2 t x) := by
  set μ := volume.restrict (LocalCLT.torusBox 2) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; exact isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top.ne)
  set ν := volume.restrict (Set.Ioi (0 : ℝ)) with hν
  set f : (Fin 2 → ℝ) → ℝ → ℝ := fun θ t =>
    Real.exp (-t * (1 - charFn 2 θ)) * (1 - Real.cos (dotSite θ x)) with hf
  have hfcont : Continuous (Function.uncurry f) := by
    rw [hf]; unfold charFn dotSite; fun_prop
  have hnn : ∀ θ t, 0 ≤ f θ t := fun θ t =>
    mul_nonneg (Real.exp_pos _).le (by linarith [Real.cos_le_one (dotSite θ x)])
  have hae : ∀ᵐ θ ∂μ, 0 < 1 - charFn 2 θ :=
    ae_abs_charFn_lt_one.mono fun θ h => by linarith [(abs_lt.mp h).2]
  have hexp : ∀ θ, 0 < 1 - charFn 2 θ →
      IntegrableOn (fun t => Real.exp (-t * (1 - charFn 2 θ))) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, Real.exp (-t * (1 - charFn 2 θ)) = (1 - charFn 2 θ)⁻¹ := by
    intro θ hθ
    have hfun : (fun t : ℝ => Real.exp (-t * (1 - charFn 2 θ)))
        = fun t => Real.exp (-(1 - charFn 2 θ) * t) := by
      funext t; ring_nf
    rw [hfun]
    refine ⟨exp_neg_integrableOn_Ioi 0 hθ, ?_⟩
    rw [integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hinner : ∀ θ, 0 < 1 - charFn 2 θ →
      ∫ t, f θ t ∂ν = (1 - Real.cos (dotSite θ x)) / (1 - charFn 2 θ) := by
    intro θ hθ
    rw [hν, hf]
    simp only
    rw [integral_mul_const, (hexp θ hθ).2, div_eq_mul_inv, mul_comm]
  have hbound : ∀ θ ∈ LocalCLT.torusBox 2,
      (1 - Real.cos (dotSite θ x)) / (1 - charFn 2 θ) ≤ Real.pi ^ 2 * euclidNorm x ^ 2 / 2 := by
    intro θ hθ
    have h1 := one_sub_charFn_two_ge hθ
    have h2 := one_sub_cos_dotSite_le θ x
    have h3 : 0 ≤ 1 - Real.cos (dotSite θ x) := by linarith [Real.cos_le_one (dotSite θ x)]
    rcases (add_nonneg (sq_nonneg (θ 0)) (sq_nonneg (θ 1))).eq_or_lt with hq | hq
    · have : 1 - Real.cos (dotSite θ x) = 0 :=
        le_antisymm (by rw [← hq] at h2; simpa using h2) h3
      rw [this, zero_div]
      positivity
    · have hpos : 0 < 1 - charFn 2 θ := lt_of_lt_of_le (by positivity) h1
      rw [div_le_iff₀ hpos]
      calc 1 - Real.cos (dotSite θ x) ≤ (θ 0 ^ 2 + θ 1 ^ 2) * euclidNorm x ^ 2 / 2 := h2
        _ = Real.pi ^ 2 * euclidNorm x ^ 2 / 2 * ((θ 0 ^ 2 + θ 1 ^ 2) / Real.pi ^ 2) := by
            field_simp
        _ ≤ Real.pi ^ 2 * euclidNorm x ^ 2 / 2 * (1 - charFn 2 θ) := by gcongr
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    rw [integrable_prod_iff hfcont.aestronglyMeasurable]
    constructor
    · filter_upwards [hae] with θ hθ
      exact ((hexp θ hθ).1.mul_const (1 - Real.cos (dotSite θ x)))
    · refine Integrable.mono' (integrable_const (Real.pi ^ 2 * euclidNorm x ^ 2 / 2))
        hfcont.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hae, (ae_restrict_iff' (LocalCLT.torusBox_measurable 2)).mpr
        (Filter.Eventually.of_forall hbound)] with θ hθ hb
      have hnorm : ∫ t, ‖Function.uncurry f (θ, t)‖ ∂ν = ∫ t, f θ t ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => by
          simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (hnn θ t)])
      rw [hnorm, hinner θ hθ, Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (by linarith [Real.cos_le_one (dotSite θ x)]) hθ.le)]
      exact hb
  have hswap := integral_integral_swap hint
  -- the left side is the Fourier form
  have hleft : ∫ θ, ∫ t, f θ t ∂ν ∂μ = (2 * Real.pi) ^ 2 * fourierPotential x := by
    rw [fourierPotential, mul_div_cancel₀ _ (by positivity)]
    exact integral_congr_ae (hae.mono fun θ hθ => hinner θ hθ)
  -- the right side is the kernel difference
  have hright : ∀ t,
      ∫ θ, f θ t ∂μ = (2 * Real.pi) ^ 2 * (ctHeat 2 t 0 - ctHeat 2 t x) := by
    intro t
    have hc : ∀ y : Site 2, Continuous fun θ : Fin 2 → ℝ =>
        Real.exp (-t * (1 - charFn 2 θ)) * Real.cos (dotSite θ y) := by
      intro y; unfold charFn dotSite; fun_prop
    have hi : ∀ y : Site 2, Integrable (fun θ : Fin 2 → ℝ =>
        Real.exp (-t * (1 - charFn 2 θ)) * Real.cos (dotSite θ y)) μ :=
      fun y => (hc y).integrableOn_Icc
    rw [ctHeat_eq_integral_cos (by norm_num) t 0, ctHeat_eq_integral_cos (by norm_num) t x,
      ← sub_div, mul_div_cancel₀ _ (by positivity), ← integral_sub (hi 0) (hi x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have h0 : dotSite θ (0 : Site 2) = 0 := by simp [dotSite]
    simp only [hf, h0, Real.cos_zero]
    ring
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  rw [← mul_right_inj' hpi, ← hleft, hswap, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => hright t)

end LatticeProb.ContinuousTime
