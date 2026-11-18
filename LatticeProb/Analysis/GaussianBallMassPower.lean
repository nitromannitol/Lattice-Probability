import Mathlib

/-!
# Gaussian kernels against measures with power-law ball masses

Let `μ` be a measure on a pseudometric space with `μ (ball z r) ≤ A r^β` for every `r > 0`, where
`0 < β ≤ 1`. Then the Gaussian weight `exp (-d(x, z)² / (2 s))` integrates against `μ` to at most
`(1024 / 7) A s^{β/2}` (`lintegral_exp_neg_dist_sq_le_of_measure_ball_le`).

The proof splits space into the dyadic shells `2^{j-1} √s ≤ d(x, z) < 2^j √s`: on the `j`-th shell
the weight is at most `128 / 16^j` (from `exp y ≥ y² / 2`), the shell has mass at most
`A 2^j s^{β/2}`, and the resulting series is geometric with ratio `1/8`.

Auxiliary facts for applying it: small-radius bounds plus a total-mass bound give bounds at all
radii (`measure_ball_le_rpow_of_le_one`), a closed ball in a proper space has mass controlled by
finitely many unit balls (`exists_measure_closedBall_le_of_measure_ball_le`), and
`∫_{(0,t]} s^{a-1} ds = t^a / a` (`lintegral_Ioc_rpow_sub_one`).

On `ℂ`, the planar Gaussian law with mean `z` and covariance `s · I₂` (the image of the product of
two real Gaussians) has density `(2π s)⁻¹ exp (-‖y - z‖² / (2 s))`
(`lintegral_map_prod_gaussianReal_eq`); hence a density whose integrals over the balls `B(z, r)` are
at most `A r^β` has Gaussian average at most `(1024 / 7) (2π)⁻¹ A s^{β/2 - 1}`
(`lintegral_map_prod_gaussianReal_le_of_setLIntegral_ball_le`).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

/-- On the shell `d ≥ 2^i √s` the Gaussian weight `exp (-d² / (2 s))` is at most `128 / 16^{i+1}`. -/
theorem exp_neg_sq_div_le_of_two_pow_mul_sqrt_le {d s : ℝ} (hs : 0 < s) (i : ℕ)
    (hd : (2 : ℝ) ^ i * Real.sqrt s ≤ d) :
    Real.exp (-(d ^ 2) / (2 * s)) ≤ 128 / 16 ^ (i + 1) := by
  have h0 : 0 ≤ (2 : ℝ) ^ i * Real.sqrt s := by positivity
  have hsq : (4 : ℝ) ^ i * s ≤ d ^ 2 := by
    have h := pow_le_pow_left₀ h0 hd 2
    have h4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, Real.sq_sqrt hs.le, h4] at h
    exact h
  set y : ℝ := (4 : ℝ) ^ i / 2 with hy
  have hypos : 0 < y := by positivity
  have hyd : y ≤ d ^ 2 / (2 * s) := by
    rw [le_div_iff₀ (by positivity)]
    have : y * (2 * s) = 4 ^ i * s := by rw [hy]; ring
    linarith
  have hq := Real.quadratic_le_exp_of_nonneg hypos.le
  have hy2 : 0 < y ^ 2 / 2 := by positivity
  calc Real.exp (-(d ^ 2) / (2 * s)) ≤ Real.exp (-y) := by
        apply Real.exp_le_exp.2; rw [neg_div]; linarith
    _ = (Real.exp y)⁻¹ := Real.exp_neg y
    _ ≤ (y ^ 2 / 2)⁻¹ := inv_anti₀ hy2 (by linarith)
    _ = 128 / 16 ^ (i + 1) := by
        have h16 : (16 : ℝ) ^ i = ((4 : ℝ) ^ i) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [hy, pow_succ (16 : ℝ) i, h16]
        field_simp
        ring

/-- Pointwise domination of the Gaussian weight by a series of indicators of dyadic balls. -/
theorem ofReal_exp_neg_dist_sq_le_tsum_indicator {α : Type*} [PseudoMetricSpace α] (z x : α)
    {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) ≤
      ∑' j : ℕ, (ball z ((2 : ℝ) ^ j * Real.sqrt s)).indicator
        (fun _ => ENNReal.ofReal (128 / 16 ^ j)) x := by
  classical
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hex : ∃ j : ℕ, dist x z < (2 : ℝ) ^ j * Real.sqrt s := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (dist x z / Real.sqrt s) (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, by rwa [div_lt_iff₀ hss] at hj⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j : ℕ, dist x z < (2 : ℝ) ^ j * Real.sqrt s ∧
      ∀ m < j, ¬ dist x z < (2 : ℝ) ^ m * Real.sqrt s :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine le_trans ?_ (ENNReal.le_tsum j)
  rw [indicator_of_mem (mem_ball.2 hj)]
  refine ENNReal.ofReal_le_ofReal ?_
  cases j with
  | zero =>
    have hle : -(dist x z ^ 2) / (2 * s) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)
    have := Real.exp_le_one_iff.2 hle
    norm_num
    linarith
  | succ i =>
    exact exp_neg_sq_div_le_of_two_pow_mul_sqrt_le hs i
      (not_lt.1 (hmin i (Nat.lt_succ_self i)))

/-- **Gaussian weights against a measure with power-law ball masses.** If
`μ (ball z r) ≤ A r^β` for every `r > 0`, with `0 < β ≤ 1` and `A ≥ 0`, then
`∫ exp (-d(x, z)² / (2 s)) dμ(x) ≤ (1024 / 7) A s^{β/2}` for every `s > 0`. -/
theorem lintegral_exp_neg_dist_sq_le_of_measure_ball_le {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} {z : α} {A β s : ℝ}
    (hβ1 : β ≤ 1) (hA : 0 ≤ A) (hs : 0 < s)
    (hball : ∀ r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (A * r ^ β)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) ∂μ ≤
      ENNReal.ofReal (1024 / 7 * A * s ^ (β / 2)) := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hS : 0 ≤ s ^ (β / 2) := Real.rpow_nonneg hs.le _
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) ∂μ
      ≤ ∫⁻ x, ∑' j : ℕ, (ball z ((2 : ℝ) ^ j * Real.sqrt s)).indicator
          (fun _ => ENNReal.ofReal (128 / 16 ^ j)) x ∂μ :=
        lintegral_mono fun x => ofReal_exp_neg_dist_sq_le_tsum_indicator z x hs
    _ = ∑' j : ℕ, ENNReal.ofReal (128 / 16 ^ j) * μ (ball z ((2 : ℝ) ^ j * Real.sqrt s)) := by
        rw [lintegral_tsum fun j => (measurable_const.indicator measurableSet_ball).aemeasurable]
        congr 1
        ext j
        rw [lintegral_indicator_const measurableSet_ball]
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (128 * A * s ^ (β / 2) * (1 / 8) ^ j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        have hr : 0 < (2 : ℝ) ^ j * Real.sqrt s := by positivity
        calc ENNReal.ofReal (128 / 16 ^ j) * μ (ball z ((2 : ℝ) ^ j * Real.sqrt s))
            ≤ ENNReal.ofReal (128 / 16 ^ j) *
                ENNReal.ofReal (A * ((2 : ℝ) ^ j * Real.sqrt s) ^ β) :=
              mul_le_mul' le_rfl (hball _ hr)
          _ = ENNReal.ofReal (128 / 16 ^ j * (A * ((2 : ℝ) ^ j * Real.sqrt s) ^ β)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (128 * A * s ^ (β / 2) * (1 / 8) ^ j) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hsb : (1 / 2 : ℝ) * β = β / 2 := by ring
              rw [Real.mul_rpow (by positivity) hss.le, Real.sqrt_eq_rpow,
                ← Real.rpow_mul hs.le, hsb]
              have h2 : ((2 : ℝ) ^ j) ^ β ≤ (2 : ℝ) ^ j := by
                calc ((2 : ℝ) ^ j) ^ β ≤ ((2 : ℝ) ^ j) ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hβ1
                  _ = (2 : ℝ) ^ j := Real.rpow_one _
              have h16 : (2 : ℝ) ^ j / 16 ^ j = (1 / 8) ^ j := by
                rw [← div_pow]; norm_num
              calc 128 / 16 ^ j * (A * (((2 : ℝ) ^ j) ^ β * s ^ (β / 2)))
                  ≤ 128 / 16 ^ j * (A * ((2 : ℝ) ^ j * s ^ (β / 2))) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hS) hA)
                      (by positivity)
                _ = 128 * A * s ^ (β / 2) * (1 / 8) ^ j := by rw [← h16]; ring
    _ = ENNReal.ofReal (1024 / 7 * A * s ^ (β / 2)) := by
        have hsum : Summable fun j : ℕ => 128 * A * s ^ (β / 2) * (1 / 8 : ℝ) ^ j :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hS) (by positivity)) hsum,
          tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        congr 1
        ring

/-- **From small balls to all balls.** If `μ (ball z r) ≤ A r^β` for `0 < r ≤ 1` and `μ` has total
mass at most `M`, then `μ (ball z r) ≤ max A M · r^{min β 1}` for every `r > 0`. -/
theorem measure_ball_le_rpow_of_le_one {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    {μ : Measure α} {z : α} {A M β : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (huniv : μ univ ≤ ENNReal.ofReal M)
    (hsmall : ∀ r, 0 < r → r ≤ 1 → μ (ball z r) ≤ ENNReal.ofReal (A * r ^ β)) :
    ∀ r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (max A M * r ^ min β 1) := by
  intro r hr
  have hmax : 0 ≤ max A M := le_max_of_le_left hA
  rcases le_or_gt r 1 with h1 | h1
  · refine (hsmall r hr h1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_left A M)
      (Real.rpow_le_rpow_of_exponent_ge hr h1 (min_le_left β 1))
      (Real.rpow_nonneg hr.le _) hmax
  · refine (measure_mono (subset_univ _)).trans (huniv.trans (ENNReal.ofReal_le_ofReal ?_))
    calc M ≤ max A M := le_max_right A M
      _ ≤ max A M * r ^ min β 1 :=
        le_mul_of_one_le_right hmax (Real.one_le_rpow h1.le (le_min hβ zero_le_one))

/-- **Mass of a closed ball from unit balls.** In a proper space, a closed ball is covered by
finitely many unit balls centred in it; hence there is `N` such that every measure giving mass at
most `C` to the unit balls centred in `closedBall x₀ R` gives mass at most `N C` to the closed ball. -/
theorem exists_measure_closedBall_le_of_measure_ball_le {α : Type*} [PseudoMetricSpace α]
    [ProperSpace α] [MeasurableSpace α] (x₀ : α) (R : ℝ) :
    ∃ N : ℕ, ∀ (μ : Measure α) (C : ℝ), 0 ≤ C →
      (∀ c ∈ closedBall x₀ R, μ (ball c 1) ≤ ENNReal.ofReal C) →
        μ (closedBall x₀ R) ≤ ENNReal.ofReal (N * C) := by
  obtain ⟨t, hts, hcov⟩ := (isCompact_closedBall x₀ R).elim_nhds_subcover (fun x => ball x 1)
    (fun x _ => ball_mem_nhds x one_pos)
  refine ⟨t.card, fun μ C hC hball => ?_⟩
  calc μ (closedBall x₀ R) ≤ μ (⋃ x ∈ t, ball x 1) := measure_mono hcov
    _ ≤ ∑ x ∈ t, μ (ball x 1) := measure_biUnion_finset_le t _
    _ ≤ ∑ _x ∈ t, ENNReal.ofReal C := Finset.sum_le_sum fun x hx => hball x (hts x hx)
    _ = ENNReal.ofReal (t.card * C) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

/-- `∫_{(0, t]} s^{a-1} ds = t^a / a` for `a > 0`, as a lower Lebesgue integral. -/
theorem lintegral_Ioc_rpow_sub_one {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ (a - 1)) = ENNReal.ofReal (t ^ a / a) := by
  have hr : -1 < a - 1 := by linarith
  have hint : IntegrableOn (fun s : ℝ => s ^ (a - 1)) (Ioc 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
      (intervalIntegral.intervalIntegrable_rpow' hr)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => Real.rpow_nonneg hs.1.le _),
    ← intervalIntegral.integral_of_le ht, integral_rpow (Or.inl hr), sub_add_cancel,
    Real.zero_rpow ha.ne', sub_zero]

section PlanarGaussian

open ProbabilityTheory
open scoped NNReal

/-- The planar Gaussian law with mean `z` and covariance `s · I₂`, realized as the image on `ℂ` of
the product of the real Gaussians `𝒩(Re z, s)` and `𝒩(Im z, s)`, has density
`(2π s)⁻¹ exp (-‖y - z‖² / (2 s))` with respect to Lebesgue measure. -/
theorem lintegral_map_prod_gaussianReal_eq (z : ℂ) {s : ℝ≥0} (hs : s ≠ 0) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y, g y ∂(((gaussianReal z.re s).prod (gaussianReal z.im s)).map
        Complex.measurableEquivRealProd.symm) =
      ∫⁻ y, ENNReal.ofReal ((2 * Real.pi * s)⁻¹ * Real.exp (-(‖y - z‖ ^ 2) / (2 * s))) * g y := by
  have hpres : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm _
  rw [lintegral_map_equiv, gaussianReal_of_var_ne_zero _ hs, gaussianReal_of_var_ne_zero _ hs,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun p : ℝ × ℝ => gaussianPDF z.re s p.1 * gaussianPDF z.im s p.2)
      (((measurable_gaussianPDF _ _).comp measurable_fst).mul
        ((measurable_gaussianPDF _ _).comp measurable_snd))
      (g := fun p => g (Complex.measurableEquivRealProd.symm p))
      (hg.comp Complex.measurableEquivRealProd.symm.measurable),
    ← hpres.lintegral_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding,
    Measure.volume_eq_prod]
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 2
  have h2 : 0 ≤ 2 * Real.pi * (s : ℝ) := by positivity
  have hnorm : ‖Complex.measurableEquivRealProd.symm p - z‖ ^ 2 =
      (p.1 - z.re) ^ 2 + (p.2 - z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.measurableEquivRealProd_symm_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hsq : (Real.sqrt (2 * Real.pi * s))⁻¹ * (Real.sqrt (2 * Real.pi * s))⁻¹ =
      (2 * Real.pi * s)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt h2]
  have hexp : Real.exp (-((p.1 - z.re) ^ 2 + (p.2 - z.im) ^ 2) / (2 * s)) =
      Real.exp (-(p.1 - z.re) ^ 2 / (2 * s)) * Real.exp (-(p.2 - z.im) ^ 2 / (2 * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [gaussianPDFReal, gaussianPDFReal, hnorm, hexp, ← hsq]
  ring

/-- Gaussian smoothing of a density with power-law ball masses: if `∫_{B(z, r)} g ≤ A r^β` for every
`r > 0`, where `β ≤ 1`, then the planar Gaussian law with mean `z` and covariance `s · I₂`
integrates `g` to at most `(1024 / 7) (2π)⁻¹ A s^{β/2 - 1}`. -/
theorem lintegral_map_prod_gaussianReal_le_of_setLIntegral_ball_le (z : ℂ) {s : ℝ≥0}
    (hs : s ≠ 0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) {A β : ℝ} (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (hball : ∀ r, 0 < r → ∫⁻ y in ball z r, g y ≤ ENNReal.ofReal (A * r ^ β)) :
    ∫⁻ y, g y ∂(((gaussianReal z.re s).prod (gaussianReal z.im s)).map
        Complex.measurableEquivRealProd.symm) ≤
      ENNReal.ofReal (1024 / 7 / (2 * Real.pi) * A * (s : ℝ) ^ (β / 2 - 1)) := by
  have hs' : (0 : ℝ) < s := lt_of_le_of_ne s.2 (by exact_mod_cast hs.symm)
  have hmeas : Measurable fun x : ℂ => ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) := by
    fun_prop
  have hL1 := lintegral_exp_neg_dist_sq_le_of_measure_ball_le (μ := volume.withDensity g) (z := z)
    hβ1 hA hs' fun r hr => by rw [withDensity_apply _ measurableSet_ball]; exact hball r hr
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hmeas] at hL1
  rw [lintegral_map_prod_gaussianReal_eq z hs hg]
  calc ∫⁻ y, ENNReal.ofReal ((2 * Real.pi * s)⁻¹ * Real.exp (-(‖y - z‖ ^ 2) / (2 * s))) * g y
      = ∫⁻ y, ENNReal.ofReal ((2 * Real.pi * s)⁻¹) *
          (g * fun x => ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s)))) y := by
        refine lintegral_congr fun y => ?_
        simp only [Pi.mul_apply, dist_eq_norm]
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
    _ = ENNReal.ofReal ((2 * Real.pi * s)⁻¹) *
          ∫⁻ y, (g * fun x => ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s)))) y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 * Real.pi * s)⁻¹) *
          ENNReal.ofReal (1024 / 7 * A * (s : ℝ) ^ (β / 2)) := by gcongr
    _ = ENNReal.ofReal (1024 / 7 / (2 * Real.pi) * A * (s : ℝ) ^ (β / 2 - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_sub_one hs'.ne']
        congr 1
        field_simp

end PlanarGaussian

end LatticeProb
