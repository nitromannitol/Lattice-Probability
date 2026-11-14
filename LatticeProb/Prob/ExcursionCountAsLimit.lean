import LatticeProb.Prob.ExcursionCountVariance
import LatticeProb.Prob.ExcursionCountMeanScale

/-!
# The Brownian excursion count as an almost sure limit

For a real Brownian motion `B` with continuous paths, `J_ε(b)` denotes the number of excursions of `B` above its
running minimum from time `0`, of length larger than `ε`, completed before the first passage below `B 0 - b`
(`pathExcursionCount`). Its mean is `b κ / √ε` with `κ = E J_1(1) < ∞` and its variance is at most its mean. Hence,
almost surely, `√ε J_ε(b) → b κ` as `ε → 0+`.

* `tendsto_sqrt_mul_of_antitone`: a deterministic interpolation lemma. If `F ≥ 0` is antitone on `(0, ∞)` and
  `√(u k) F (u k) → L` along a decreasing sequence `u k → 0` of positive reals with `u k / u (k + 1) → 1`, then
  `√ε F ε → L` as `ε → 0+`;
* `tendsto_sqrt_mul_of_antitone_quartic`: the case `u k = (k + 1)⁻⁴`;
* `memLp_two_pathExcursionCount`, `integral_pathExcursionCount`, `variance_pathExcursionCount_le`: the excursion
  count is square integrable and its variance is at most its mean;
* `measure_le_abs_sqrt_mul_pathExcursionCount_sub_le`: Chebyshev's inequality for `√ε J_ε(b)`;
* `ae_tendsto_sqrt_mul_pathExcursionCount_quartic`: almost sure convergence along `ε = (k + 1)⁻⁴` (Borel-Cantelli);
* `ae_tendsto_sqrt_mul_pathExcursionCount`: the almost sure limit as `ε → 0+`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- **Interpolation along a sequence.** Let `F ≥ 0` be antitone on `(0, ∞)` and let `u` be a decreasing sequence of
positive reals with `u k → 0` and `u k / u (k + 1) → 1`. If `√(u k) F (u k) → L`, then `√ε F ε → L` as `ε → 0+`. -/
theorem tendsto_sqrt_mul_of_antitone {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ F x)
    (hF : ∀ x y, 0 < x → x ≤ y → F y ≤ F x) {u : ℕ → ℝ} (hu0 : ∀ k, 0 < u k) (hu : Antitone u)
    (hlim : Tendsto u atTop (𝓝 0)) (hratio : Tendsto (fun k => u k / u (k + 1)) atTop (𝓝 1)) {L : ℝ}
    (ha : Tendsto (fun k => √(u k) * F (u k)) atTop (𝓝 L)) :
    Tendsto (fun ε => √ε * F ε) (𝓝[>] 0) (𝓝 L) := by
  classical
  have hne : ∀ ε : ℝ, 0 < ε → {n | u (n + 1) < ε}.Nonempty := by
    intro ε hε
    obtain ⟨n, hn⟩ := ((hlim.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds hε)).exists
    exact ⟨n, hn⟩
  -- the index `k ε`, with `u (k ε + 1) < ε ≤ u (k ε)` for `0 < ε ≤ u 0`
  let k : ℝ → ℕ := fun ε => sInf {n | u (n + 1) < ε}
  have hk1 : ∀ ε : ℝ, 0 < ε → u (k ε + 1) < ε := fun ε hε => Nat.sInf_mem (hne ε hε)
  have hk2 : ∀ ε : ℝ, ε ≤ u 0 → ε ≤ u (k ε) := by
    intro ε hε0
    rcases Nat.eq_zero_or_pos (k ε) with h | h
    · rw [h]
      exact hε0
    · have h' : ¬ u (k ε - 1 + 1) < ε := Nat.notMem_of_lt_sInf (Nat.sub_lt h one_pos)
      rw [Nat.sub_add_cancel h] at h'
      exact not_lt.1 h'
  have hk : Tendsto k (𝓝[>] 0) atTop := by
    refine tendsto_atTop.2 fun J => ?_
    filter_upwards [Ioo_mem_nhdsGT (hu0 J)] with ε hε
    by_contra hlt
    have h1 := hk1 ε hε.1
    have h2 : u J ≤ u (k ε + 1) := hu (by omega)
    linarith [hε.2]
  have hr' : Tendsto (fun m => u (m + 1) / u m) atTop (𝓝 1) := by
    have h := hratio.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun m => inv_div _ _
  have hU : Tendsto (fun m => √(u m / u (m + 1)) * (√(u (m + 1)) * F (u (m + 1)))) atTop (𝓝 L) := by
    have h := hratio.sqrt.mul (ha.comp (tendsto_add_atTop_nat 1))
    rw [Real.sqrt_one, one_mul] at h
    exact h
  have hL : Tendsto (fun m => √(u (m + 1) / u m) * (√(u m) * F (u m))) atTop (𝓝 L) := by
    have h := hr'.sqrt.mul ha
    rw [Real.sqrt_one, one_mul] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.comp hk) (hU.comp hk) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (hu0 0)] with ε hε
    have h1 := hk1 ε hε.1
    have h2 := hk2 ε hε.2.le
    show √(u (k ε + 1) / u (k ε)) * (√(u (k ε)) * F (u (k ε))) ≤ √ε * F ε
    rw [Real.sqrt_div (hu0 _).le, ← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_pos.2 (hu0 _)).ne']
    exact mul_le_mul (Real.sqrt_le_sqrt h1.le) (hF ε _ hε.1 h2) (hF0 _) (Real.sqrt_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (hu0 0)] with ε hε
    have h1 := hk1 ε hε.1
    have h2 := hk2 ε hε.2.le
    show √ε * F ε ≤ √(u (k ε) / u (k ε + 1)) * (√(u (k ε + 1)) * F (u (k ε + 1)))
    rw [Real.sqrt_div (hu0 _).le, ← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_pos.2 (hu0 _)).ne']
    exact mul_le_mul (Real.sqrt_le_sqrt h2) (hF _ ε (hu0 _) h1.le) (hF0 _) (Real.sqrt_nonneg _)

/-- **Interpolation along `(k + 1)⁻⁴`.** If `F ≥ 0` is antitone on `(0, ∞)` and `√ε F ε → L` along
`ε = (k + 1)⁻⁴`, then `√ε F ε → L` as `ε → 0+`. -/
theorem tendsto_sqrt_mul_of_antitone_quartic {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ F x)
    (hF : ∀ x y, 0 < x → x ≤ y → F y ≤ F x) {L : ℝ}
    (ha : Tendsto (fun k : ℕ => √((((k : ℝ) + 1) ^ 4)⁻¹) * F ((((k : ℝ) + 1) ^ 4)⁻¹)) atTop (𝓝 L)) :
    Tendsto (fun ε => √ε * F ε) (𝓝[>] 0) (𝓝 L) := by
  refine tendsto_sqrt_mul_of_antitone hF0 hF (u := fun k : ℕ => (((k : ℝ) + 1) ^ 4)⁻¹)
    (fun k => by positivity) ?_ ?_ ?_ ha
  · intro a b hab
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hab
      linarith
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hab' 4)
  · exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1 |>.pow 4
    rw [add_zero, one_pow] at h
    refine h.congr fun k => ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    push_cast
    field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem ofReal_natCast_sq (x : ℕ) : ENNReal.ofReal ((x : ℝ) ^ 2) = (x : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The excursion count, as a real random variable, is square integrable. -/
theorem memLp_two_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 ≤ b) {ε : ℝ}
    (hε : 0 < ε) :
    MemLp (fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ)) 2 P := by
  have hmeas : Measurable fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_pathExcursionCount hm hcont b hε)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)]
  simp_rw [ofReal_natCast_sq]
  have hfin := lintegral_pathExcursionCount_lt_top hB hm hcont hb hε
  exact (lintegral_pathExcursionCount_sq_le hB hm hcont hb hε).trans_lt
    (ENNReal.add_lt_top.2 ⟨hfin, (ENNReal.pow_ne_top hfin.ne).lt_top⟩)

/-- The mean of the excursion count, as a real number. -/
theorem integral_pathExcursionCount (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ) ∂P =
      (∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P).toReal := by
  have hmeas : Measurable fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_pathExcursionCount hm hcont b hε)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _) hmeas.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]

/-- **The variance of the excursion count is at most its mean.** -/
theorem variance_pathExcursionCount_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 ≤ b) {ε : ℝ}
    (hε : 0 < ε) :
    variance (fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ)) P ≤
      ∫ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ) ∂P := by
  have hmeas : Measurable fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_pathExcursionCount hm hcont b hε)
  have hX := memLp_two_pathExcursionCount hB hm hcont hb hε
  rw [variance_eq_sub hX, integral_pathExcursionCount hm hcont b hε]
  have hsq : ∫ ω, ((fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ)) ^ 2) ω ∂P =
      (∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P).toReal := by
    simp only [Pi.pow_apply]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
      (hmeas.pow_const 2).aestronglyMeasurable]
    simp_rw [ofReal_natCast_sq]
  rw [hsq]
  have hfin := lintegral_pathExcursionCount_lt_top hB hm hcont hb hε
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin.ne, ENNReal.pow_ne_top hfin.ne⟩)
    (lintegral_pathExcursionCount_sq_le hB hm hcont hb hε)
  rw [ENNReal.toReal_add hfin.ne (ENNReal.pow_ne_top hfin.ne), ENNReal.toReal_pow] at h
  linarith

/-- **Chebyshev's inequality for the rescaled excursion count.** For `b, ε, δ > 0`, with `κ = E J_1(1)`,
`P(δ ≤ |√ε J_ε(b) - b κ|) ≤ √ε b κ / δ²`. -/
theorem measure_le_abs_sqrt_mul_pathExcursionCount_sub_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | δ ≤ |√ε * (pathExcursionCount (fun t => B t ω) b ε : ℝ) -
        b * (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal|} ≤
      ENNReal.ofReal (√ε * b * (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal / δ ^ 2) := by
  set κ := (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal with hκ
  have hX := memLp_two_pathExcursionCount hB hm hcont hb.le hε
  have hY : MemLp (fun ω => √ε * (pathExcursionCount (fun t => B t ω) b ε : ℝ)) 2 P := hX.const_mul _
  have hsq : 0 < √ε := Real.sqrt_pos.2 hε
  have hmean0 : ∫ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ) ∂P = b / √ε * κ := by
    rw [integral_pathExcursionCount hm hcont b hε, lintegral_pathExcursionCount_eq_div_sqrt hB hm hcont hε hb,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hb.le hsq.le)]
  have hmean : ∫ ω, √ε * (pathExcursionCount (fun t => B t ω) b ε : ℝ) ∂P = b * κ := by
    rw [integral_const_mul, hmean0]
    field_simp
  have hvar : variance (fun ω => √ε * (pathExcursionCount (fun t => B t ω) b ε : ℝ)) P ≤ √ε * b * κ := by
    rw [variance_const_mul, Real.sq_sqrt hε.le]
    calc ε * variance (fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ)) P
        ≤ ε * (b / √ε * κ) := by
          rw [← hmean0]
          exact mul_le_mul_of_nonneg_left (variance_pathExcursionCount_le hB hm hcont hb.le hε) hε.le
      _ = (√ε * √ε) * (b / √ε * κ) := by rw [Real.mul_self_sqrt hε.le]
      _ = √ε * b * κ := by field_simp
  have h := meas_ge_le_variance_div_sq hY hδ
  rw [hmean] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg _)))

/-- **Almost sure convergence along `ε = (k + 1)⁻⁴`.** For `b > 0`, almost surely
`√ε J_ε(b) → b κ` along `ε = (k + 1)⁻⁴`, `κ = E J_1(1)`. -/
theorem ae_tendsto_sqrt_mul_pathExcursionCount_quartic [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => √((((k : ℝ) + 1) ^ 4)⁻¹) *
        (pathExcursionCount (fun t => B t ω) b ((((k : ℝ) + 1) ^ 4)⁻¹) : ℝ)) atTop
      (𝓝 (b * (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal)) := by
  set κ := (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal with hκ
  have hκ0 : 0 ≤ κ := ENNReal.toReal_nonneg
  have hu : ∀ k : ℕ, 0 < (((k : ℝ) + 1) ^ 4)⁻¹ := fun k => by positivity
  have hsq : ∀ k : ℕ, √((((k : ℝ) + 1) ^ 4)⁻¹) = (((k : ℝ) + 1) ^ 2)⁻¹ := by
    intro k
    rw [Real.sqrt_inv, show ((k : ℝ) + 1) ^ 4 = (((k : ℝ) + 1) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hδ : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∉ {ω | 1 / ((j : ℝ) + 1) ≤
      |√((((k : ℝ) + 1) ^ 4)⁻¹) * (pathExcursionCount (fun t => B t ω) b ((((k : ℝ) + 1) ^ 4)⁻¹) : ℝ) -
        b * κ|} := by
    intro j
    apply ae_eventually_notMem
    have hc : 0 ≤ b * κ * ((j : ℝ) + 1) ^ 2 := mul_nonneg (mul_nonneg hb.le hκ0) (by positivity)
    have hsum : Summable fun k : ℕ => b * κ * ((j : ℝ) + 1) ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
      have h := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2))
      refine (h.mul_left (b * κ * ((j : ℝ) + 1) ^ 2)).congr fun k => ?_
      push_cast
      ring
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ,
      ENNReal.ofReal (b * κ * ((j : ℝ) + 1) ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹)) ?_ (ENNReal.tsum_le_tsum fun k => ?_)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc (by positivity)) hsum]
      exact ENNReal.ofReal_ne_top
    · refine (measure_le_abs_sqrt_mul_pathExcursionCount_sub_le hB hm hcont hb (hu k)
        (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hsq, ← hκ]
      field_simp
  filter_upwards [ae_all_iff.2 hδ] with ω hω
  refine Metric.tendsto_atTop.2 fun η hη => ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω j)
  refine ⟨N, fun k hk => ?_⟩
  have h : |√((((k : ℝ) + 1) ^ 4)⁻¹) * (pathExcursionCount (fun t => B t ω) b ((((k : ℝ) + 1) ^ 4)⁻¹) : ℝ) -
      b * κ| < 1 / ((j : ℝ) + 1) := not_le.1 (hN k hk)
  rw [Real.dist_eq]
  exact h.trans hj

/-- **The excursion count as an almost sure limit.** For a real Brownian motion `B` with continuous paths and
`b > 0`, almost surely `√ε J_ε(b) → b κ` as `ε → 0+`, where `κ = E J_1(1) < ∞`. -/
theorem ae_tendsto_sqrt_mul_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, Tendsto (fun ε => √ε * (pathExcursionCount (fun t => B t ω) b ε : ℝ)) (𝓝[>] 0)
      (𝓝 (b * (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal)) := by
  filter_upwards [ae_tendsto_sqrt_mul_pathExcursionCount_quartic hB hm hcont hb] with ω hω
  refine tendsto_sqrt_mul_of_antitone_quartic (fun x => Nat.cast_nonneg _) (fun x y hx hxy => ?_) hω
  have h : pathExcursionCount (fun t => B t ω) b y ≤ pathExcursionCount (fun t => B t ω) b x := by
    unfold pathExcursionCount
    exact excursionCount_anti_eps _ _ _ hx hxy
  exact_mod_cast h

end LatticeProb.LadderSet
