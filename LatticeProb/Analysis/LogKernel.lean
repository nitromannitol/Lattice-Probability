import Mathlib

/-!
# Logarithmic kernel under a dyadic volume bound

Let `μ` be a measure on `ℂ` with `μ (ball z (r * (1 / 2) ^ k)) ≤ (r * (1 / 2) ^ k) ^ β` for every `k : ℕ`
(a dyadic volume bound with exponent `β > 0`). The integral of the logarithmic kernel
`log (1 / ‖z - w‖) + 1` over the ball `ball z r`, `0 < r ≤ 1`, is then bounded by a constant times
`r ^ β (1 - 2 ^ (-β))⁻¹` (`setLIntegral_ball_log_le`). The estimate is obtained by summing over the dyadic annuli
`ball z (r * (1 / 2) ^ k)`: the pointwise bound `ofReal_log_le_tsum_indicator` gives the kernel as a sum of
indicators of these balls, and the geometric series `tsum_ofReal_mul_rpow_half_pow` sums the resulting bounds.
Further statements: a measure with `μ (ball z r) ≤ r ^ β` on a closed ball is finite on the open ball
(`measure_ball_lt_top_of_vol`); a union bound over dyadic scales (`measure_compl_iInter_le`); and the absorption
`(log (1 / δ) + 1) δ ^ (β / 2) → 0` as `δ → 0⁺` in the form `exists_pos_log_rpow_le`.

Literature: the logarithmic-correlation normalisation of the Gaussian free field in Duplantier-Sheffield,
arXiv:0808.1560, Sec. 3.1, p. 16 (Green's function `G(x,y) = -log|y-x| - G~_x(y)`).
-/

namespace LatticeProb.LogKernel

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- `(r 2^{-k})^β = r^β (2^{-β})^k`. -/
theorem rpow_mul_half_pow {r : ℝ} (β : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    (r * (1 / 2) ^ k) ^ β = r ^ β * ((1 / 2) ^ β) ^ k := by
  rw [Real.mul_rpow hr (by positivity), ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_comm (k : ℝ) β, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Geometric sum over dyadic scales: `∑_k K (r 2^{-k})^β = K r^β (1 - 2^{-β})⁻¹`. -/
theorem tsum_ofReal_mul_rpow_half_pow {K r β : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hβ : 0 < β) :
    ∑' k : ℕ, ENNReal.ofReal (K * (r * (1 / 2) ^ k) ^ β) =
      ENNReal.ofReal (K * r ^ β * (1 - (1 / 2) ^ β)⁻¹) := by
  have hx0 : 0 ≤ ((1 : ℝ) / 2) ^ β := Real.rpow_nonneg (by norm_num) _
  have hx1 : ((1 : ℝ) / 2) ^ β < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hKr : 0 ≤ K * r ^ β := mul_nonneg hK (Real.rpow_nonneg hr _)
  have h : ∀ k : ℕ, ENNReal.ofReal (K * (r * (1 / 2) ^ k) ^ β) =
      ENNReal.ofReal (K * r ^ β) * ENNReal.ofReal ((1 / 2) ^ β) ^ k := by
    intro k
    rw [rpow_mul_half_pow β hr k, ← mul_assoc, ENNReal.ofReal_mul hKr, ENNReal.ofReal_pow hx0]
  simp_rw [h]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hx0,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hx1), ← ENNReal.ofReal_mul hKr]


/-- Pointwise dyadic bound of the logarithmic kernel on `B_r(z)`, `r ≤ 1`: with `c = log (1/r) + 1 + log 2`,
`log (1/|z - w|) + 1 ≤ c · #{k : |z - w| < r 2^{-k}}` (for `w = z` the right side is infinite). -/
theorem ofReal_log_le_tsum_indicator {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {z w : ℂ} (hw : w ∈ ball z r) :
    ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ≤
      ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator
        (fun _ => ENNReal.ofReal (Real.log (1 / r) + 1 + Real.log 2)) w := by
  set c := Real.log (1 / r) + 1 + Real.log 2 with hc
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr0]; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hwz : w = z
  · rw [hwz]
    have h0 : (ball z (r * (1 / 2) ^ 0)).indicator (fun _ => ENNReal.ofReal c) z = ENNReal.ofReal c :=
      indicator_of_mem (mem_ball_self (by simpa using hr0)) _
    calc ENNReal.ofReal (Real.log (1 / ‖z - z‖) + 1) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := h0.symm
      _ ≤ ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator (fun _ => ENNReal.ofReal c) z :=
          ENNReal.le_tsum (f := fun k : ℕ => (ball z (r * (1 / 2) ^ k)).indicator (fun _ => ENNReal.ofReal c) z) 0
  · have hd : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hwz))
    have hdr : ‖z - w‖ < r := by rw [norm_sub_rev]; exact mem_ball_iff_norm.mp hw
    have hex : ∃ j : ℕ, r * (1 / 2) ^ (j + 1) ≤ ‖z - w‖ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hd hr0) (by norm_num : (1 / 2 : ℝ) < 1)
      have h' : (1 / 2 : ℝ) ^ n * r < ‖z - w‖ := (lt_div_iff₀ hr0).mp hn
      have hpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
      refine ⟨n, ?_⟩
      have e : r * (1 / 2 : ℝ) ^ (n + 1) = r * (1 / 2) ^ n * (1 / 2) := by rw [pow_succ]; ring
      rw [e]
      nlinarith
    classical
    have hj := Nat.find_spec hex
    have hmin : ∀ k < Nat.find hex, ¬ r * (1 / 2) ^ (k + 1) ≤ ‖z - w‖ := fun k hk => Nat.find_min hex hk
    set j := Nat.find hex
    have hlt : ∀ k ≤ j, ‖z - w‖ < r * (1 / 2) ^ k := by
      intro k hk
      rcases k with _ | k
      · simpa using hdr
      · exact not_le.mp (hmin k (by omega))
    have hsum : ∑ k ∈ Finset.range (j + 1), (ball z (r * (1 / 2) ^ k)).indicator (fun _ => ENNReal.ofReal c) w =
        ((j + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c := by
      have h : ∀ k ∈ Finset.range (j + 1),
          (ball z (r * (1 / 2) ^ k)).indicator (fun _ => ENNReal.ofReal c) w = ENNReal.ofReal c := by
        intro k hk
        refine indicator_of_mem (mem_ball_iff_norm.mpr ?_) _
        rw [norm_sub_rev]
        exact hlt k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : 1 / ‖z - w‖ ≤ 2 ^ (j + 1) / r := by
      have h2pos : (0 : ℝ) < 2 ^ (j + 1) := by positivity
      have h := mul_le_mul_of_nonneg_right hj h2pos.le
      rw [mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow, mul_one] at h
      rw [div_le_div_iff₀ hd hr0, one_mul, mul_comm]
      exact h
    have h2 : Real.log (1 / ‖z - w‖) ≤ Real.log (2 ^ (j + 1) / r) :=
      Real.log_le_log (one_div_pos.mpr hd) h1
    have h3 : Real.log (2 ^ (j + 1) / r) = ((j : ℝ) + 1) * Real.log 2 + Real.log (1 / r) := by
      rw [Real.log_div (by positivity) hr0.ne', Real.log_pow, one_div, Real.log_inv]
      push_cast
      ring
    have hreal : Real.log (1 / ‖z - w‖) + 1 ≤ ((j : ℝ) + 1) * c := by
      rw [hc]
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (add_nonneg hL zero_le_one)]
    calc ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ≤ ENNReal.ofReal (((j : ℝ) + 1) * c) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ((j + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c := by
          rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ = _ := hsum.symm
      _ ≤ _ := ENNReal.sum_le_tsum _


/-- **Dyadic bound of the logarithmic integral.** If `μ(B_{r 2^{-k}}(z)) ≤ (r 2^{-k})^β` for all `k`, `0 < r ≤ 1`, then
`∫_{B_r(z)} (log (1/|z - w|) + 1) dμ(w) ≤ (log (1/r) + 1 + log 2) r^β (1 - 2^{-β})⁻¹`. -/
theorem setLIntegral_ball_log_le {μ : Measure ℂ} {z : ℂ} {r β : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hβ : 0 < β)
    (hvol : ∀ k : ℕ, μ (ball z (r * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((r * (1 / 2) ^ k) ^ β)) :
    ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
      ENNReal.ofReal ((Real.log (1 / r) + 1 + Real.log 2) * r ^ β * (1 - (1 / 2) ^ β)⁻¹) := by
  have hc : 0 ≤ Real.log (1 / r) + 1 + Real.log 2 := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 1 / r by rw [le_div_iff₀ hr0]; linarith)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  set c := Real.log (1 / r) + 1 + Real.log 2
  calc ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
      ≤ ∫⁻ w in ball z r, ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator (fun _ => ENNReal.ofReal c) w ∂μ :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2
          (Eventually.of_forall fun w hw => ofReal_log_le_tsum_indicator hr0 hr1 hw))
    _ ≤ ∫⁻ w, ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator (fun _ => ENNReal.ofReal c) w ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ENNReal.ofReal c * μ (ball z (r * (1 / 2) ^ k)) := by
        rw [lintegral_tsum fun k => (measurable_const.indicator measurableSet_ball).aemeasurable]
        exact tsum_congr fun k => lintegral_indicator_const measurableSet_ball _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (c * (r * (1 / 2) ^ k) ^ β) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [ENNReal.ofReal_mul hc]
        gcongr
        exact hvol k
    _ = ENNReal.ofReal (c * r ^ β * (1 - (1 / 2) ^ β)⁻¹) := tsum_ofReal_mul_rpow_half_pow hc hr0.le hβ


/-- A measure with `μ(B_r(z)) ≤ r^β` for every `z ∈ cl B_ρ` is finite on `B_ρ` (finite cover by `r`-balls). -/
theorem measure_ball_lt_top_of_vol {μ : Measure ℂ} {ρ r β : ℝ} (hr : 0 < r)
    (hvol : ∀ z ∈ closedBall (0 : ℂ) ρ, μ (ball z r) ≤ ENNReal.ofReal (r ^ β)) : μ (ball 0 ρ) < ⊤ := by
  obtain ⟨t, ht, htfin, hcover⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) ρ) hr
  exact (measure_mono (ball_subset_closedBall.trans hcover)).trans_lt
    (measure_biUnion_lt_top htfin fun x hx => (hvol x (ht hx)).trans_lt ENNReal.ofReal_lt_top)


/-- Union bound over the dyadic scales `r 2^{-k}` for a family of events with
`P[(E s)ᶜ] ≤ K s^p` for `0 < s < r₀`. -/
theorem measure_compl_iInter_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    {K p r₀ : ℝ} (hp : 0 < p) (hE : ∀ s, 0 < s → s < r₀ → P (E s)ᶜ ≤ ENNReal.ofReal (K * s ^ p))
    {r : ℝ} (hr : 0 < r) (hrr : r < r₀) {F : Set Ω} (hF : (⋂ k : ℕ, E (r * (1 / 2) ^ k)) ⊆ F) :
    P Fᶜ ≤ ENNReal.ofReal (max K 0 * (1 - (1 / 2) ^ p)⁻¹ * r ^ p) := by
  have hpos : ∀ k : ℕ, 0 < r * (1 / 2) ^ k := fun k => mul_pos hr (pow_pos (by norm_num) k)
  have hlt : ∀ k : ℕ, r * (1 / 2) ^ k < r₀ := fun k =>
    lt_of_le_of_lt (mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))) hrr
  calc P Fᶜ ≤ P (⋃ k : ℕ, (E (r * (1 / 2) ^ k))ᶜ) := by
        refine measure_mono ?_
        rw [← Set.compl_iInter]
        exact Set.compl_subset_compl.mpr hF
    _ ≤ ∑' k : ℕ, P (E (r * (1 / 2) ^ k))ᶜ := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (max K 0 * (r * (1 / 2) ^ k) ^ p) :=
        ENNReal.tsum_le_tsum fun k => (hE _ (hpos k) (hlt k)).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hpos k).le _)))
    _ = ENNReal.ofReal (max K 0 * r ^ p * (1 - (1 / 2) ^ p)⁻¹) :=
        tsum_ofReal_mul_rpow_half_pow (le_max_right _ _) hr.le hp
    _ = ENNReal.ofReal (max K 0 * (1 - (1 / 2) ^ p)⁻¹ * r ^ p) := by
        congr 1
        ring


/-- An eventual property as `r → 0⁺` holds on an interval `(0, r₁)`. -/
theorem exists_pos_of_eventually_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → p r := by
  obtain ⟨r₁, hr₁, h'⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp h
  exact ⟨r₁, hr₁, fun r hr hrr => h' ⟨hr, hrr⟩⟩


/-- Absorption of the logarithm: `(log (1/(2δ)) + 1 + log 2) (2δ)^β (1 - 2^{-β})⁻¹ ≤ δ^{β/2}` for small `δ > 0`. -/
theorem exists_pos_log_rpow_le {β : ℝ} (hβ : 0 < β) :
    ∃ δ₁ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      (Real.log (1 / (2 * δ)) + 1 + Real.log 2) * (2 * δ) ^ β * (1 - (1 / 2) ^ β)⁻¹ ≤ δ ^ (β / 2) := by
  set A := (1 - ((1 : ℝ) / 2) ^ β)⁻¹
  have t1 : Tendsto (fun δ : ℝ => Real.log δ * δ ^ (β / 2)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (half_pos hβ)
  have t2 : Tendsto (fun δ : ℝ => δ ^ (β / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun δ : ℝ => δ ^ (β / 2)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (β / 2))) :=
      h1.rpow_const (Or.inr (half_pos hβ).le)
    rwa [Real.zero_rpow (half_pos hβ).ne'] at h2
  have t3 : Tendsto (fun δ : ℝ => (-(Real.log δ * δ ^ (β / 2)) + δ ^ (β / 2)) * (2 ^ β * A)) (𝓝[>] 0)
      (𝓝 ((-0 + 0) * (2 ^ β * A))) := (t1.neg.add t2).mul_const _
  rw [neg_zero, zero_add, zero_mul] at t3
  obtain ⟨δ₁, hδ₁, h⟩ := exists_pos_of_eventually_nhdsGT ((tendsto_order.1 t3).2 1 one_pos)
  refine ⟨δ₁, hδ₁, fun δ hδ hδδ => ?_⟩
  have e1 : Real.log (1 / (2 * δ)) = -Real.log 2 - Real.log δ := by
    rw [one_div, Real.log_inv, Real.log_mul two_ne_zero hδ.ne']
    ring
  have e2 : (2 * δ) ^ β = 2 ^ β * (δ ^ (β / 2) * δ ^ (β / 2)) := by
    rw [Real.mul_rpow zero_le_two hδ.le, ← Real.rpow_add hδ, add_halves]
  rw [e1, e2]
  have hd : 0 ≤ δ ^ (β / 2) := Real.rpow_nonneg hδ.le _
  calc (-Real.log 2 - Real.log δ + 1 + Real.log 2) * (2 ^ β * (δ ^ (β / 2) * δ ^ (β / 2))) * A
      = ((-(Real.log δ * δ ^ (β / 2)) + δ ^ (β / 2)) * (2 ^ β * A)) * δ ^ (β / 2) := by ring
    _ ≤ 1 * δ ^ (β / 2) := mul_le_mul_of_nonneg_right (h δ hδ hδδ).le hd
    _ = δ ^ (β / 2) := one_mul _


end LatticeProb.LogKernel
