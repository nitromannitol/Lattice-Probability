import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiD1

/-!
# The Liouville graph distance exponent from a sandwich with random constants

Ding-Zeitouni-Zhang (arXiv:1807.00422, Theorem 1.1, proof l. 126-141 and Proposition 5.1) obtain the
almost sure exponent of the Liouville graph distance `D_δ(u, v)` by sandwiching it between two
auxiliary distances whose tails have a summable rate along the dyadic scales `2^{-k}`:
`D^{lo}_{c_l δ} ≤ D_δ ≤ D^{up}_{c_u δ}` for small `δ`. When the sandwich comes from a comparison of
measures through a field that is only bounded on compact sets, the constants `c_l, c_u` and the
threshold depend on the sample. This file shows that random constants cost nothing: a distance
antitone in `δ` absorbs any constant `c` between two dyadic scales `2^{-j} ≤ c ≤ 2^i`, so the rates
at the fixed scales `2^{-k}` and Borel-Cantelli give the exponent.

* `LatticeProb.LQG.lgdMinSet_antitone`: the minimal distance between two sets is antitone in `δ`.
* `LatticeProb.LQG.tendsto_lgdRatio_of_scaled_sandwich`: the deterministic statement, along the
  dyadic scales, for a sandwich with fixed positive constants.
* `LatticeProb.LQG.ae_tendsto_lgdRatio_of_random_sandwich`: the almost sure exponent from the rates
  of the two auxiliary distances and an almost sure sandwich with sample-dependent constants.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

open DZZ

/-- The minimal Liouville graph distance between two sets is antitone in `δ`. -/
theorem _root_.LatticeProb.LQG.lgdMinSet_antitone (μ : Measure ℂ) {δ δ' : ℝ} (hδ : 0 ≤ δ)
    (hδδ' : δ ≤ δ') (A B : Set ℂ) : lgdMinSet μ δ' A B ≤ lgdMinSet μ δ A B :=
  iInf₂_mono fun x _ => iInf₂_mono fun y _ => lgdDZZ_antitone μ hδ hδδ' x y

/-- **The exponent along the dyadic scales from a sandwich with constants.** Let `g`, `lo`, `up` be
antitone in `δ > 0` with `1 ≤ g`, let `lo (c_l δ) ≤ g δ ≤ up (c_u δ)` for `0 < δ < δ₀`, and let, for
every `n`, eventually in `k`, `up (2^{-k}) ≤ 2^{k(χ + 1/(n+1))}` and
`2^{k(χ − 1/(n+1))} ≤ lo (2^{-k})`. Then `log g(2^{-k}) / (k log 2) → χ`. -/
theorem _root_.LatticeProb.LQG.tendsto_lgdRatio_of_scaled_sandwich {g lo up : ℝ → ℕ∞}
    {χ cl cu δ₀ : ℝ}
    (hlo : ∀ δ δ', 0 < δ → δ ≤ δ' → lo δ' ≤ lo δ)
    (hup : ∀ δ δ', 0 < δ → δ ≤ δ' → up δ' ≤ up δ)
    (hg1 : ∀ δ, 1 ≤ g δ) (hcl : 0 < cl) (hcu : 0 < cu) (hδ₀ : 0 < δ₀)
    (hsand : ∀ δ, 0 < δ → δ < δ₀ → lo (δ * cl) ≤ g δ ∧ g δ ≤ up (δ * cu))
    (hupR : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop, ((up ((2 : ℝ)⁻¹ ^ k) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (-(χ + 1 / ((n : ℝ) + 1)))))
    (hloR : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (-(χ - 1 / ((n : ℝ) + 1)))) ≤
        ((lo ((2 : ℝ)⁻¹ ^ k) : ℕ∞) : ℝ≥0∞)) :
    Tendsto (fun k : ℕ => Real.log (g ((2 : ℝ)⁻¹ ^ k)).toNat / (k * Real.log 2)) atTop
      (𝓝 χ) := by
  -- dyadic scales bracketing the two constants
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ cu := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hcu (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨j, hj.le⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, cl ≤ (2 : ℝ) ^ i := by
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt cl (by norm_num : (1 : ℝ) < 2)
    exact ⟨i, hi.le⟩
  have hsmall : ∀ᶠ k : ℕ in atTop, (2 : ℝ)⁻¹ ^ k < δ₀ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds hδ₀)
  -- the upper bound, at the shifted scales `2^{-(k+j)} ≤ c_u 2^{-k}`
  have hupper : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop, ((g ((2 : ℝ)⁻¹ ^ k) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j * (2 : ℝ)⁻¹ ^ k) ^ (-(χ + 1 / ((n : ℝ) + 1)))) := by
    intro n
    filter_upwards [(tendsto_add_atTop_nat j).eventually (hupR n), hsmall] with k hk hk2
    have h1 := (hsand _ (by positivity) hk2).2
    have h2 : up ((2 : ℝ)⁻¹ ^ k * cu) ≤ up ((2 : ℝ)⁻¹ ^ (k + j)) :=
      hup _ _ (by positivity) (by rw [pow_add]; exact mul_le_mul_of_nonneg_left hj (by positivity))
    rw [mul_comm ((2 : ℝ)⁻¹ ^ j), ← pow_add]
    exact (ENat.toENNReal_le.2 (h1.trans h2)).trans hk
  -- the lower bound, at the shifted scales `c_l 2^{-k} ≤ 2^{-(k-i)}`
  have hlower : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (((2 : ℝ) ^ i * (2 : ℝ)⁻¹ ^ k) ^ (-(χ - 1 / ((n : ℝ) + 1)))) ≤
        ((g ((2 : ℝ)⁻¹ ^ k) : ℕ∞) : ℝ≥0∞) := by
    intro n
    filter_upwards [(tendsto_sub_atTop_nat i).eventually (hloR n), hsmall,
      eventually_ge_atTop i] with k hk hk2 hki
    have h1 := (hsand _ (by positivity) hk2).1
    have he : (2 : ℝ) ^ i * (2 : ℝ)⁻¹ ^ k = (2 : ℝ)⁻¹ ^ (k - i) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hki
      rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ two_ne_zero, one_pow, one_mul]
    have h2 : lo ((2 : ℝ)⁻¹ ^ (k - i)) ≤ lo ((2 : ℝ)⁻¹ ^ k * cl) :=
      hlo _ _ (mul_pos (by positivity) hcl)
        (by rw [← he, mul_comm ((2 : ℝ) ^ i)]; exact mul_le_mul_of_nonneg_left hi (by positivity))
    rw [he]
    exact hk.trans (ENat.toENNReal_le.2 (h2.trans h1))
  have hfin : ∀ᶠ k : ℕ in atTop, g ((2 : ℝ)⁻¹ ^ k) ≠ ⊤ :=
    (hupper 0).mono fun k hk hT => by
      rw [hT, ENat.toENNReal_top] at hk
      exact ENNReal.ofReal_ne_top (top_le_iff.1 hk)
  refine DZZ.tendsto_div_of_bounds (s₁ := (2 : ℝ)⁻¹ ^ j) (s₂ := (2 : ℝ) ^ i)
    (fun n => ?_) (fun n => ?_)
  · filter_upwards [hupper n] with k hk
    rw [← DZZ.log_rpow_neg_scale (s := (2 : ℝ)⁻¹ ^ j) (by positivity)]
    exact DZZ.log_toNat_le_of_le_ofReal (hg1 _) hk
  · filter_upwards [hlower n, hfin] with k hk hkf
    rw [← DZZ.log_rpow_neg_scale (s := (2 : ℝ) ^ i) (by positivity)]
    exact DZZ.log_le_log_toNat_of_ofReal_le hkf (by positivity) hk

/-- **The almost sure Liouville graph distance exponent from a sandwich with random constants.**
Let `g ω`, `lo ω`, `up ω` be antitone in `δ > 0` with `1 ≤ g ω`, let `up` and `lo` satisfy the
upper and lower rate bounds `P[up_δ > δ^{−χ−ι}]`, `P[lo_δ < δ^{−χ+ι}] ≤ C(δ^c + e^{−(log δ⁻¹)^{0.7}})`
for every `ι > 0`, and let almost surely `lo (c_l δ) ≤ g δ ≤ up (c_u δ)` for all small `δ`, with
constants `c_l, c_u > 0` and a threshold depending on the sample. Then almost surely
`log g_δ / log δ⁻¹ → χ` as `δ ↓ 0`. -/
theorem _root_.LatticeProb.LQG.ae_tendsto_lgdRatio_of_random_sandwich {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {g lo up : Ω → ℝ → ℕ∞} {χ : ℝ}
    (hg : ∀ ω δ δ', 0 < δ → δ ≤ δ' → g ω δ' ≤ g ω δ)
    (hlo : ∀ ω δ δ', 0 < δ → δ ≤ δ' → lo ω δ' ≤ lo ω δ)
    (hup : ∀ ω δ δ', 0 < δ → δ ≤ δ' → up ω δ' ≤ up ω δ)
    (hg1 : ∀ ω δ, 1 ≤ g ω δ)
    (hupR : ∀ ι : ℝ, 0 < ι → HasRate P (fun δ => {ω | ((up ω δ : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}))
    (hloR : ∀ ι : ℝ, 0 < ι → HasRate P (fun δ => {ω | ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
      ((lo ω δ : ℕ∞) : ℝ≥0∞)}))
    (hsand : ∀ᵐ ω ∂P, ∃ cl cu δ₀ : ℝ, 0 < cl ∧ 0 < cu ∧ 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      lo ω (δ * cl) ≤ g ω δ ∧ g ω δ ≤ up ω (δ * cu)) :
    ∀ᵐ ω ∂P, Tendsto (fun δ : ℝ => Real.log (g ω δ).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
  have hι : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hu := ae_all_iff.2 fun n : ℕ => (hupR _ (hι n)).ae_eventually one_pos
  have hl := ae_all_iff.2 fun n : ℕ => (hloR _ (hι n)).ae_eventually one_pos
  filter_upwards [hsand, hu, hl] with ω ⟨cl, cu, δ₀, hcl, hcu, hδ₀, hs⟩ huω hlω
  have key := LatticeProb.LQG.tendsto_lgdRatio_of_scaled_sandwich (hlo ω) (hup ω) (hg1 ω) hcl hcu
    hδ₀ hs (fun n => (huω n).mono fun k hk => by simpa only [one_mul] using hk)
    (fun n => (hlω n).mono fun k hk => by simpa only [one_mul] using hk)
  exact (GMCIdent4.tendsto_lgdRatio_iff_dyadic (hg ω) (hg1 ω) χ).2
    (by simpa only [GMCIdent4.lgdRatio, GMCIdent4.log_inv_two_inv_pow] using key)

end LQGMetric
