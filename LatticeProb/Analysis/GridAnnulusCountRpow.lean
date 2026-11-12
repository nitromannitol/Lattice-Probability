import LatticeProb.Analysis.GridAnnulusCount

/-!
# Polynomial count of the grid annuli at scale `ε`

For the grid of annuli of `gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂` (centres on the lattice `η ℤ²` in
the closed disc of radius `ρ`, outer radii `q ^ a ∈ [x₁, y₁]`, inner radii `q ^ b ∈ [x₂, y₂]`) at
scale `ε`, with mesh `η = ε ^ a`, smallest radii `x_i = b_i ε ^ {p_i}` and fixed largest radii `Y_i`,
the number of grid annuli is at most `K ε ^ {-(2a + δ)}` for every `δ > 0`: the lattice factor is
`O(ε ^ {-2a})` and each logarithmic factor `log_q (Y_i / x_i) + 1 = O(log (1/ε))` is `O(ε ^ {-δ/2})`.
This is the count needed for a union bound over the grid with polynomially small failure
probabilities.

* `exists_logb_div_mul_rpow_add_one_le`: `log_q (Y / (b ε ^ p)) + 1 ≤ K ε ^ {-δ}` on `(0, 1)`;
* `two_mul_div_rpow_add_three_le`: `2ρ / ε ^ a + 3 ≤ (2ρ + 3) ε ^ {-a}` on `(0, 1]`;
* `exists_card_gridAnnulusIndex_le_rpow`: the count `#gridAnnulusIndex ≤ K ε ^ {-(2a + δ)}`.
-/

namespace LatticeProb

/-- **Logarithmic factors are smaller than any power.** For `q > 1`, `b, Y > 0`, `p ≥ 0` and
`δ > 0` there is `K ≥ 0` with `log_q (Y / (b ε ^ p)) + 1 ≤ K ε ^ {-δ}` for all `ε ∈ (0, 1)`. -/
theorem exists_logb_div_mul_rpow_add_one_le {q b p Y δ : ℝ} (hq : 1 < q) (hb : 0 < b) (hp : 0 ≤ p)
    (hY : 0 < Y) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      Real.logb q (Y / (b * ε ^ p)) + 1 ≤ K * ε ^ (-δ) := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  refine ⟨(|Real.log Y - Real.log b| + p / δ) / Real.log q + 1,
    add_nonneg (div_nonneg (add_nonneg (abs_nonneg _) (div_nonneg hp hδ.le)) hlq.le) zero_le_one,
    fun ε hε hε1 => ?_⟩
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have h1 : 1 ≤ ε ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by linarith)
  have hlog : Real.logb q (Y / (b * ε ^ p)) =
      (Real.log Y - Real.log b - p * Real.log ε) / Real.log q := by
    rw [Real.logb, Real.log_div hY.ne' (mul_pos hb hεp).ne', Real.log_mul hb.ne' hεp.ne',
      Real.log_rpow hε]
    ring
  have hlε : -Real.log ε ≤ ε ^ (-δ) / δ := by
    have h := Real.log_le_rpow_div (inv_nonneg.mpr hε.le) hδ
    rwa [Real.log_inv, Real.inv_rpow hε.le, ← Real.rpow_neg hε.le] at h
  have hA : Real.log Y - Real.log b ≤ |Real.log Y - Real.log b| * ε ^ (-δ) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) h1)
  have hpL : p * (-Real.log ε) ≤ p / δ * ε ^ (-δ) := by
    calc p * (-Real.log ε) ≤ p * (ε ^ (-δ) / δ) := mul_le_mul_of_nonneg_left hlε hp
      _ = p / δ * ε ^ (-δ) := by ring
  rw [hlog]
  calc (Real.log Y - Real.log b - p * Real.log ε) / Real.log q + 1
      ≤ (|Real.log Y - Real.log b| * ε ^ (-δ) + p / δ * ε ^ (-δ)) / Real.log q + ε ^ (-δ) :=
        add_le_add (div_le_div_of_nonneg_right (by linarith) hlq.le) h1
    _ = ((|Real.log Y - Real.log b| + p / δ) / Real.log q + 1) * ε ^ (-δ) := by ring

/-- `2ρ / ε ^ a + 3 ≤ (2ρ + 3) ε ^ {-a}` for `a ≥ 0` and `ε ∈ (0, 1]`. -/
theorem two_mul_div_rpow_add_three_le {ρ a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : 2 * ρ / ε ^ a + 3 ≤ (2 * ρ + 3) * ε ^ (-a) := by
  have h1 : 1 ≤ ε ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hdiv : 2 * ρ / ε ^ a = 2 * ρ * ε ^ (-a) := by
    rw [Real.rpow_neg hε.le, div_eq_mul_inv]
  rw [hdiv]
  nlinarith

/-- **Polynomial count of the grid annuli.** Let `q > 1`, `ρ ≥ 0`, `a ≥ 0`, `δ > 0`, and for
`i = 1, 2` let `0 < b_i ≤ Y_i` and `p_i ≥ 0`. There is `K ≥ 0` such that for every `ε ∈ (0, 1)`
the grid with mesh `ε ^ a`, outer radii in `[b₁ ε ^ {p₁}, Y₁]` and inner radii in
`[b₂ ε ^ {p₂}, Y₂]` has at most `K ε ^ {-(2a + δ)}` annuli. -/
theorem exists_card_gridAnnulusIndex_le_rpow {q ρ a b₁ p₁ Y₁ b₂ p₂ Y₂ δ : ℝ} (hq : 1 < q)
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hb₁ : 0 < b₁) (hp₁ : 0 ≤ p₁) (hbY₁ : b₁ ≤ Y₁) (hb₂ : 0 < b₂)
    (hp₂ : 0 ≤ p₂) (hbY₂ : b₂ ≤ Y₂) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ((gridAnnulusIndex q (ε ^ a) ρ (b₁ * ε ^ p₁) Y₁ (b₂ * ε ^ p₂) Y₂).card : ℝ) ≤
        K * ε ^ (-(2 * a + δ)) := by
  obtain ⟨K₁, hK₁, hL₁⟩ := exists_logb_div_mul_rpow_add_one_le hq hb₁ hp₁ (hb₁.trans_le hbY₁)
    (half_pos hδ)
  obtain ⟨K₂, hK₂, hL₂⟩ := exists_logb_div_mul_rpow_add_one_le hq hb₂ hp₂ (hb₂.trans_le hbY₂)
    (half_pos hδ)
  refine ⟨(2 * ρ + 3) ^ 2 * (K₁ * K₂), by positivity, fun ε hε hε1 => ?_⟩
  have hx : ∀ {b p Y : ℝ}, 0 < b → 0 ≤ p → b ≤ Y → 0 < b * ε ^ p ∧ b * ε ^ p ≤ Y ∧
      0 ≤ Real.logb q (Y / (b * ε ^ p)) + 1 := by
    intro b p Y hb hp hbY
    have hpos : 0 < b * ε ^ p := mul_pos hb (Real.rpow_pos_of_pos hε p)
    have hle : b * ε ^ p ≤ Y :=
      (mul_le_of_le_one_right hb.le (Real.rpow_le_one hε.le hε1.le hp)).trans hbY
    exact ⟨hpos, hle, by linarith [Real.logb_nonneg hq ((one_le_div hpos).2 hle)]⟩
  obtain ⟨hx₁, hxY₁, hL₁0⟩ := hx hb₁ hp₁ hbY₁
  obtain ⟨hx₂, hxY₂, hL₂0⟩ := hx hb₂ hp₂ hbY₂
  have hX : (2 * ρ / ε ^ a + 3) ^ 2 ≤ ((2 * ρ + 3) * ε ^ (-a)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (two_mul_div_rpow_add_three_le ha hε hε1.le) 2
  have huv : (Real.logb q (Y₁ / (b₁ * ε ^ p₁)) + 1) * (Real.logb q (Y₂ / (b₂ * ε ^ p₂)) + 1) ≤
      (K₁ * ε ^ (-(δ / 2))) * (K₂ * ε ^ (-(δ / 2))) :=
    mul_le_mul (hL₁ ε hε hε1) (hL₂ ε hε hε1) hL₂0 (by positivity)
  have hsplit : ε ^ (-(2 * a + δ)) = ε ^ (-a) * ε ^ (-a) * ε ^ (-(δ / 2)) * ε ^ (-(δ / 2)) := by
    rw [show -(2 * a + δ) = -a + -a + -(δ / 2) + -(δ / 2) by ring, Real.rpow_add hε,
      Real.rpow_add hε, Real.rpow_add hε]
  calc ((gridAnnulusIndex q (ε ^ a) ρ (b₁ * ε ^ p₁) Y₁ (b₂ * ε ^ p₂) Y₂).card : ℝ)
      ≤ (2 * ρ / ε ^ a + 3) ^ 2 *
          ((Real.logb q (Y₁ / (b₁ * ε ^ p₁)) + 1) * (Real.logb q (Y₂ / (b₂ * ε ^ p₂)) + 1)) :=
        card_gridAnnulusIndex_le hq (Real.rpow_pos_of_pos hε a) hρ hx₁ hxY₁ hx₂ hxY₂
    _ ≤ ((2 * ρ + 3) * ε ^ (-a)) ^ 2 * ((K₁ * ε ^ (-(δ / 2))) * (K₂ * ε ^ (-(δ / 2)))) :=
        mul_le_mul hX huv (mul_nonneg hL₁0 hL₂0) (by positivity)
    _ = (2 * ρ + 3) ^ 2 * (K₁ * K₂) * ε ^ (-(2 * a + δ)) := by rw [hsplit]; ring

end LatticeProb
