/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6Rate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate5Rate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47kG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateUnion

/-!
# The rate condition of `gm_T42_reg`, uniform in the scale (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.7 (4.14), (4.19) as used in
Lemma 4.21 (l. 2380–2390: `κ = ε^{2ν+o(1)}`, `e = o^∞_ε(ε)`) and Proposition 4.17 (l. 2404–2433).
With `X = #ℛ (4λ₄ε)^{2−1/M₈}𝕣² / (λ₁ε^{1+ν}𝕣/4)² + 1 = #ℛ c₁ ε^{-(2ν+1/M₈)} + 1`, `#ℛ ≤ μ log₈ ε⁻¹`,
and `g = #(candidates) √δ` with `#(candidates) ≲ ε^{-2M₈-2-2ν} #ℛ` (`gm_grid_card_le`, the
candidate radius `‖𝕫‖ + (4λ₄ε)^{-M₈}𝕣 + 2λ₄ε𝕣 + 𝕣`, `‖𝕫‖ ≤ B𝕣`) and `δ ≤ C₈ε^p`, `p` large
(Lemma 4.8, `gm_L4_8_uncondU`): `g ≤ 1/(4Λ)` and `gm_T42_rate_abs` applies. All thresholds depend
only on the numbers, not on `𝕣`. Own elementary bookkeeping of GM's "`o^∞_ε(ε)`".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace LQGMetric.GM

/-- `#ℛ ≤ ⌊μ log₈ ε⁻¹⌋` -/
theorem gm_rads_card_le {R : RegPar} {𝕣 ε : ℝ} {Rads : Finset ℝ}
    (hRads : (Rads : Set ℝ) = p4Rads R 𝕣 ε) : Rads.card ≤ ⌊R.μ * Real.logb 8 ε⁻¹⌋₊ := by
  rw [← Set.ncard_coe_finset, hRads, p4Rads]
  refine (Set.ncard_image_le (Set.finite_Iio _)).trans ?_
  rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- the number of candidate pairs `(z, r)`: grid points of `B_L(0)` times `#ℛ` -/
theorem gm_candSet_ncard_le (R : RegPar) {𝕣 ε L : ℝ}
    (hs : 0 < R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (hL : 0 ≤ L) {Rads : Finset ℝ}
    (hRads : (Rads : Set ℝ) = p4Rads R 𝕣 ε) :
    ((gmCandSet R 𝕣 ε L).ncard : ℝ) * (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 ≤
      4 * (L + 2 * (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4)) ^ 2 * Rads.card := by
  set s := R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4
  have hfin := gm_gridPts_ball_finite (L := L) hs
  have hA := gm_grid_card_le hs hL hfin.toFinset (fun z hz => hfin.mem_toFinset.1 hz)
  rw [gmCandSet, Set.ncard_prod, ← hRads, Set.ncard_coe_finset,
    Set.ncard_eq_toFinset_card _ hfin]
  push_cast
  have hN : (0 : ℝ) ≤ Rads.card := Nat.cast_nonneg _
  calc ((hfin.toFinset.card : ℝ) * Rads.card) * s ^ 2 = (hfin.toFinset.card * s ^ 2) * Rads.card := by
        ring
    _ ≤ 4 * (L + 2 * s) ^ 2 * Rads.card := mul_le_mul_of_nonneg_right hA hN

/-- `#ℛ (4λ₄ε)^{2−1/M₈}𝕣² / (λ₁ε^{1+ν}𝕣/4)² = #ℛ c₁ ε^{-(2ν+1/M₈)}` -/
theorem gm_X_eq {N l0 l3 ν M₈ 𝕣 ε : ℝ} (hl0 : 0 < l0) (hl3 : 0 < l3) (h𝕣 : 0 < 𝕣) (hε : 0 < ε) :
    N * ((4 * l3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) / (l0 * ε ^ (1 + ν) * 𝕣 / 4) ^ 2 =
      N * (16 * (4 * l3) ^ (2 - 1 / M₈) / l0 ^ 2 * ε ^ (-(2 * ν + 1 / M₈))) := by
  have h1 : ε ^ (2 - 1 / M₈) = ε ^ (-(2 * ν + 1 / M₈)) * (ε ^ (1 + ν)) ^ 2 := by
    rw [← Real.rpow_natCast (ε ^ (1 + ν)) 2, ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
    congr 1; push_cast; ring
  have hp : 0 < ε ^ (1 + ν) := Real.rpow_pos_of_pos hε _
  rw [Real.mul_rpow (by positivity) hε.le, h1]
  field_simp
  norm_num

/-- the candidate radius plus `2s` is `≤ Q (4λ₄ε)^{-M₈} 𝕣` -/
theorem gm_cand_radius_le {B l0 l3 ν M₈ 𝕣 ε : ℝ} {𝕫 : ℂ} (hl0 : 0 < l0) (hl3 : 0 < l3)
    (hν : 0 ≤ ν) (hM₈ : 0 < M₈) (h𝕣 : 0 < 𝕣) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hε3 : 4 * l3 * ε ≤ 1) (h𝕫 : ‖𝕫‖ ≤ B * 𝕣) :
    ‖𝕫‖ + (4 * l3 * ε) ^ (-M₈) * 𝕣 + 2 * l3 * ε * 𝕣 + 𝕣 + 2 * (l0 * ε ^ (1 + ν) * 𝕣 / 4) ≤
      (B + 2 * l3 + l0 + 2) * (4 * l3 * ε) ^ (-M₈) * 𝕣 := by
  have hy0 : 0 < 4 * l3 * ε := by positivity
  have hy1 : 1 ≤ (4 * l3 * ε) ^ (-M₈) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hε3 (by linarith)
  have hp1 : ε ^ (1 + ν) ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith)
  have hB : 0 ≤ B * 𝕣 := le_trans (norm_nonneg _) h𝕫
  have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left hB h𝕣
  have e1 : 2 * l3 * ε * 𝕣 ≤ 2 * l3 * 𝕣 := by
    have := mul_le_mul_of_nonneg_left hε1 (show 0 ≤ 2 * l3 * 𝕣 by positivity)
    linarith
  have e2 : 2 * (l0 * ε ^ (1 + ν) * 𝕣 / 4) ≤ l0 * 𝕣 := by
    have := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ l0 * 𝕣 by positivity)
    have : 0 ≤ l0 * 𝕣 := by positivity
    linarith
  have hy𝕣 : 𝕣 ≤ (4 * l3 * ε) ^ (-M₈) * 𝕣 := by nlinarith
  have hQ : 0 ≤ B + 2 * l3 + l0 + 1 := by linarith
  have : (B + 2 * l3 + l0 + 1) * 𝕣 ≤ (B + 2 * l3 + l0 + 1) * ((4 * l3 * ε) ^ (-M₈) * 𝕣) :=
    mul_le_mul_of_nonneg_left hy𝕣 hQ
  nlinarith

/-- **`g = #(candidates)·√δ ≤ K₀ ε`** for `δ ≤ C₈ε^p`, `p ≥ 4M₈ + 4ν + 8`, uniformly in `𝕣` -/
theorem gm_g_le {B l0 l3 ν μ M₈ C₈ p 𝕣 ε δ : ℝ} {𝕫 : ℂ} (hl0 : 0 < l0) (hl3 : 0 < l3)
    (hν : 0 ≤ ν) (hμ : 0 ≤ μ) (hM₈ : 0 < M₈) (hC : 0 ≤ C₈) (hp : 4 * M₈ + 4 * ν + 8 ≤ p)
    (h𝕣 : 0 < 𝕣) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hε3 : 4 * l3 * ε ≤ 1) (h𝕫 : ‖𝕫‖ ≤ B * 𝕣)
    (R : RegPar) (hR0 : R.lam 0 = l0) (hR3 : R.lam 3 = l3) (hRν : R.ν = ν) (hRμ : R.μ = μ)
    {Rads : Finset ℝ} (hRads : (Rads : Set ℝ) = p4Rads R 𝕣 ε) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ C₈ * ε ^ p) :
    ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣)).ncard
        : ℝ) * Real.sqrt δ ≤
      64 * (B + 2 * l3 + l0 + 2) ^ 2 / l0 ^ 2 * ((4 * l3) ^ (-M₈)) ^ 2 * (μ / Real.log 8) *
        Real.sqrt C₈ * ε := by
  subst hR0 hR3 hRν hRμ
  have hs : 0 < R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 := by positivity
  have hB : 0 ≤ B * 𝕣 := le_trans (norm_nonneg _) h𝕫
  have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left hB h𝕣
  have hY0 : 0 ≤ (4 * R.lam 3 * ε) ^ (-M₈) := Real.rpow_nonneg (by positivity) _
  have hL0 : 0 ≤ ‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣 := by
    positivity
  have h1 := gm_candSet_ncard_le R hs hL0 hRads
  have h2 := gm_cand_radius_le (B := B) hl0 hl3 hν hM₈ h𝕣 hε0 hε1 hε3 h𝕫
  -- `#ℛ ≤ (μ / log 8) ε⁻¹`
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).2 hε1
  have hN1 : (Rads.card : ℝ) ≤ R.μ / Real.log 8 * ε⁻¹ := by
    have hc := gm_rads_card_le hRads
    have hlb : 0 ≤ R.μ * Real.logb 8 ε⁻¹ := mul_nonneg hμ (Real.logb_nonneg (by norm_num) hinv)
    have hc' : (Rads.card : ℝ) ≤ (⌊R.μ * Real.logb 8 ε⁻¹⌋₊ : ℝ) := by exact_mod_cast hc
    have h0 : (Rads.card : ℝ) ≤ R.μ * Real.logb 8 ε⁻¹ := hc'.trans (Nat.floor_le hlb)
    rw [← Real.log_div_log] at h0
    have hl : Real.log ε⁻¹ ≤ ε⁻¹ :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc (Rads.card : ℝ) ≤ R.μ * (Real.log ε⁻¹ / Real.log 8) := h0
      _ = R.μ / Real.log 8 * Real.log ε⁻¹ := by ring
      _ ≤ R.μ / Real.log 8 * ε⁻¹ := mul_le_mul_of_nonneg_left hl (by positivity)
  -- `√δ ≤ √C₈ ε^{p/2}`
  have hsq : Real.sqrt δ ≤ Real.sqrt C₈ * ε ^ (p / 2) := by
    refine (Real.sqrt_le_sqrt hδ).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (ε ^ p), ← Real.rpow_mul hε0.le]
    congr 2; ring
  -- `Y² = A² ε^{-2M₈}`
  have hYe : ((4 * R.lam 3 * ε) ^ (-M₈)) ^ 2 =
      ((4 * R.lam 3) ^ (-M₈)) ^ 2 * ε ^ (-(2 * M₈)) := by
    rw [Real.mul_rpow (by positivity) hε0.le, mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]; congr 1; push_cast; ring
  -- exponents
  have hexp : ε ^ (-(2 * M₈)) * ε⁻¹ * ε ^ (p / 2) ≤ ε * (ε ^ (1 + R.ν)) ^ 2 := by
    have l1 : ε ^ (-(2 * M₈)) * ε⁻¹ * ε ^ (p / 2) = ε ^ (p / 2 - 2 * M₈ - 1) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hε0, ← Real.rpow_add hε0]; congr 1; ring
    have l2 : ε * (ε ^ (1 + R.ν)) ^ 2 = ε ^ (3 + 2 * R.ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
      rw [show ε * ε ^ ((1 + R.ν) * ((2 : ℕ) : ℝ)) = ε ^ (1 : ℝ) * ε ^ ((1 + R.ν) * ((2 : ℕ) : ℝ))
        by rw [Real.rpow_one], ← Real.rpow_add hε0]; congr 1; push_cast; ring
    rw [l1, l2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have he0 : 0 < ε ^ (1 + R.ν) := Real.rpow_pos_of_pos hε0 _
  have hsqδ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hK : 0 ≤ 64 * (B + 2 * R.lam 3 + R.lam 0 + 2) ^ 2 / R.lam 0 ^ 2 *
      ((4 * R.lam 3) ^ (-M₈)) ^ 2 * (R.μ / Real.log 8) * Real.sqrt C₈ := by positivity
  have hA2 : 0 ≤ ((4 * R.lam 3) ^ (-M₈)) ^ 2 := by positivity
  have hQ0 : 0 ≤ B + 2 * R.lam 3 + R.lam 0 + 2 := by linarith
  have hnc0 : (0 : ℝ) ≤ ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 +
    2 * R.lam 3 * ε * 𝕣 + 𝕣)).ncard : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (Rads.card : ℝ) := Nat.cast_nonneg _
  have hz0 : 0 ≤ ‖𝕫‖ := norm_nonneg _
  generalize ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 +
    𝕣)).ncard : ℝ) = nc at h1 hnc0 ⊢
  generalize (Rads.card : ℝ) = N at h1 hN1 hN0
  generalize ε ^ (1 + R.ν) = e at h1 h2 hexp he0
  generalize (4 * R.lam 3 * ε) ^ (-M₈) = Y at h1 h2 hYe hY0 hL0
  generalize ‖𝕫‖ = z at h1 h2 hL0 hz0
  generalize ((4 * R.lam 3) ^ (-M₈)) ^ 2 = A at hYe hK hA2 ⊢
  generalize B + 2 * R.lam 3 + R.lam 0 + 2 = Q at h2 hK hQ0 ⊢
  have hW0 : 0 ≤ z + Y * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣 + 2 * (R.lam 0 * e * 𝕣 / 4) := by
    positivity
  have h3 := pow_le_pow_left₀ hW0 h2 2
  have h4 : nc * (R.lam 0 ^ 2 * e ^ 2) * 𝕣 ^ 2 ≤ 64 * Q ^ 2 * Y ^ 2 * N * 𝕣 ^ 2 := by
    have e1 : nc * (R.lam 0 ^ 2 * e ^ 2) * 𝕣 ^ 2 = 16 * (nc * (R.lam 0 * e * 𝕣 / 4) ^ 2) := by
      ring
    have e2 : 64 * Q ^ 2 * Y ^ 2 * N * 𝕣 ^ 2 = 16 * (4 * N * (Q * Y * 𝕣) ^ 2) := by ring
    have := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 4 * N by positivity)
    rw [e1, e2]
    nlinarith
  have h4' : nc * (R.lam 0 ^ 2 * e ^ 2) ≤ 64 * Q ^ 2 * Y ^ 2 * N :=
    le_of_mul_le_mul_right h4 (by positivity)
  have hY2 : 0 ≤ 64 * Q ^ 2 * Y ^ 2 := by positivity
  have h5 : nc * Real.sqrt δ * (R.lam 0 ^ 2 * e ^ 2) ≤
      64 * Q ^ 2 * A * (R.μ / Real.log 8) * Real.sqrt C₈ *
        (ε ^ (-(2 * M₈)) * ε⁻¹ * ε ^ (p / 2)) := by
    calc nc * Real.sqrt δ * (R.lam 0 ^ 2 * e ^ 2) = nc * (R.lam 0 ^ 2 * e ^ 2) * Real.sqrt δ := by
          ring
      _ ≤ 64 * Q ^ 2 * Y ^ 2 * N * Real.sqrt δ := mul_le_mul_of_nonneg_right h4' hsqδ
      _ ≤ 64 * Q ^ 2 * Y ^ 2 * (R.μ / Real.log 8 * ε⁻¹) * (Real.sqrt C₈ * ε ^ (p / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hN1 hY2) hsq hsqδ (by positivity)
      _ = _ := by rw [hYe]; ring
  have hK' : 0 ≤ 64 * Q ^ 2 * A * (R.μ / Real.log 8) * Real.sqrt C₈ := by positivity
  have h6 := h5.trans (mul_le_mul_of_nonneg_left hexp hK')
  have hl2 : 0 < R.lam 0 ^ 2 * e ^ 2 := by positivity
  have h7 : nc * Real.sqrt δ * (R.lam 0 ^ 2 * e ^ 2) ≤
      (64 * Q ^ 2 / R.lam 0 ^ 2 * A * (R.μ / Real.log 8) * Real.sqrt C₈ * ε) *
        (R.lam 0 ^ 2 * e ^ 2) := by
    have : (64 * Q ^ 2 / R.lam 0 ^ 2 * A * (R.μ / Real.log 8) * Real.sqrt C₈ * ε) *
        (R.lam 0 ^ 2 * e ^ 2) =
        64 * Q ^ 2 * A * (R.μ / Real.log 8) * Real.sqrt C₈ * (ε * e ^ 2) := by
      field_simp
    rw [this]; exact h6
  exact le_of_mul_le_mul_right h7 hl2

/-- **the rate condition of `gm_T42_reg`** (`ε^{2ν+ζ/2} ≤ κ/2 − e ≤ 1`, GM l. 2380–2433), for
`δ ≤ C₈ε^p`, `p ≥ 4M₈ + 4ν + 8`, `M₈ > 2/ζ`, `‖𝕫‖ ≤ B𝕣`; `ε₂` depends only on the numbers -/
theorem gm_T42_rateU {Λ ν ζ M₈ μ l0 l3 B C₈ p : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 ≤ ν) (hζ : 0 < ζ)
    (hM0 : 0 < M₈) (hM : 2 / ζ < M₈) (hl0 : 0 < l0) (hl3 : 0 < l3) (hμ : 0 ≤ μ) (hC : 0 ≤ C₈)
    (hp : 4 * M₈ + 4 * ν + 8 ≤ p) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₂, ∀ R : RegPar, R.lam 0 = l0 → R.lam 3 = l3 →
      R.ν = ν → R.μ = μ → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ 𝕫 : ℂ, ‖𝕫‖ ≤ B * 𝕣 →
      ∀ Rads : Finset ℝ, (Rads : Set ℝ) = p4Rads R 𝕣 ε → ∀ δ : ℝ, 0 ≤ δ → δ ≤ C₈ * ε ^ p →
      ε ^ (2 * ν + ζ / 2) ≤
        (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ / 2 -
        ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) ∧
      (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ / 2 -
        ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) ≤ 1 := by
  have hΛ0 : 0 < Λ := by linarith
  have hc₁ : 0 ≤ 16 * (4 * l3) ^ (2 - 1 / M₈) / l0 ^ 2 := by positivity
  obtain ⟨ε₂, hε₂, HA⟩ := gm_T42_rate_abs (c₄ := μ / Real.log 8) hΛ0 hc₁ hν hζ hM0 hM
  set K₀ := 64 * (B + 2 * l3 + l0 + 2) ^ 2 / l0 ^ 2 * ((4 * l3) ^ (-M₈)) ^ 2 *
    (μ / Real.log 8) * Real.sqrt C₈ with hK₀
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  refine ⟨min ε₂ (min (min 1 (1 / (4 * l3))) (1 / (4 * Λ * (K₀ + 1)))),
    lt_min hε₂ (lt_min (lt_min one_pos (by positivity)) (by positivity)), ?_⟩
  intro ε hε R hR0 hR3 hRν hRμ 𝕣 h𝕣 𝕫 h𝕫 Rads hRads δ hδ0 hδ
  have hε0 : 0 < ε := hε.1
  have hεA : ε ∈ Ioo 0 ε₂ := ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩
  have hεB := hε.2.trans_le (min_le_right _ _)
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hεB ((min_le_left _ _).trans (min_le_left _ _))).le
  have hε3 : 4 * l3 * ε ≤ 1 := by
    have := lt_of_lt_of_le hεB ((min_le_left _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at this; linarith
  have hεK : ε * (4 * Λ * (K₀ + 1)) ≤ 1 := by
    have := lt_of_lt_of_le hεB (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this; linarith
  have hg := gm_g_le (B := B) hl0 hl3 hν hμ hM0 hC hp h𝕣 hε0 hε1 hε3 h𝕫 R hR0 hR3 hRν hRμ hRads
    hδ0 hδ
  rw [← hK₀] at hg
  subst hR0 hR3 hRν hRμ
  rw [gm_X_eq hl0 hl3 h𝕣 hε0]
  set g := ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 +
    𝕣)).ncard : ℝ) * Real.sqrt δ with hgdef
  have hg0 : 0 ≤ g := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hg4 : g ≤ 1 / (4 * Λ) := by
    rw [le_div_iff₀ (by positivity)]
    have : K₀ * ε * (4 * Λ) ≤ 1 := by nlinarith
    nlinarith
  have hN0 : (0 : ℝ) ≤ Rads.card := Nat.cast_nonneg _
  have hNl : (Rads.card : ℝ) ≤ R.μ / Real.log 8 * Real.log ε⁻¹ + 1 := by
    have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).2 hε1
    have hc := gm_rads_card_le hRads
    have hlb : 0 ≤ R.μ * Real.logb 8 ε⁻¹ := mul_nonneg hμ (Real.logb_nonneg (by norm_num) hinv)
    have hc' : (Rads.card : ℝ) ≤ (⌊R.μ * Real.logb 8 ε⁻¹⌋₊ : ℝ) := by exact_mod_cast hc
    have h0 : (Rads.card : ℝ) ≤ R.μ * Real.logb 8 ε⁻¹ := hc'.trans (Nat.floor_le hlb)
    rw [← Real.log_div_log] at h0
    have : R.μ * (Real.log ε⁻¹ / Real.log 8) = R.μ / Real.log 8 * Real.log ε⁻¹ := by ring
    linarith
  refine ⟨HA ε hεA _ g hN0 hNl hg0 hg4, ?_⟩
  set X := (Rads.card : ℝ) * (16 * (4 * R.lam 3) ^ (2 - 1 / M₈) / R.lam 0 ^ 2 *
    ε ^ (-(2 * R.ν + 1 / M₈))) + 1 with hX
  have hX1 : 1 ≤ X := by
    have : 0 ≤ (Rads.card : ℝ) * (16 * (4 * R.lam 3) ^ (2 - 1 / M₈) / R.lam 0 ^ 2 *
        ε ^ (-(2 * R.ν + 1 / M₈))) :=
      mul_nonneg hN0 (mul_nonneg hc₁ (Real.rpow_nonneg hε0.le _))
    rw [hX]; linarith
  have h1 : (Λ * X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have h2 : 0 ≤ g / X := div_nonneg hg0 (by linarith)
  linarith

end LQGMetric.GM
