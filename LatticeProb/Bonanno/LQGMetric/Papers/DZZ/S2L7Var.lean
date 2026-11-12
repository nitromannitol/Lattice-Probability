/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7Var at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5

/-!
# DZZ (eq-variance-truncation) (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 2.7, l. 553–559:
with `Δ_i(v) = h̃_{2^{-i}}^{2^{-i+1}}(v) − η_{2^{-i}}^{2^{-i+1}}(v)` (`i ≥ 1`) and
`Δ_0(v) = h̃_1(v) − η_1(v)`, "uniformly in `v ∈ 𝕍` and `i`, `Var Δ_i(v) = O(1) P(τ_i ≤ 2^{-2i}) =
O(1) e^{−Ω(i²)}`".

`dzz_variance_truncation` proves `Var Δ_i(v) ≤ K ρ^i` with `ρ < 1` (geometric decay, which is all
`dzz_sum_sup_tail` uses; DZZ's `e^{−Ω(i²)}` is stronger and not needed downstream), for all
`v ∈ ℂ`. Steps: `variance_wnField_sub_etaField_le` (S2L7Trunc), the bridge exit bound
`killedHeat_sub_inter_ball_le`, and `r(s)²/s ≥ κ i` on the band `(4^{-(i+1)}, 4^{-i})`
(`etaRad_band`), then `∫_a^b (2πs)⁻¹ ds = log(b/a)/(2π)`. For `Δ_0` the bound is
`Var ≤ π ∫_1^∞ p_𝕍(s; v, v) ds ≤ 4` (`killedHeat_le_rpow`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- The constant `κ = min((log 4)²/16, 1/100)` in `r(s)²/s ≥ κ i`. -/
def kappaBand : ℝ := min (Real.log 4 ^ 2 / 16) (1 / 100)

lemma kappaBand_pos : 0 < kappaBand := by
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold kappaBand; positivity

/-- On the band `s ∈ (4^{-(i+1)}, 4^{-i})`: `r(s) > 0` and `r(s)²/s ≥ κ i`. -/
lemma etaRad_band (i : ℕ) {s : ℝ} (hs : s ∈ Ioo ((1 / 4 : ℝ) ^ (i + 1)) ((1 / 4 : ℝ) ^ i)) :
    0 < etaRad s ∧ kappaBand * i ≤ etaRad s ^ 2 / s := by
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := lt_trans (by positivity) hs1
  have hs1' : s < 1 := hs2.trans_le (pow_le_one₀ (by norm_num) (by norm_num))
  have hL0 : 0 < Real.log s⁻¹ := Real.log_pos (one_lt_inv₀ hs0 |>.mpr hs1')
  have hL : (i : ℝ) * Real.log 4 ≤ Real.log s⁻¹ := by
    rw [← Real.log_pow]
    refine Real.log_le_log (by positivity) ?_
    have : (4 : ℝ) ^ i = ((1 / 4 : ℝ) ^ i)⁻¹ := by rw [one_div, inv_pow, inv_inv]
    rw [this]
    exact inv_anti₀ hs0 hs2.le
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hi : (i : ℝ) ≤ (i : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ i := by exact_mod_cast h
      nlinarith
  have hi4 : (i : ℝ) ≤ 4 ^ i := by
    have h1 : (i : ℝ) < 2 ^ i := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ i ≤ 4 ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
    linarith
  have habs : |Real.log s⁻¹| = Real.log s⁻¹ := abs_of_pos hL0
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hpos : 0 < Real.sqrt s * |Real.log s⁻¹| / 4 := by
    rw [habs]; have := Real.sqrt_pos.mpr hs0; positivity
  refine ⟨lt_min hpos (by norm_num), ?_⟩
  unfold etaRad
  rcases le_total (Real.sqrt s * |Real.log s⁻¹| / 4) (1 / 10) with h | h
  · rw [min_eq_left h, habs, div_pow, mul_pow, hsq]
    have e : s * Real.log s⁻¹ ^ 2 / 4 ^ 2 / s = Real.log s⁻¹ ^ 2 / 16 := by
      field_simp; norm_num
    rw [e]
    have h1 : kappaBand ≤ Real.log 4 ^ 2 / 16 := min_le_left _ _
    have h2 : (i : ℝ) * Real.log 4 ^ 2 ≤ Real.log s⁻¹ ^ 2 := by
      have : ((i : ℝ) * Real.log 4) ^ 2 ≤ Real.log s⁻¹ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hL 2
      nlinarith [sq_nonneg (Real.log 4)]
    have hk0 := kappaBand_pos.le
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    calc kappaBand * i ≤ Real.log 4 ^ 2 / 16 * i := mul_le_mul_of_nonneg_right h1 hi0
      _ ≤ Real.log s⁻¹ ^ 2 / 16 := by nlinarith
  · rw [min_eq_right h]
    have h1 : kappaBand ≤ 1 / 100 := min_le_right _ _
    have hs4 : (4 : ℝ) ^ i ≤ s⁻¹ := by
      have : (4 : ℝ) ^ i = ((1 / 4 : ℝ) ^ i)⁻¹ := by rw [one_div, inv_pow, inv_inv]
      rw [this]; exact inv_anti₀ hs0 hs2.le
    have e : (1 / 10 : ℝ) ^ 2 / s = s⁻¹ / 100 := by field_simp; norm_num
    rw [e]
    have hk0 := kappaBand_pos.le
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    calc kappaBand * i ≤ 1 / 100 * i := mul_le_mul_of_nonneg_right h1 hi0
      _ ≤ s⁻¹ / 100 := by linarith

/-- Integrated truncation bound on a band `(a, b)` where `2(r(s)/3)²/s ≥ m`:
`π ∫_a^b (p_𝕍(s; v, v) − p_{𝕍 ∩ B(v, r(s))}(s; v, v)) ds ≤ 2 e^{−m} log(b/a)`. -/
theorem pi_integral_trunc_le {a b m : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ s ∈ Ioo a b, 0 < etaRad s) (hm : ∀ s ∈ Ioo a b, m ≤ 2 * (etaRad s / 3) ^ 2 / s)
    (v : ℂ) :
    Real.pi * ((∫ s in Ioo a b, killedHeat openSquare s.toNNReal v v) -
      ∫ s in Ioo a b, killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v) ≤
      2 * Real.exp (-m) * Real.log (b / a) := by
  have hI0 : Ioo a b ⊆ Ioi a := Ioo_subset_Ioi_self
  have hiu := integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare
    (by norm_num : (0 : ℝ) ≤ 2) openSquare_subset_ball ha hI0 v v
  have hie : IntegrableOn (fun s : ℝ =>
      killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v) (Ioo a b) :=
    Integrable.mono' hiu (measurable_killedHeat_eta_time v).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
        exact killedHeat_mono inter_subset_left _ _ _)
  have hinv : IntegrableOn (fun s : ℝ => s⁻¹) (Ioo a b) :=
    ((continuousOn_inv₀.mono fun x hx => mem_compl_singleton_iff.mpr
      (ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← integral_sub hiu hie, ← integral_const_mul]
  calc ∫ s in Ioo a b, Real.pi * (killedHeat openSquare s.toNNReal v v -
        killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v)
      ≤ ∫ s in Ioo a b, 2 * Real.exp (-m) * s⁻¹ := by
        refine setIntegral_mono_on ((hiu.sub hie).const_mul _) (hinv.const_mul _)
          measurableSet_Ioo fun s hs => ?_
        have hs0 : 0 < s := ha.trans hs.1
        have htn : s.toNNReal ≠ 0 := by simpa using hs0
        have hc : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0.le
        have h := killedHeat_sub_inter_ball_le htn openSquare v (hr s hs)
        rw [hc] at h
        have he : Real.exp (-(2 * (etaRad s / 3) ^ 2 / s)) ≤ Real.exp (-m) :=
          Real.exp_le_exp.mpr (neg_le_neg (hm s hs))
        have h2 : killedHeat openSquare s.toNNReal v v -
            killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v ≤
            (2 * Real.pi * s)⁻¹ * (4 * Real.exp (-m)) :=
          h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        calc Real.pi * (killedHeat openSquare s.toNNReal v v -
              killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v)
            ≤ Real.pi * ((2 * Real.pi * s)⁻¹ * (4 * Real.exp (-m))) :=
              mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
          _ = 2 * Real.exp (-m) * s⁻¹ := by
              have := Real.pi_pos
              field_simp
              ring
    _ = 2 * Real.exp (-m) * Real.log (b / a) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DZZ's `Δ_i(v)` (proof of Lemma 2.7, l. 553): `Δ_0 = h̃_1 − η_1`,
`Δ_i = h̃_{2^{-i}}^{2^{-i+1}} − η_{2^{-i}}^{2^{-i+1}}` for `i ≥ 1`. -/
def dzzDelta (W : WNSpace → Ω → ℝ) (i : ℕ) (v : ℂ) (ω : Ω) : ℝ :=
  if i = 0 then tildeHInf W 1 v ω - etaInf W 1 v ω
  else tildeH W ((1 / 2 : ℝ) ^ i) ((1 / 2 : ℝ) ^ (i - 1)) v ω -
    eta W ((1 / 2 : ℝ) ^ i) ((1 / 2 : ℝ) ^ (i - 1)) v ω

lemma variance_dzzDelta_zero_le (hW : IsWhiteNoise P W) (v : ℂ) :
    Var[dzzDelta W 0 v; P] ≤ 4 := by
  have e : dzzDelta W 0 v = fun ω => wnField W openSquare (Ioi 1) v ω - etaField W (Ioi 1) v ω := by
    funext ω; simp [dzzDelta, tildeHInf, etaInf]
  rw [e]
  refine (variance_wnField_sub_etaField_le hW measurableSet_Ioi one_pos subset_rfl v).trans ?_
  have hiu := integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare
    (by norm_num : (0 : ℝ) ≤ 2) openSquare_subset_ball one_pos subset_rfl v v
  have h0 : 0 ≤ ∫ s in Ioi (1 : ℝ),
      killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v :=
    setIntegral_nonneg measurableSet_Ioi fun s _ => killedHeat_nonneg _ _ _ _
  have hpow : IntegrableOn (fun s : ℝ => 2 ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  have h1 : ∫ s in Ioi (1 : ℝ), killedHeat openSquare s.toNNReal v v ≤ 4 / Real.pi := by
    calc ∫ s in Ioi (1 : ℝ), killedHeat openSquare s.toNNReal v v
        ≤ ∫ s in Ioi (1 : ℝ), 2 ^ 2 / Real.pi * s ^ (-2 : ℝ) :=
          setIntegral_mono_on hiu hpow measurableSet_Ioi fun s hs =>
            killedHeat_le_rpow (by norm_num) openSquare_subset_ball (one_pos.trans hs) v v
      _ = 4 / Real.pi := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
          norm_num
  have := Real.pi_pos
  calc Real.pi * ((∫ s in Ioi (1 : ℝ), killedHeat openSquare s.toNNReal v v) -
        ∫ s in Ioi (1 : ℝ), killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v)
      ≤ Real.pi * (4 / Real.pi) := mul_le_mul_of_nonneg_left (by linarith) this.le
    _ = 4 := by field_simp

lemma variance_dzzDelta_succ_le (hW : IsWhiteNoise P W) (j : ℕ) (v : ℂ) :
    Var[dzzDelta W (j + 1) v; P] ≤
      2 * Real.exp (-(2 / 9 * kappaBand * j)) * Real.log 4 := by
  set I := Ioo ((1 / 4 : ℝ) ^ (j + 1)) ((1 / 4 : ℝ) ^ j)
  have e : dzzDelta W (j + 1) v = fun ω => wnField W openSquare I v ω - etaField W I v ω := by
    funext ω
    simp only [dzzDelta, Nat.add_one_ne_zero, if_false, tildeH, eta, Nat.add_sub_cancel, I]
    rw [← pow_mul, ← pow_mul, mul_comm (j + 1), mul_comm j, pow_mul, pow_mul]
    norm_num
  rw [e]
  have ha : (0 : ℝ) < (1 / 4) ^ (j + 1) := by positivity
  have hab : (1 / 4 : ℝ) ^ (j + 1) ≤ (1 / 4) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)
  refine (variance_wnField_sub_etaField_le hW measurableSet_Ioo ha Ioo_subset_Ioi_self v).trans ?_
  have hlog : Real.log ((1 / 4 : ℝ) ^ j / (1 / 4) ^ (j + 1)) = Real.log 4 := by
    rw [pow_succ, div_mul_cancel_left₀ (by positivity)]
    norm_num
  rw [← hlog]
  refine pi_integral_trunc_le ha hab (fun s hs => (etaRad_band j hs).1) (fun s hs => ?_) v
  have h := (etaRad_band j hs).2
  have hs0 : 0 < s := ha.trans hs.1
  have e2 : 2 * (etaRad s / 3) ^ 2 / s = 2 / 9 * (etaRad s ^ 2 / s) := by ring
  rw [e2]
  nlinarith

/-- **DZZ (eq-variance-truncation)** (l. 556–559), geometric form: `Var Δ_i(v) ≤ K ρ^i` for all
`i ∈ ℕ`, `v ∈ ℂ`, with `K > 0`, `ρ ∈ (0, 1)` absolute constants. -/
theorem dzz_variance_truncation :
    ∃ K ρ : ℝ, 0 < K ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ (i : ℕ) (v : ℂ),
        Var[dzzDelta W i v; P] ≤ K * ρ ^ i := by
  set ρ := Real.exp (-(2 / 9 * kappaBand)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by have := kappaBand_pos; linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨max 4 (2 * Real.log 4 / ρ), ρ, by positivity, hρ0, hρ1, ?_⟩
  intro Ω _ P W hW i v
  rcases i with _ | j
  · simpa using (variance_dzzDelta_zero_le hW v).trans (le_max_left _ _)
  · refine (variance_dzzDelta_succ_le hW j v).trans ?_
    have e : Real.exp (-(2 / 9 * kappaBand * j)) = ρ ^ j := by
      rw [hρ, ← Real.exp_nat_mul]; ring_nf
    rw [e]
    calc 2 * ρ ^ j * Real.log 4 = 2 * Real.log 4 / ρ * ρ ^ (j + 1) := by
          field_simp; ring
      _ ≤ max 4 (2 * Real.log 4 / ρ) * ρ ^ (j + 1) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end DZZ
end LQGMetric
