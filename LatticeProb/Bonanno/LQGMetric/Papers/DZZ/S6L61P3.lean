/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61P3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61P2

/-!
# DZZ (eq-point-to-boundary-kappa), lower half, for moving centres (P2-DZZ61P)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2593–2596; DEC-117 §2(b):
`DZZL61PtBdry` is true as stated. From the one-scale estimate `ptBdry_key` (S6L61P2) with
`λ` fixed large (depending on `ε`), `t₁ = M log δ⁻¹`, `t₂ = M log δ'⁻¹`, and
`log δ'⁻¹ = log δ⁻¹ − λ + log(1−α)`:

* **`dzzL61PtBdry_dzzMuIn`**: `DZZL61PtBdry P (dzzMuIn γ W) α χ u` for `u ∈ 𝕍̄`, `0 < α < 1`,
  from DZZ Lemma 5.4 (`DZZLem54Exp`, used at the single box `𝕍_{c₀,1/20}`, `c₀ = (1/2,1/2)`).

DZZ use a fixed `λ`-free form "by Lemma 5.4 and a similar derivation"; we take the shift
`e^{±λ}` of lem-scaling-coupling with `λ` fixed (it costs `O(1)` in `log δ⁻¹`), not
`λ = (log δ⁻¹)^{0.6}` as suggested in DEC-117 §2(b) (both work; the fixed one is simpler).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

lemma dzz61p_exp_neg_one_lt_half : Real.exp (-1) < 1 / 2 := by
  have := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith

lemma le_log_inv_of_lt_exp {δ T : ℝ} (hδ : 0 < δ) (h : δ < Real.exp (-T)) :
    T ≤ Real.log δ⁻¹ := by
  rw [Real.log_inv]
  have := Real.log_lt_log hδ h
  rw [Real.log_exp] at this
  linarith

set_option maxHeartbeats 1000000 in
/-- **DZZ (eq-point-to-boundary-kappa), lower half, moving centres** (l. 2593–2596; DEC-117
§2(b)): from DZZ Lemma 5.4 at `μIn`. -/
theorem dzzL61PtBdry_dzzMuIn {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {α χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h54 : DZZLem54Exp P (dzzMuIn γ W) χ) {u : ℂ} (hu : u ∈ dzzVbar) :
    DZZL61PtBdry P (dzzMuIn γ W) α χ u := by
  intro v hv ε hε
  haveI := hW.isProbabilityMeasure
  by_cases hχ : χ ≤ ε
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ.1).mpr hδ.2)
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hL.le).trans
      (integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _)
  push_neg at hχ
  have hr : 0 < 1 - α := by linarith
  obtain ⟨C, a₁, b₁, hC, ha₁, hb₁, hkey⟩ := ptBdry_key hW hγ hγ2 hα0 hα1 hu
  set Bm := a₁ + b₁ + 1 with hBm
  have hBm0 : 0 < Bm := by linarith
  set M := 16 * Bm / ε with hMdef
  have hM : 0 < M := by positivity
  have hMε : ε / 16 * M = Bm := by rw [hMdef]; field_simp
  set η := ε / (16 * M) with hηdef
  have hη : 0 < η := by positivity
  have hηM : M * η = ε / 16 := by rw [hηdef]; field_simp
  -- the coupling parameter `λ`
  have hlamT : Tendsto (fun lam : ℝ => C * Real.exp (-lam ^ 2 / C)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun lam : ℝ => lam ^ 2 / C) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const hC
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    simpa [Function.comp_def, neg_div] using h2
  obtain ⟨lam, hlam0, hlamη⟩ :=
    ((eventually_ge_atTop 0).and ((tendsto_order.1 hlamT).2 η hη)).exists
  set c₀ := lam - Real.log (1 - α) with hc₀def
  have hc₀ : 0 ≤ c₀ := by
    have := Real.log_nonpos hr.le (by linarith); linarith
  -- the scale `δ' = δ e^{λ}/(1−α)` of the fixed box
  have hφ : Tendsto (fun δ : ℝ => δ * Real.exp lam / (1 - α)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Continuous fun δ : ℝ => δ * Real.exp lam / (1 - α) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos (mul_pos hδ (Real.exp_pos _)) hr
  have hev1 := (tendsto_order.1 ((h54 ptCentre ptCentre_mem_dzzVbar).comp hφ)).1 (χ - ε / 4)
    (by linarith)
  have hBig : Tendsto (fun δ => P.real {ω | ¬ BigBallsAt (dzzMuIn γ W ω) ((1 - α) / 20 / 4) δ})
      (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (dzzBigBalls_dzzMuIn hW hγ hγ2 (r := (1 - α) / 20 / 4) (by positivity))
    exact h
  have hev2 := (tendsto_order.1 hBig).2 η hη
  set T := 4 * χ * c₀ / ε with hTdef
  have hδ₀ : 0 < min (Real.exp (-1)) (min ((1 - α) * Real.exp (-1) / Real.exp lam)
      (Real.exp (-T))) := lt_min (Real.exp_pos _) (lt_min (by positivity) (Real.exp_pos _))
  filter_upwards [hev1, hev2, Ioo_mem_nhdsGT hδ₀] with δ h1 h2 h3
  obtain ⟨hδ, hδ₀'⟩ := h3
  have hδe : δ < Real.exp (-1) := hδ₀'.trans_le (min_le_left _ _)
  have hδe' : δ < (1 - α) * Real.exp (-1) / Real.exp lam :=
    hδ₀'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδT : δ < Real.exp (-T) := hδ₀'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set δ' := δ * Real.exp lam / (1 - α) with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'e : δ' < Real.exp (-1) := by
    rw [hδ'def, div_lt_iff₀ hr]
    rw [lt_div_iff₀ (Real.exp_pos _)] at hδe'
    linarith
  set L := Real.log δ⁻¹ with hLdef
  set L' := Real.log δ'⁻¹ with hL'def
  have hL1 : 1 ≤ L := le_log_inv_of_lt_exp hδ hδe
  have hL'1 : 1 ≤ L' := le_log_inv_of_lt_exp hδ'pos hδ'e
  have hLL' : L' = L - c₀ := by
    rw [hL'def, hLdef, hδ'def, Real.log_inv, Real.log_inv, Real.log_div (by positivity) hr.ne',
      Real.log_mul hδ.ne' (Real.exp_pos _).ne', Real.log_exp, hc₀def]
    ring
  have hLT : T ≤ L := le_log_inv_of_lt_exp hδ hδT
  have hδ2 : δ ≤ 1 / 2 := (hδe.trans dzz61p_exp_neg_one_lt_half).le
  have hδ'2 : δ' ≤ 1 / 2 := (hδ'e.trans dzz61p_exp_neg_one_lt_half).le
  have key := hkey (v δ) (hv δ) δ lam (M * L) (M * L') hδ hδ2 hlam0 hδ'2 (by positivity)
    (by positivity)
  simp only [Function.comp_apply] at h1
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < L')] at h1
  -- the error terms are each `≤ ε L / 16`
  have hL'L : L' ≤ L := by linarith
  have e1 : (a₁ + b₁ * L' ^ 2) / (M * L') ≤ ε / 16 * L := by
    rw [div_le_iff₀ (by positivity)]
    have : a₁ + b₁ * L' ^ 2 ≤ Bm * L' ^ 2 := by
      have hsq : 1 ≤ L' ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left hsq ha₁
      rw [hBm]; nlinarith
    have : L' ^ 2 ≤ L * L' := by nlinarith
    nlinarith
  have e2 : (a₁ + b₁ * L ^ 2) / (M * L) ≤ ε / 16 * L := by
    rw [div_le_iff₀ (by positivity)]
    have : a₁ + b₁ * L ^ 2 ≤ Bm * L ^ 2 := by
      have hsq : 1 ≤ L ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left hsq ha₁
      rw [hBm]; nlinarith
    nlinarith
  have e3 : M * L' * (C * Real.exp (-lam ^ 2 / C)) ≤ ε / 16 * L := by
    have : M * L' * (C * Real.exp (-lam ^ 2 / C)) ≤ M * L' * η :=
      mul_le_mul_of_nonneg_left hlamη.le (by positivity)
    nlinarith
  have e4 : M * L * P.real {ω | ¬ BigBallsAt (dzzMuIn γ W ω) ((1 - α) / 20 / 4) δ} ≤
      ε / 16 * L := by
    have : M * L * P.real {ω | ¬ BigBallsAt (dzzMuIn γ W ω) ((1 - α) / 20 / 4) δ} ≤
        M * L * η := mul_le_mul_of_nonneg_left h2.le (by positivity)
    nlinarith
  have hprod : (χ - ε / 4) * L' = (χ - ε / 4) * L - (χ - ε / 4) * c₀ := by rw [hLL']; ring
  have hc0χ : (χ - ε / 4) * c₀ ≤ χ * c₀ := by nlinarith
  have hTc : χ * c₀ ≤ ε / 4 * L := by
    have : χ * c₀ = ε / 4 * T := by rw [hTdef]; field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hLT (by positivity)
  have hYge : (χ - ε / 4) * L' ≤ ∫ ω, logMinLGD (dzzWall (sqBox ptCentre (1 / 10))
      (dzzMuIn γ W ω)) δ' {ptCentre} (frontier (sqBox ptCentre (1 / 20))) ∂P := h1.le
  nlinarith

end DZZ
end LQGMetric
