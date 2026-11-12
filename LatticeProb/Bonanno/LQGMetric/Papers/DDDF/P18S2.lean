/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18S2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2Indep
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Conv
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWUncond

/-!
# DDDF Prop 18, Step 1 (percolation) and Prop 18 (task P2-DDDF18P)

DDDF (arXiv:1904.08021, `tightness.tex` l. 900–910, proof of Prop 18 = `eq:UpperTailsPhi`,
Step 1): sites of `ℤ²` (the unit squares of `[1, 3k−1] × [1, k−1]`), a site being open when each
of the four `3 × 1` rectangles around it has `ψ`-crossing length `≤ ℓ̄^{(n)}_{3,1}(ψ, p'')`.
* `P(site closed) ≤ 4p''` (`prob_siteBad_le`, `prob_gt_ellBarQ`; law invariance under rigid
  motions, `map_psiMN_motion`);
* sites at `ℓ^∞`-distance `> 4` are independent (`prob_iInter_sbox`), so the Peierls bound
  `perc_peierls` (with `r = 4`, `θ = 1/16`) gives
  `P(no left–right open path) ≤ (3k−2) 2^{-(k−2)}`;
* on a left–right open path, `L^{(n)}_{3k,k}(ψ) ≤ 32 k² ℓ̄_{3,1}(ψ, p'')`
  (`rectLen_le_of_percGoodLR`);
* RSW (`psi_rsw_high_quantile'`, DDDF Prop 10 / Cor 13 for `ψ`) with `(1,1) → (3,1)`,
  `p'' = 3p^{1/C}`: `ℓ̄_{3,1}(ψ, p'') ≤ K_p ℓ̄_{1,1}(ψ, p)`.
This proves `P18Step1Psi` (`dddf_p18_step1_psi`), hence **DDDF Prop 18** (`dddf_prop18`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- the Peierls tail `(3k−2) 2^{-(k−2)} ≤ (24 / log 2) e^{-(log 2 / 2) k}` -/
lemma p18_perc_tail (k : ℕ) (hk : 3 ≤ k) :
    ((3 * k - 2 : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ (k - 2) ≤
      24 / Real.log 2 * Real.exp (-(Real.log 2 / 2 * k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : 3 * (m + 3) - 2 = 3 * m + 7 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2]
  set x : ℝ := Real.log 2 / 2 * ((m + 3 : ℕ) : ℝ)
  have hE : 0 < Real.exp x := Real.exp_pos x
  have hx : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hE2 : Real.exp x ^ 2 = 2 ^ (m + 3) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * x = ((m + 3 : ℕ) : ℝ) * Real.log 2 by
      simp only [x]; push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have e3 : (2⁻¹ : ℝ) ^ (m + 1) = 4 / Real.exp x ^ 2 := by
    rw [hE2, inv_pow, show (2 : ℝ) ^ (m + 3) = 2 ^ (m + 1) * 2 ^ 2 by rw [← pow_add]]
    field_simp; norm_num
  have hlin : ((3 * m + 7 : ℕ) : ℝ) * Real.log 2 ≤ 6 * Real.exp x := by
    have : ((3 * m + 7 : ℕ) : ℝ) * Real.log 2 ≤ 6 * x := by
      simp only [x]; push_cast; nlinarith
    linarith
  rw [e3, Real.exp_neg]
  rw [show ((3 * m + 7 : ℕ) : ℝ) * (4 / Real.exp x ^ 2) =
      4 * (((3 * m + 7 : ℕ) : ℝ) * Real.log 2) / (Real.log 2 * Real.exp x ^ 2) by
    field_simp]
  calc 4 * (((3 * m + 7 : ℕ) : ℝ) * Real.log 2) / (Real.log 2 * Real.exp x ^ 2) ≤
      4 * (6 * Real.exp x) / (Real.log 2 * Real.exp x ^ 2) := by gcongr
    _ = 24 / Real.log 2 * (Real.exp x)⁻¹ := by field_simp; ring

/-- **DDDF Prop 18, Step 1 for `ψ`** (display after l. 905). -/
theorem dddf_p18_step1_psi {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    P18Step1Psi ξ W P := by
  have := hW.isProbabilityMeasure
  set Q := psiQ₀
  obtain ⟨CR, hCR, hrsw⟩ := psi_rsw_high_quantile' hW hξ Q (A := 1 / 2) (B := 4)
    (by norm_num) (by norm_num)
  set θr : ℝ := (1 / 16 : ℝ) ^ 25 / 12
  have hθr : 0 < θr := by positivity
  refine ⟨min (1 / 4) (θr ^ CR), lt_min (by norm_num) (Real.rpow_pos_of_pos hθr _),
    fun p hp hpp => ?_⟩
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_left _ _)
  set p'' : ℝ := 3 * p ^ (1 / CR)
  have hp''0 : 0 < p'' := by have := Real.rpow_pos_of_pos hp (1 / CR); positivity
  have hp''θ : p'' ≤ 3 * θr := by
    have h : p ^ (1 / CR) ≤ θr :=
      calc p ^ (1 / CR) ≤ (θr ^ CR) ^ (1 / CR) := Real.rpow_le_rpow hp.le
            (hpp.trans (min_le_right _ _)) (by positivity)
        _ = θr := by rw [one_div, Real.rpow_rpow_inv hθr.le hCR.ne']
    show 3 * p ^ (1 / CR) ≤ 3 * θr
    linarith
  have hp''1 : p'' < 1 := by
    have : 3 * θr < 1 := by norm_num [θr]
    linarith
  have h4p : 4 * p'' ≤ (1 / 16 : ℝ) ^ 25 := by
    calc 4 * p'' ≤ 4 * (3 * θr) := mul_le_mul_of_nonneg_left hp''θ (by norm_num)
      _ = (1 / 16 : ℝ) ^ 25 := by simp only [θr]; ring
  set Kp : ℝ := CR * Real.exp (CR * Real.sqrt |Real.log (p / CR)|)
  have hKp : 0 < Kp := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 / 2
  set C : ℝ := max (64 * Kp) (24 / Real.log 2)
  have hC24 : 24 / Real.log 2 ≤ C := le_max_right _ _
  have hC64 : 64 * Kp ≤ C := le_max_left _ _
  refine ⟨C, c, lt_of_lt_of_le (by positivity) hC24, by positivity, fun n k hk => ?_⟩
  set f := psiMN Q W P 0 n
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  set ℓ := ellBarQ ξ P f (rectAB 3 1) (ENNReal.ofReal p'')
  set ℓ1 := ellBarQ ξ P f (rectAB 1 1) (ENNReal.ofReal p)
  have hrs : ℓ ≤ Kp * ℓ1 := by
    have h := hrsw 1 1 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) n p hp
      (by linarith) hp''1
    calc ℓ ≤ CR * ℓ1 * Real.exp (CR * Real.sqrt |Real.log (p / CR)|) := h
      _ = Kp * ℓ1 := by simp only [Kp]; ring
  have hq0 : 0 < ENNReal.ofReal p'' := ENNReal.ofReal_pos.2 hp''0
  have hq1 : ENNReal.ofReal p'' < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hp''1
  have hℓ0 : 0 ≤ ℓ := ellQ_nonneg hψ.cont hψ.meas _ (tsub_pos_of_lt hq1)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne')
  by_cases hk3 : k < 3
  · calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
      _ ≤ ENNReal.ofReal (C * Real.exp (-(c * k))) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have h1 := Real.add_one_le_exp (-(c * k))
        have hc : c * k ≤ Real.log 2 := by simp only [c]; nlinarith
        have hl2 := Real.log_two_lt_d9
        have h24 : 24 ≤ 24 / Real.log 2 := by
          rw [le_div_iff₀ hl]; norm_num at hl2 ⊢; linarith
        have hE : (3 / 10 : ℝ) ≤ Real.exp (-(c * k)) := by norm_num at hl2; linarith
        nlinarith [mul_le_mul (h24.trans hC24) hE (by norm_num) (by positivity)]
  push_neg at hk3
  set B : ℤ × ℤ → Set Ω := fun x => siteBad (ξ := ξ) f ℓ (sh x)
  have hθ : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 16) ≤ 2⁻¹ := by
    rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    apply ENNReal.ofReal_le_ofReal; norm_num
  have hεθ : ENNReal.ofReal (4 * p'') ≤ ENNReal.ofReal (1 / 16) ^ ((4 + 1) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by norm_num at h4p ⊢; linarith)
  have hper := perc_peierls P (3 * k - 2) (k - 2) (by omega) (by omega) B 4 hθ hεθ
    (fun x _ => by
      refine (prob_siteBad_le hW Q n ℓ (sh x)).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      exact prob_gt_ellBarQ hψ.cont hψ.meas _ hq0 hq1)
    (fun F _ hF => by
      choose T hT hTe using fun x => siteBad_eq_preimage (ξ := ξ) hψ.cont ℓ x
      have e : ∀ x, B x = {ω | (fun y => psiMN Q W P 0 n (sbox x y) ω) ∈ T x} := hTe
      simp only [e]
      exact (prob_iInter_sbox hW Q psiSmall_psiQ₀ n T hT F hF).le)
  have hsub : {ω | C * k ^ 2 * ℓ1 ≤ lenObs ξ f (rectAB (3 * k) k) ω} ⊆
      {ω | ¬ PercGoodLR ((3 * k - 2 : ℕ) : ℤ) ((k - 2 : ℕ) : ℤ) (fun x => ω ∉ B x)} := by
    intro ω hω hLR
    have eK : ((3 * k - 2 : ℕ) : ℤ) = 3 * (k : ℤ) - 2 := by omega
    have eL : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
    rw [eK, eL] at hLR
    have conv : ∀ R : MarkedRect, 0 ≤ R.w → 0 ≤ R.h → lenObs ξ f R ω ≤ ℓ →
        rectLen ξ (fun x => f x ω) R ≤ ENNReal.ofReal ℓ := fun R hw hh h => by
      rw [← ofReal_lenObs hψ.cont R hw hh ω]; exact ENNReal.ofReal_le_ofReal h
    have hR := rectLen_le_of_percGoodLR (ξ := ξ) (g := fun x => f x ω) (k := k)
      ENNReal.ofReal_ne_top (good := fun x => ω ∉ B x) (fun x hx _ => by
        simp only [B, siteBad, mem_union, mem_ofPred_eq, not_or, not_lt] at hx
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
        exact ⟨conv _ (by norm_num [sB]) (by norm_num [sB]) h1,
          conv _ (by norm_num [sT]) (by norm_num [sT]) h2,
          conv _ (by norm_num [sL]) (by norm_num [sL]) h3,
          conv _ (by norm_num [sR]) (by norm_num [sR]) h4⟩) hLR
    have e : (2 * ((3 * k * k : ℕ) : ℝ≥0∞) + 2) * (4 * ENNReal.ofReal ℓ) =
        ENNReal.ofReal (((8 * (3 * k * k) + 8 : ℕ) : ℝ) * ℓ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]; push_cast; ring
    rw [e] at hR
    have hL : lenObs ξ f (rectAB (3 * k) k) ω ≤ ((8 * (3 * k * k) + 8 : ℕ) : ℝ) * ℓ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hR
    have hpos : 0 < lenObs ξ f (rectAB (3 * k) k) ω :=
      lenObs_pos hψ.cont _ (by simp [rectAB]) (by simp [rectAB])
        (by simp [MarkedRect.crossWidth, rectAB]; omega) ω
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hN : ((8 * (3 * k * k) + 8 : ℕ) : ℝ) ≤ 32 * (k : ℝ) ^ 2 := by push_cast; nlinarith
    have h32 : lenObs ξ f (rectAB (3 * k) k) ω ≤ 32 * (k : ℝ) ^ 2 * (Kp * ℓ1) :=
      hL.trans ((mul_le_mul_of_nonneg_right hN hℓ0).trans
        (mul_le_mul_of_nonneg_left hrs (by positivity)))
    have hℓ1 : 0 < ℓ1 := by
      by_contra h
      push_neg at h
      have : 32 * (k : ℝ) ^ 2 * (Kp * ℓ1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos hKp.le h)
      linarith
    have hkl : 0 < (k : ℝ) ^ 2 * ℓ1 := by positivity
    have h64 : 64 * Kp * ((k : ℝ) ^ 2 * ℓ1) ≤ C * ((k : ℝ) ^ 2 * ℓ1) :=
      mul_le_mul_of_nonneg_right hC64 hkl.le
    have hω' : C * (k : ℝ) ^ 2 * ℓ1 ≤ lenObs ξ f (rectAB (3 * k) k) ω := hω
    nlinarith [mul_pos hKp hkl]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := hper
    _ ≤ ((3 * k - 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ (k - 2) := by gcongr
    _ = ENNReal.ofReal (((3 * k - 2 : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ (k - 2)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(c * k))) :=
      ENNReal.ofReal_le_ofReal ((p18_perc_tail k hk3).trans
        (mul_le_mul_of_nonneg_right hC24 (Real.exp_pos _).le))

/-- **DDDF Prop 18** (`eq:UpperTailsPhi`, `tightness.tex` l. 892–945):
`P(L^{(n)}_{3,1}(φ) ≥ e^s Λ_n(p) ℓ_n(p)) ≤ C e^{-c s² / log s}` for `s > 2`, `p` small. -/
theorem dddf_prop18 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) :=
  dddf_prop18_of_step1 hW hξ (p18_step1_of_psi hW hξ (dddf_p18_step1_psi hW hξ))

end DDDF
end LQGMetric
