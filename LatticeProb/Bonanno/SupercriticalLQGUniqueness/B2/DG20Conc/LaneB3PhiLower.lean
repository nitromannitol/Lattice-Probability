/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PhiLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Pathwise
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Arith
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBUnitSquareTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBObigGaussian
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFineShortFiniteTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1QuantileStep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBProbabilityTransfer
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

 










set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise
open LQGMetric.DDDF.T20C LQGMetric.DDDF.T20D

universe u

 



theorem laneB3_phi_lower_tail (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {p : ℝ} (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (hunit : LaneA2HasUnitTails.{u} (ξ : ℝ) p)
    (ζ : ℝ) (hζ : 0 < ζ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A a T₀ : ℝ, ∃ K₀ : ℕ, 0 < A ∧ 0 < a ∧ 1 < T₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ K n : ℕ, K₀ ≤ K → K < n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ T : ℝ, T₀ ≤ T →
        P {ω | lenObs (ξ : ℝ) (phiMN W P 0 n) (rectAB 1 1) ω <
          T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
            lambdaN (ξ : ℝ) W P (n - K)} ≤
          ENNReal.ofReal (A * 4 ^ K * Real.exp (-a * (Real.log T) ^ 2)) := by
  obtain ⟨Cneg, cNeg, Cpos, cPos, hCn, hcn, hCp, hcp, hU⟩ := hunit
  obtain ⟨pa, ca, Ca, Cna, cna, Cpa, cpa, hpa, hpaH, hca, hCa, hCna, hcna, hCpa, hcpa,
    hapr⟩ := laneB_apriori_unit_square_power_tails ξ Q hQ (ζ / 2) (by linarith)
  obtain ⟨CO, σ2, hCO, hσ2, hObig⟩ := laneB_Obig_gaussian_tail
  obtain ⟨K₁, hK₁⟩ := laneB3_sqrt_absorb C ζ hC hζ
  have hξ : (0 : ℝ) < ξ := ξ.2
  set C₁ : ℝ := 164 + 6 * (ξ : ℝ) with hC₁def
  have hC₁ : 0 < C₁ := by positivity
  set y₀ : ℝ := 4 * (Real.log 3 + |Real.log ca| + |Real.log Ca| + |Real.log C₁|) +
    8 * |Real.log ca| + 1 with hy₀
  set a : ℝ := min (1 / (32 * C₁ ^ 2 * σ2)) (min (cNeg / 16) (cna / 64)) with hadef
  have ha : 0 < a := by positivity
  have hy₀1 : 1 ≤ y₀ := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have := abs_nonneg (Real.log ca)
    have := abs_nonneg (Real.log Ca)
    have := abs_nonneg (Real.log C₁)
    rw [hy₀]; linarith
  refine ⟨CO + 36 * Cneg + Cna, a, Real.exp y₀, max K₁ 2, by positivity, ha,
    by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + K := ⟨n - K, by omega⟩
  have hm' : 1 ≤ m' := by omega
  simp only [Nat.add_sub_cancel] at hH ⊢
  have hK2 : 2 ≤ K := le_trans (le_max_right _ _) hK
  have hKK₁ : K₁ ≤ K := le_trans (le_max_left _ _) hK
  
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  set y : ℝ := Real.log T with hydef
  have hTy : T = Real.exp y := (Real.exp_log hTpos).symm
  have hyy₀ : y₀ ≤ y := by rw [hydef, Real.le_log_iff_exp_le hTpos]; exact hT
  set s : ℝ := Real.exp (y / 4) with hsdef
  have hs0 : 0 < s := Real.exp_pos _
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have habs := abs_nonneg (Real.log ca)
  have habs2 := abs_nonneg (Real.log Ca)
  have habs3 := abs_nonneg (Real.log C₁)
  have hy4 : Real.log 3 + |Real.log ca| + |Real.log Ca| + |Real.log C₁| < y / 4 := by
    linarith
  have hs3 : 3 < s := by
    rw [hsdef, ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hcas : 3 < ca * s := by
    rw [hsdef, ← Real.exp_log hca, ← Real.exp_add,
      ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_lt_exp.mpr ?_
    have := neg_abs_le (Real.log ca)
    linarith
  have hsCa : 3 < s / Ca := by
    rw [lt_div_iff₀ hCa, hsdef, ← Real.exp_log hCa,
      ← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    refine Real.exp_lt_exp.mpr ?_
    have := le_abs_self (Real.log Ca)
    linarith
  have hC₁s : C₁ ≤ s := by
    rw [hsdef, ← Real.exp_log hC₁]
    refine Real.exp_le_exp.mpr ?_
    have := le_abs_self (Real.log C₁)
    linarith
  have hsinv : s⁻¹ = Real.exp (-(y / 4)) := by rw [hsdef, Real.exp_neg]
  
  obtain ⟨Y, -, hY, -, hYc, -⟩ := exists_C1_modification_phi hW
    (a := ((2 : ℝ) ^ K)⁻¹) (b := 1) (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hpath := laneB3_lower_pathwise hW hξ (k := K) (n := m') hK2 hm' Y
    (fun x => hY x) hYc
  
  set B : ℝ := Real.exp (C * Real.sqrt (K : ℝ)) with hBdef
  have hB : 0 < B := Real.exp_pos _
  have hsand := j1_quantile_sandwich_of_induction P hW (ξ : ℝ) hp
    (by linarith : p ≤ 1 / 2) hH
  have hell : 0 < ellN (ξ : ℝ) W P m' (ENNReal.ofReal p) := by
    have hv := isPhiVersion_phiMN hW (Nat.zero_le m')
    have hp1 : ENNReal.ofReal p < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
    exact T20.ellQ_pos hv.cont hv.meas (ENNReal.ofReal_pos.mpr hp) hp1
  have hlam0 : 0 < lambdaN (ξ : ℝ) W P m' := lambdaN_pos hW m'
  
  set g : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) with hgdef
  set g' : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (K : ℝ)) with hg'def
  have hg0 : 0 ≤ g := by positivity
  have hBg : B * g ≤ g' := by
    have h1 := hK₁ K hKK₁
    calc B * g ≤ (2 : ℝ) ^ ((ζ / 2) * (K : ℝ)) * g :=
          mul_le_mul_of_nonneg_right h1 hg0
      _ = g' := by
          rw [hgdef, hg'def, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  
  set J' := laneB3ShortFamily K with hJ'
  set E1 : Set Ω := {ω | y / (4 * C₁) ≤ Obig K Y ω} with hE1
  set E2 : Set Ω := {ω | ∃ j ∈ J', T20B.mrectLen (ξ : ℝ)
      (fun z => phiMN W P K (m' + K) z ω) K ((fun j : Circle × ℂ => j.1) j)
        ((fun j : Circle × ℂ => j.2) j) 1 3 <
      s⁻¹ * ellN (ξ : ℝ) W P (m' + K - K) (ENNReal.ofReal p) * (2 : ℝ)⁻¹ ^ K} with hE2
  set E3 : Set Ω := {ω | lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω <
      s⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (K : ℝ))} with hE3
  have hmain := laneB_measure_le_of_ae_good_imp P
    {ω | lenObs (ξ : ℝ) (phiMN W P 0 (m' + K)) (rectAB 1 1) ω <
      T⁻¹ * g * lambdaN (ξ : ℝ) W P m'} ∅ (E1 ∪ E2 ∪ E3) (by
    filter_upwards [hpath] with ω hω hA hbad
    exfalso
    simp only [Set.mem_union, not_or] at hbad
    obtain ⟨⟨h1, h2⟩, h3⟩ := hbad
    simp only [hE1, hE3, Set.mem_ofPred_eq, not_le, not_lt] at h1 h3
    have hO : Obig K Y ω < y / (4 * C₁) := h1
    have hm : Real.exp (-(y / 4)) * ellN (ξ : ℝ) W P m' (ENNReal.ofReal p) *
        (2 : ℝ)⁻¹ ^ K ≤ minShort (ξ : ℝ) W P K (m' + K) J'
          (laneB3ShortFamily_nonempty K) ω := by
      refine Finset.le_inf' _ _ fun j hj => ?_
      by_contra hlt
      push_neg at hlt
      apply h2
      refine ⟨j, hj, ?_⟩
      simp only [Nat.add_sub_cancel]
      rw [hsinv]
      exact hlt
    have hLk : Real.exp (-(y / 4)) * (B * g) ≤
        lenN (ξ : ℝ) W P 1 1 K ω := by
      have := h3
      calc Real.exp (-(y / 4)) * (B * g) ≤ Real.exp (-(y / 4)) * g' :=
            mul_le_mul_of_nonneg_left hBg (Real.exp_pos _).le
        _ = s⁻¹ * g' := by rw [hsinv]
        _ ≤ _ := this
    have hfin := laneB3_lower_arith (C₁ := C₁) (O := Obig K Y ω) (y := y)
      (m := minShort (ξ : ℝ) W P K (m' + K) J' (laneB3ShortFamily_nonempty K) ω)
      (Lk := lenN (ξ : ℝ) W P 1 1 K ω) (Ln := lenN (ξ : ℝ) W P 1 1 (m' + K) ω)
      (ell := ellN (ξ : ℝ) W P m' (ENNReal.ofReal p))
      (lam := lambdaN (ξ : ℝ) W P m') (g := g) (B := B) K hC₁ hO hm hLk hω hsand.1 hB hg0
      hell.le hlam0.le hC₁s
    have hAω : lenN (ξ : ℝ) W P 1 1 (m' + K) ω < T⁻¹ * g * lambdaN (ξ : ℝ) W P m' := hA
    rw [hTy, ← Real.exp_neg] at hAω
    linarith)
  
  have hP1 : P E1 ≤ ENNReal.ofReal (CO * 4 ^ K * Real.exp (-a * y ^ 2)) := by
    have hx0 : 0 ≤ y / (4 * C₁) := div_nonneg (by linarith) (by positivity)
    have h := hObig hW K Y (fun x => hY x) hYc (y / (4 * C₁)) hx0
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal (h.trans ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hae : a ≤ 1 / (32 * C₁ ^ 2 * σ2) := min_le_left _ _
    have hid : -(y / (4 * C₁)) ^ 2 / (2 * σ2) = -(1 / (32 * C₁ ^ 2 * σ2)) * y ^ 2 := by
      field_simp; ring
    rw [hid]
    have := mul_le_mul_of_nonneg_right hae (sq_nonneg y)
    linarith
  have hP2 : P E2 ≤ ENNReal.ofReal (36 * Cneg * 4 ^ K * Real.exp (-a * y ^ 2)) := by
    have h := laneB_fine_short_finite_tail P hW hU K (m' + K) (by omega) J'
      (fun j : Circle × ℂ => j.1) (fun j : Circle × ℂ => j.2) s hs3
    refine h.trans ?_
    have hlogs : Real.log s = y / 4 := by rw [hsdef, Real.log_exp]
    rw [hlogs]
    have hcard := laneB3ShortFamily_card_le K
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hae : a ≤ cNeg / 16 := (min_le_right _ _).trans (min_le_left _ _)
    have he : Real.exp (-cNeg * (y / 4) ^ 2) ≤ Real.exp (-a * y ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right hae (sq_nonneg y)
      have hid : -cNeg * (y / 4) ^ 2 = -(cNeg / 16 * y ^ 2) := by ring
      linarith
    calc ((J'.card : ℕ) : ℝ) * (Cneg * Real.exp (-cNeg * (y / 4) ^ 2))
        ≤ (36 * 4 ^ K) * (Cneg * Real.exp (-a * y ^ 2)) := by
          gcongr
      _ = 36 * Cneg * 4 ^ K * Real.exp (-a * y ^ 2) := by ring
  have hP3 : P E3 ≤ ENNReal.ofReal (Cna * 4 ^ K * Real.exp (-a * y ^ 2)) := by
    have h := (hapr P W hW K s hcas hsCa).1
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hae : a ≤ cna / 64 := (min_le_right _ _).trans (min_le_right _ _)
    have hlog : y / 8 ≤ Real.log (ca * s) := by
      rw [Real.log_mul hca.ne' hs0.ne', hsdef, Real.log_exp]
      have := neg_abs_le (Real.log ca)
      linarith
    have hy8 : 0 ≤ y / 8 := by linarith
    have hsq : (y / 8) ^ 2 ≤ (Real.log (ca * s)) ^ 2 := pow_le_pow_left₀ hy8 hlog 2
    have he : Real.exp (-cna * (Real.log (ca * s)) ^ 2) ≤ Real.exp (-a * y ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 := mul_le_mul_of_nonneg_right hae (sq_nonneg y)
      have h2 := mul_le_mul_of_nonneg_left hsq hcna.le
      have hid : cna * (y / 8) ^ 2 = cna / 64 * y ^ 2 := by ring
      linarith
    have h4 : (1 : ℝ) ≤ 4 ^ K := one_le_pow₀ (by norm_num)
    have h5 : Real.exp (-a * y ^ 2) ≤ 4 ^ K * Real.exp (-a * y ^ 2) :=
      le_mul_of_one_le_left (Real.exp_pos _).le h4
    have h6 := mul_le_mul_of_nonneg_left (he.trans h5) hCna.le
    linarith [mul_assoc Cna (4 ^ K : ℝ) (Real.exp (-a * y ^ 2))]
  refine le_trans hmain ?_
  rw [measure_empty, zero_add]
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add (measure_union_le _ _) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add hP1 hP2) hP3) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_of_eq ?_
  congr 1; ring

end SupercriticalLQGUniqueness.B2.DG20Conc
