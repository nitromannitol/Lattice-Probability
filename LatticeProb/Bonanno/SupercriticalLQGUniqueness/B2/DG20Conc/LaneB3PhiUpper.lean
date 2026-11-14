/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PhiUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PhiLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFineLongFiniteTail

 









set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise
open LQGMetric.DDDF.T20C LQGMetric.DDDF.T20D

universe u

 

theorem laneB3_double_sum_le {ι κ : Type*} (I : Finset ι) (circ : ι → Finset κ)
    (V : ι → ℝ) (f : κ → ℝ) {C₁ M : ℝ} (hV : ∀ b ∈ I, 0 ≤ V b)
    (hf : ∀ b ∈ I, ∀ j ∈ circ b, f j ≤ M) (hcard : ∀ b, ((circ b).card : ℝ) ≤ C₁)
    (hM : 0 ≤ M) :
    ∑ b ∈ I, V b * ∑ j ∈ circ b, f j ≤ (∑ b ∈ I, V b) * (C₁ * M) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (hV b hb)
  calc ∑ j ∈ circ b, f j ≤ ∑ _j ∈ circ b, M := Finset.sum_le_sum fun j hj => hf b hb j hj
    _ = (circ b).card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C₁ * M := mul_le_mul_of_nonneg_right (hcard b) hM

 


theorem laneB3_phi_upper_tail (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {p : ℝ} (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (hunit : LaneA2HasUnitTails.{u} (ξ : ℝ) p)
    (ζ : ℝ) (hζ : 0 < ζ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A a T₀ : ℝ, ∃ K₀ : ℕ, 0 < A ∧ 0 < a ∧ Real.exp 9 ≤ T₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ K n : ℕ, K₀ ≤ K → K < n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ T : ℝ, T₀ ≤ T →
        P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
            lambdaN (ξ : ℝ) W P (n - K) <
          lenObs (ξ : ℝ) (phiMN W P 0 n) (rectAB 1 1) ω} ≤
          ENNReal.ofReal (A * 4 ^ K *
            Real.exp (-a * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  classical
  obtain ⟨Cneg, cNeg, Cpos, cPos, hCn, hcn, hCp, hcp, hU⟩ := hunit
  obtain ⟨pa, ca, Ca, Cna, cna, Cpa, cpa, hpa, hpaH, hca, hCa, hCna, hcna, hCpa, hcpa,
    hapr⟩ := laneB_apriori_unit_square_power_tails ξ Q hQ (ζ / 2) (by linarith)
  obtain ⟨CO, σ2, hCO, hσ2, hObig⟩ := laneB_Obig_gaussian_tail
  obtain ⟨K₁, hK₁⟩ := laneB3_sqrt_absorb C ζ hC hζ
  have hξ : (0 : ℝ) < ξ := ξ.2
  obtain ⟨C₁, hC₁, hup⟩ := laneB3_upper_pathwise hξ
  set y₀ : ℝ := 4 * (Real.log 3 + |Real.log ca| + |Real.log Ca| + |Real.log (C₁ ^ 2)|) +
    8 * |Real.log Ca| + 9 with hy₀
  set a : ℝ := min (1 / (32 * C₁ ^ 2 * σ2)) (min (cPos / 16) (cpa / 64)) with hadef
  have ha : 0 < a := by positivity
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hab1 := abs_nonneg (Real.log ca)
  have hab2 := abs_nonneg (Real.log Ca)
  have hab3 := abs_nonneg (Real.log (C₁ ^ 2))
  have hy₀9 : 9 ≤ y₀ := by rw [hy₀]; linarith
  refine ⟨CO + 9 * C₁ * Cpos + Cpa, a, Real.exp y₀, max K₁ 2, by positivity, ha,
    Real.exp_le_exp.mpr hy₀9, ?_⟩
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
  have hy9 : 9 ≤ y := hy₀9.trans hyy₀
  set s : ℝ := Real.exp (y / 4) with hsdef
  have hs0 : 0 < s := Real.exp_pos _
  have hy4 : Real.log 3 + |Real.log ca| + |Real.log Ca| + |Real.log (C₁ ^ 2)| < y / 4 := by
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
  have hC₁s : C₁ ^ 2 ≤ s := by
    rw [hsdef, ← Real.exp_log (by positivity : (0 : ℝ) < C₁ ^ 2)]
    refine Real.exp_le_exp.mpr ?_
    have := le_abs_self (Real.log (C₁ ^ 2))
    linarith
  
  obtain ⟨Y, -, hY, -, hYc, -⟩ := exists_C1_modification_phi hW
    (a := ((2 : ℝ) ^ K)⁻¹) (b := 1) (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  obtain ⟨circ, hcard, hcircW⟩ := hup K hK2
  obtain ⟨V, hV0, hVY⟩ := hcircW P W hW m' hm'
  have hpath := hVY Y (fun x => hY x) hYc
  
  set B : ℝ := Real.exp (C * Real.sqrt (K : ℝ)) with hBdef
  have hB : 0 < B := Real.exp_pos _
  have hsand := j1_quantile_sandwich_of_induction P hW (ξ : ℝ) hp
    (by linarith : p ≤ 1 / 2) hH
  have hlam0 : 0 < lambdaN (ξ : ℝ) W P m' := lambdaN_pos hW m'
  
  set g : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) with hgdef
  set g' : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (K : ℝ)) with hg'def
  have hg'0 : 0 ≤ g' := by positivity
  have hBg : B * g' ≤ g := by
    have h1 := hK₁ K hKK₁
    calc B * g' ≤ (2 : ℝ) ^ ((ζ / 2) * (K : ℝ)) * g' :=
          mul_le_mul_of_nonneg_right h1 hg'0
      _ = g := by
          rw [hgdef, hg'def, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  
  set JJ : Finset (Circle × ℂ) := (T20.blkIdx K).biUnion circ with hJJ
  set M : ℝ := s * LambdaN (ξ : ℝ) W P m' (ENNReal.ofReal p) *
    ellN (ξ : ℝ) W P m' (ENNReal.ofReal p) * (2 : ℝ)⁻¹ ^ K with hMdef
  set E1 : Set Ω := {ω | y / (4 * C₁) ≤ Obig K Y ω} with hE1
  set E2 : Set Ω := {ω | ∃ j ∈ JJ,
      s * LambdaN (ξ : ℝ) W P (m' + K - K) (ENNReal.ofReal p) *
        ellN (ξ : ℝ) W P (m' + K - K) (ENNReal.ofReal p) * (2 : ℝ)⁻¹ ^ K <
      T20B.mrectLen (ξ : ℝ) (fun z => phiMN W P K (m' + K) z ω) K
        ((fun j : Circle × ℂ => j.1) j) ((fun j : Circle × ℂ => j.2) j) 3 1} with hE2
  set E3 : Set Ω := {ω | s * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (K : ℝ)) <
      lenObs (ξ : ℝ) (phiMN W P 0 K) (rectAB 1 1) ω} with hE3
  have hM0 : 0 ≤ M := by
    have hv := isPhiVersion_phiMN hW (Nat.zero_le m')
    have hp1 : ENNReal.ofReal p < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
    have hell := T20.ellQ_pos (P := P) (ξ := (ξ : ℝ)) hv.cont hv.meas
      (ENNReal.ofReal_pos.mpr hp) hp1
    have hbar : lambdaN (ξ : ℝ) W P m' ≤ ellBarN (ξ : ℝ) W P m' (ENNReal.ofReal p) :=
      T20B.lambdaN_le_ellBarN (ENNReal.ofReal_pos.mpr hp)
        (by
          have he : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
              ENNReal.ofReal_inv_of_pos (by norm_num)]
            norm_num
          rw [← he]
          exact ENNReal.ofReal_le_ofReal (by linarith)) m'
    have hrat : ellBarN (ξ : ℝ) W P m' (ENNReal.ofReal p) /
        ellN (ξ : ℝ) W P m' (ENNReal.ofReal p) ≤
        LambdaN (ξ : ℝ) W P m' (ENNReal.ofReal p) :=
      Finset.le_sup' (fun k => ellBarN (ξ : ℝ) W P k (ENNReal.ofReal p) /
        ellN (ξ : ℝ) W P k (ENNReal.ofReal p)) (Finset.mem_range.2 (Nat.lt_succ_self m'))
    have hΛ0 : 0 ≤ LambdaN (ξ : ℝ) W P m' (ENNReal.ofReal p) :=
      le_trans (div_nonneg (hlam0.trans_le hbar).le hell.le) hrat
    exact mul_nonneg (mul_nonneg (mul_nonneg hs0.le hΛ0) hell.le) (by positivity)
  have hmain := laneB_measure_le_of_ae_good_imp P
    {ω | T * g * lambdaN (ξ : ℝ) W P m' <
      lenObs (ξ : ℝ) (phiMN W P 0 (m' + K)) (rectAB 1 1) ω} ∅ (E1 ∪ E2 ∪ E3) (by
    filter_upwards [hpath] with ω hω hA hbad
    exfalso
    simp only [Set.mem_union, not_or] at hbad
    obtain ⟨⟨h1, h2⟩, h3⟩ := hbad
    simp only [hE1, hE3, Set.mem_ofPred_eq, not_le, not_lt] at h1 h3
    have hfj : ∀ b ∈ T20.blkIdx K, ∀ j ∈ circ b,
        T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P K (m' + K) x ω) K j.1 j.2 3 1 ≤ M := by
      intro b hb j hj
      by_contra hlt
      push_neg at hlt
      apply h2
      refine ⟨j, by rw [hJJ]; exact Finset.mem_biUnion.2 ⟨b, hb, hj⟩, ?_⟩
      simp only [Nat.add_sub_cancel]
      exact hlt
    have hds := laneB3_double_sum_le (T20.blkIdx K) circ (fun b => V b ω)
      (fun j : Circle × ℂ =>
        T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P K (m' + K) x ω) K j.1 j.2 3 1)
      (fun b hb => hV0 b hb ω) hfj hcard hM0
    have hSV0 : 0 ≤ ∑ b ∈ T20.blkIdx K, V b ω :=
      Finset.sum_nonneg fun b hb => hV0 b hb ω
    have hLk0 : 0 ≤ lenN (ξ : ℝ) W P 1 1 K ω := ENNReal.toReal_nonneg
    have hfin := laneB3_upper_arith (C₁ := C₁) (O := Obig K Y ω) (y := y)
      (SV := ∑ b ∈ T20.blkIdx K, V b ω) (Lk := lenN (ξ : ℝ) W P 1 1 K ω)
      (Ln := lenN (ξ : ℝ) W P 1 1 (m' + K) ω) (M := M)
      (LamEll := LambdaN (ξ : ℝ) W P m' (ENNReal.ofReal p) *
        ellN (ξ : ℝ) W P m' (ENNReal.ofReal p))
      (lam := lambdaN (ξ : ℝ) W P m') (g := g) (g' := g') (B := B) K hC₁ h1
      (hω.1.trans hds) hω.2 hM0 (by rw [hMdef, hsdef]; ring_nf; exact le_rfl) hLk0
      (by rw [← hsdef]; exact h3) hsand.2 hBg hg'0 hlam0.le hC₁s
    have hAω : T * g * lambdaN (ξ : ℝ) W P m' < lenN (ξ : ℝ) W P 1 1 (m' + K) ω := hA
    rw [hTy] at hAω
    linarith)
  
  have hly : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hlogy0 : 0 < Real.log y := by linarith
  have hP1 : P E1 ≤ ENNReal.ofReal (CO * 4 ^ K * Real.exp (-a * y ^ 2 / Real.log y)) := by
    have hx0 : 0 ≤ y / (4 * C₁) := div_nonneg (by linarith) (by positivity)
    have h := hObig hW K Y (fun x => hY x) hYc (y / (4 * C₁)) hx0
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal (h.trans ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hae : a ≤ 1 / (32 * C₁ ^ 2 * σ2) := min_le_left _ _
    have hid : -(y / (4 * C₁)) ^ 2 / (2 * σ2) = -(1 / (32 * C₁ ^ 2 * σ2)) * y ^ 2 := by
      field_simp; ring
    rw [hid]
    have h1 := mul_le_mul_of_nonneg_right hae (sq_nonneg y)
    have h2 : a * y ^ 2 / Real.log y ≤ a * y ^ 2 :=
      div_le_self (by positivity) hly
    have : -a * y ^ 2 / Real.log y = -(a * y ^ 2 / Real.log y) := by ring
    linarith
  have hP2 : P E2 ≤ ENNReal.ofReal (9 * C₁ * Cpos * 4 ^ K *
      Real.exp (-a * y ^ 2 / Real.log y)) := by
    have h := laneB_fine_long_finite_tail P hW hU K (m' + K) (by omega) JJ
      (fun j : Circle × ℂ => j.1) (fun j : Circle × ℂ => j.2) s hs3
    refine h.trans ?_
    have hlogs : Real.log s = y / 4 := by rw [hsdef, Real.log_exp]
    rw [hlogs]
    have hcardJJ : ((JJ.card : ℕ) : ℝ) ≤ 9 * C₁ * 4 ^ K := by
      calc ((JJ.card : ℕ) : ℝ) ≤ ∑ b ∈ T20.blkIdx K, ((circ b).card : ℝ) := by
            rw [hJJ]; exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _b ∈ T20.blkIdx K, C₁ := Finset.sum_le_sum fun b _ => hcard b
        _ = (T20.blkIdx K).card * C₁ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (9 * 4 ^ K) * C₁ := by gcongr; exact card_blkIdx_le K
        _ = 9 * C₁ * 4 ^ K := by ring
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hae : a ≤ cPos / 16 := (min_le_right _ _).trans (min_le_left _ _)
    have hl4 : 0 < Real.log (y / 4) := Real.log_pos (by linarith)
    have hl4y : Real.log (y / 4) ≤ Real.log y := Real.log_le_log (by linarith) (by linarith)
    have he : Real.exp (-cPos * (y / 4) ^ 2 / Real.log (y / 4)) ≤
        Real.exp (-a * y ^ 2 / Real.log y) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : a * y ^ 2 ≤ cPos * (y / 4) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hae (sq_nonneg y)
        have e : cPos / 16 * y ^ 2 = cPos * (y / 4) ^ 2 := by ring
        linarith
      have h2 : a * y ^ 2 / Real.log y ≤ cPos * (y / 4) ^ 2 / Real.log (y / 4) :=
        div_le_div₀ (by positivity) h1 hl4 hl4y
      have e1 : -cPos * (y / 4) ^ 2 / Real.log (y / 4) =
          -(cPos * (y / 4) ^ 2 / Real.log (y / 4)) := by ring
      have e2 : -a * y ^ 2 / Real.log y = -(a * y ^ 2 / Real.log y) := by ring
      linarith
    calc ((JJ.card : ℕ) : ℝ) * (Cpos * Real.exp (-cPos * (y / 4) ^ 2 / Real.log (y / 4)))
        ≤ (9 * C₁ * 4 ^ K) * (Cpos * Real.exp (-a * y ^ 2 / Real.log y)) := by
          gcongr
      _ = 9 * C₁ * Cpos * 4 ^ K * Real.exp (-a * y ^ 2 / Real.log y) := by ring
  have hP3 : P E3 ≤ ENNReal.ofReal (Cpa * 4 ^ K * Real.exp (-a * y ^ 2 / Real.log y)) := by
    have h := (hapr P W hW K s hcas hsCa).2
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hae : a ≤ cpa / 64 := (min_le_right _ _).trans (min_le_right _ _)
    have hlog : Real.log (s / Ca) = y / 4 - Real.log Ca := by
      rw [Real.log_div hs0.ne' hCa.ne', hsdef, Real.log_exp]
    have hlo : y / 8 ≤ Real.log (s / Ca) := by
      rw [hlog]; have := le_abs_self (Real.log Ca); linarith
    have hhi : Real.log (s / Ca) ≤ y := by
      rw [hlog]; have := neg_abs_le (Real.log Ca); linarith
    have hl1 : 1 < Real.log (s / Ca) := by linarith
    have hll0 : 0 < Real.log (Real.log (s / Ca)) := Real.log_pos hl1
    have hlly : Real.log (Real.log (s / Ca)) ≤ Real.log y :=
      Real.log_le_log (by linarith) hhi
    have hsq : (y / 8) ^ 2 ≤ (Real.log (s / Ca)) ^ 2 := pow_le_pow_left₀ (by linarith) hlo 2
    have he : Real.exp (-cpa * (Real.log (s / Ca)) ^ 2 / Real.log (Real.log (s / Ca))) ≤
        Real.exp (-a * y ^ 2 / Real.log y) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : a * y ^ 2 ≤ cpa * (Real.log (s / Ca)) ^ 2 := by
        have h1a := mul_le_mul_of_nonneg_right hae (sq_nonneg y)
        have h1b := mul_le_mul_of_nonneg_left hsq hcpa.le
        have e : cpa / 64 * y ^ 2 = cpa * (y / 8) ^ 2 := by ring
        linarith
      have h2 : a * y ^ 2 / Real.log y ≤
          cpa * (Real.log (s / Ca)) ^ 2 / Real.log (Real.log (s / Ca)) :=
        div_le_div₀ (by positivity) h1 hll0 hlly
      have e1 : -cpa * (Real.log (s / Ca)) ^ 2 / Real.log (Real.log (s / Ca)) =
          -(cpa * (Real.log (s / Ca)) ^ 2 / Real.log (Real.log (s / Ca))) := by ring
      have e2 : -a * y ^ 2 / Real.log y = -(a * y ^ 2 / Real.log y) := by ring
      linarith
    have h4 : (1 : ℝ) ≤ 4 ^ K := one_le_pow₀ (by norm_num)
    have h5 : Real.exp (-a * y ^ 2 / Real.log y) ≤
        4 ^ K * Real.exp (-a * y ^ 2 / Real.log y) :=
      le_mul_of_one_le_left (Real.exp_pos _).le h4
    have h6 := mul_le_mul_of_nonneg_left (he.trans h5) hCpa.le
    linarith [mul_assoc Cpa (4 ^ K : ℝ) (Real.exp (-a * y ^ 2 / Real.log y))]
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
