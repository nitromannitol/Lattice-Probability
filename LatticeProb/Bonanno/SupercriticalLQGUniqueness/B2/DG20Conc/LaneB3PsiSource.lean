/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PsiSource at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PsiTails

 










set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 
theorem laneB3_rate_cmp_gauss {a c₁ y D : ℝ} (hc : c₁ ≤ 9 / 16 * a) (hc0 : 0 ≤ c₁)
    (hD : 1 ≤ D) : Real.exp (-a * (3 * y / 4) ^ 2) ≤ Real.exp (-(c₁ * y ^ 2 / D)) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : c₁ * y ^ 2 / D ≤ c₁ * y ^ 2 := div_le_self (by positivity) hD
  have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  have e : -a * (3 * y / 4) ^ 2 = -(9 / 16 * a * y ^ 2) := by ring
  linarith

 
theorem laneB3_rate_cmp_loglog {a c₁ y Kε : ℝ} (hc : c₁ ≤ 9 / 16 * a) (hc0 : 0 ≤ c₁)
    (hKε : 1 ≤ Kε) (hy : 9 ≤ y) :
    Real.exp (-a * (3 * y / 4) ^ 2 / Real.log (3 * y / 4)) ≤
      Real.exp (-(c₁ * y ^ 2 / (Kε * Real.log y))) := by
  refine Real.exp_le_exp.mpr ?_
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hl34 : 0 < Real.log (3 * y / 4) := Real.log_pos (by linarith)
  have hl34y : Real.log (3 * y / 4) ≤ Real.log y := Real.log_le_log (by linarith) (by linarith)
  have hnum : 0 ≤ c₁ * y ^ 2 := by positivity
  have h1 : c₁ * y ^ 2 / (Kε * Real.log y) ≤ c₁ * y ^ 2 / Real.log y :=
    div_le_div_of_nonneg_left hnum hly (le_mul_of_one_le_left hly.le hKε)
  have h2 : c₁ * y ^ 2 / Real.log y ≤ 9 / 16 * a * y ^ 2 / Real.log y :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg y)) hly.le
  have ha : 0 ≤ 9 / 16 * a * y ^ 2 := le_trans hnum (mul_le_mul_of_nonneg_right hc (sq_nonneg y))
  have h3 : 9 / 16 * a * y ^ 2 / Real.log y ≤ 9 / 16 * a * y ^ 2 / Real.log (3 * y / 4) :=
    div_le_div_of_nonneg_left ha hl34 hl34y
  have e : -a * (3 * y / 4) ^ 2 / Real.log (3 * y / 4) =
      -(9 / 16 * a * y ^ 2 / Real.log (3 * y / 4)) := by ring
  linarith

 
theorem laneB3_rate_cmp_xbig {cX c₁ y D ξ : ℝ} (hξ : 0 < ξ) (hc : c₁ ≤ cX / (16 * ξ ^ 2))
    (hc0 : 0 ≤ c₁) (hD : 1 ≤ D) :
    Real.exp (-(cX * (y / (4 * ξ)) ^ 2)) ≤ Real.exp (-(c₁ * y ^ 2 / D)) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : c₁ * y ^ 2 / D ≤ c₁ * y ^ 2 := div_le_self (by positivity) hD
  have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  have e : cX * (y / (4 * ξ)) ^ 2 = cX / (16 * ξ ^ 2) * y ^ 2 := by field_simp; ring
  linarith

 

theorem laneB3_lower_tail_pt {ψ φ X x ξ y T T' g l : ℝ} (hψ0 : 0 ≤ ψ)
    (h1 : φ ≤ Real.exp (|ξ| * X) * ψ) (hbad : X < x) (hA : ψ < T⁻¹ * g * l)
    (hex : Real.exp (|ξ| * x) = Real.exp (y / 4)) (hTT' : T = Real.exp (y / 4) * T') :
    φ < T'⁻¹ * g * l := by
  have hexp : Real.exp (|ξ| * X) ≤ Real.exp (|ξ| * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbad.le (abs_nonneg _))
  have h2 : φ ≤ Real.exp (|ξ| * x) * ψ := h1.trans (mul_le_mul_of_nonneg_right hexp hψ0)
  have h3 : Real.exp (|ξ| * x) * ψ < Real.exp (|ξ| * x) * (T⁻¹ * g * l) :=
    mul_lt_mul_of_pos_left hA (Real.exp_pos _)
  have h4 : Real.exp (|ξ| * x) * (T⁻¹ * g * l) = T'⁻¹ * g * l := by
    rw [hex, hTT', mul_inv]
    have : Real.exp (y / 4) * (Real.exp (y / 4))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.exp_pos _).ne'
    calc Real.exp (y / 4) * ((Real.exp (y / 4))⁻¹ * T'⁻¹ * g * l)
        = (Real.exp (y / 4) * (Real.exp (y / 4))⁻¹) * T'⁻¹ * g * l := by ring
      _ = T'⁻¹ * g * l := by rw [this, one_mul]
  linarith

 
theorem laneB3_upper_tail_pt {ψ φ X x ξ y T T' g l : ℝ} (hφ0 : 0 ≤ φ)
    (h1 : ψ ≤ Real.exp (|ξ| * X) * φ) (hbad : X < x) (hA : T * g * l < ψ)
    (hex : Real.exp (|ξ| * x) = Real.exp (y / 4))
    (hTsplit : ∀ z : ℝ, T * z = Real.exp (y / 4) * (T' * z)) :
    T' * g * l < φ := by
  have hexp : Real.exp (|ξ| * X) ≤ Real.exp (|ξ| * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbad.le (abs_nonneg _))
  have h2 : ψ ≤ Real.exp (y / 4) * φ := by
    have := h1.trans (mul_le_mul_of_nonneg_right hexp hφ0)
    rwa [hex] at this
  have h3 : Real.exp (y / 4) * (T' * g * l) < Real.exp (y / 4) * φ := by
    have e := hTsplit (g * l)
    have hA' : T * (g * l) < ψ := by rw [← mul_assoc]; exact hA
    rw [e, ← mul_assoc T'] at hA'
    exact lt_of_lt_of_le hA' h2
  exact lt_of_mul_lt_mul_left h3 (Real.exp_pos _).le

 



theorem laneB3_fixedP_subadd_tails (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (Qψ : PsiParams) {p : ℝ} (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (hunit : LaneA2HasUnitTails.{u} (ξ : ℝ) p) :
    LaneB3Defs.B3FixedPSubaddTails.{u} Qψ ξ Q p := by
  intro ζ C hζ hC
  obtain ⟨A, a, T₀, K₁, hA, ha, hT₀, hφ⟩ :=
    laneB3_phi_tails_ge ξ Q hQ hp hpHalf hunit ζ hζ C hC.le
  obtain ⟨CX, cX, hCX, hcX, hX⟩ := laneB_Xbig_real_gaussian_tail_uniform Qψ
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hT₀pos : 0 < T₀ := lt_of_lt_of_le (Real.exp_pos 9) hT₀
  have hlT₀ : 9 ≤ Real.log T₀ := by rw [Real.le_log_iff_exp_le hT₀pos]; exact hT₀
  set ym : ℝ := 4 / 3 * Real.log T₀ + 9 with hym
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K₂, hK₂⟩ := exists_nat_ge ((ym / Real.log 2) ^ 2)
  set c₁ : ℝ := min (9 / 16 * a) (cX / (16 * (ξ : ℝ) ^ 2)) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  refine ⟨max K₁ (max K₂ 1), A + CX, c₁, by positivity, hc₁0, ?_⟩
  intro Ω _ P W hW n K hK hKn hH T hT
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hKK₁ : K₁ ≤ K := (le_max_left _ _).trans hK
  have hKK₂ : K₂ ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
  have hK1 : 1 ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans hK
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  
  have h2pos : 0 < (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) := by positivity
  have hTpos : 0 < T := h2pos.trans hT
  set y : ℝ := Real.log T with hydef
  have hylo : (K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀) * Real.log 2 < y := by
    have := Real.log_lt_log h2pos hT
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at this
  have hsqrtK : Real.sqrt (K : ℝ) ≤ (K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hK1r (by linarith [Qψ.ε₀_pos])
  have hymK : ym / Real.log 2 ≤ Real.sqrt (K : ℝ) := by
    have hym0 : 0 ≤ ym / Real.log 2 := div_nonneg (by linarith) hl2.le
    rw [show ym / Real.log 2 = Real.sqrt ((ym / Real.log 2) ^ 2) by rw [Real.sqrt_sq hym0]]
    exact Real.sqrt_le_sqrt (hK₂.trans (by exact_mod_cast hKK₂))
  have hyym : ym ≤ y := by
    have h1 : ym ≤ Real.sqrt (K : ℝ) * Real.log 2 := by
      rwa [div_le_iff₀ hl2] at hymK
    have h2 := mul_le_mul_of_nonneg_right hsqrtK hl2.le
    linarith
  have hy9 : 9 ≤ y := by linarith
  set T' : ℝ := Real.exp (3 * y / 4) with hT'def
  have hlogT' : Real.log T' = 3 * y / 4 := by rw [hT'def, Real.log_exp]
  have hT₀T' : T₀ ≤ T' := by
    rw [hT'def, ← Real.exp_log hT₀pos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hTT' : T = Real.exp (y / 4) * T' := by
    rw [hT'def, ← Real.exp_add, hydef, ← Real.exp_log hTpos, Real.log_exp]; ring_nf
  set x : ℝ := y / (4 * (ξ : ℝ)) with hxdef
  have hx0 : 0 < x := div_pos (by linarith) (by positivity)
  have hex : Real.exp (|(ξ : ℝ)| * x) = Real.exp (y / 4) := by
    rw [abs_of_pos hξ, hxdef]; congr 1; field_simp
  
  have hKε : (1 : ℝ) ≤ (K : ℝ) ^ (3 * Qψ.ε₀) :=
    Real.one_le_rpow hK1r (by linarith [Qψ.ε₀_pos])
  have hly1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hD : 1 ≤ (K : ℝ) ^ (3 * Qψ.ε₀) * Real.log y := by nlinarith
  have h45 : (4 : ℝ) ^ K ≤ 5 ^ K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
  have h15 : (1 : ℝ) ≤ 5 ^ K := one_le_pow₀ (by norm_num)
  have hcA : c₁ ≤ 9 / 16 * a := min_le_left _ _
  have hcX' : c₁ ≤ cX / (16 * (ξ : ℝ) ^ 2) := min_le_right _ _
  set R : ℝ := c₁ * y ^ 2 / ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log y) with hR
  have hXbad : P {ω | x ≤ T20C.Xbig Qψ W P ω} ≤
      ENNReal.ofReal (CX * (5 : ℝ) ^ K * Real.exp (-R)) := by
    refine (hX P W hW x hx0).trans (ENNReal.ofReal_le_ofReal ?_)
    have he := laneB3_rate_cmp_xbig (y := y) hξ hcX' hc₁0.le hD
    have h1 : CX * Real.exp (-(cX * x ^ 2)) ≤ CX * Real.exp (-R) :=
      mul_le_mul_of_nonneg_left he hCX.le
    have h2 : CX * Real.exp (-R) ≤ CX * 5 ^ K * Real.exp (-R) := by
      have := mul_le_mul_of_nonneg_left h15 hCX.le
      nlinarith [Real.exp_pos (-R)]
    linarith
  have hcmp := laneB3_ae_lenObs_compare hW Qψ (ξ : ℝ)
  have hTsplit : ∀ z : ℝ, T * z = Real.exp (y / 4) * (T' * z) := by
    intro z; rw [hTT']; ring
  obtain ⟨hφL, hφU⟩ := hφ P W hW K n hKK₁ hKn hH T' hT₀T'
  rw [hlogT'] at hφL hφU
  refine ⟨?_, ?_⟩
  · 
    generalize hg : (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) = g at hφL ⊢
    have hmain := laneB_measure_le_of_ae_good_imp P
      {ω | lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω <
        T⁻¹ * g * lambdaN (ξ : ℝ) W P (n - K)}
      {ω | lenObs (ξ : ℝ) (phiMN W P 0 n) (rectAB 1 1) ω <
        T'⁻¹ * g * lambdaN (ξ : ℝ) W P (n - K)}
      {ω | x ≤ T20C.Xbig Qψ W P ω} (by
        filter_upwards [hcmp] with ω hω hA hbad
        simp only [not_le] at hA hbad ⊢
        exact laneB3_lower_tail_pt ENNReal.toReal_nonneg (hω n).2 hbad hA hex hTT')
    refine hmain.trans ((add_le_add hφL hXbad).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have he := laneB3_rate_cmp_gauss (y := y) hcA hc₁0.le hD
    have h1 : A * 4 ^ K * Real.exp (-a * (3 * y / 4) ^ 2) ≤ A * 5 ^ K * Real.exp (-R) := by
      gcongr
    refine le_trans (add_le_add h1 le_rfl) (le_of_eq ?_)
    ring
  · 
    generalize hg : (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) = g at hφU ⊢
    have hmain := laneB_measure_le_of_ae_good_imp P
      {ω | T * g * lambdaN (ξ : ℝ) W P (n - K) <
        lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω}
      {ω | T' * g * lambdaN (ξ : ℝ) W P (n - K) <
        lenObs (ξ : ℝ) (phiMN W P 0 n) (rectAB 1 1) ω}
      {ω | x ≤ T20C.Xbig Qψ W P ω} (by
        filter_upwards [hcmp] with ω hω hA hbad
        simp only [not_le] at hA hbad ⊢
        exact laneB3_upper_tail_pt ENNReal.toReal_nonneg (hω n).1 hbad hA hex hTsplit)
    refine hmain.trans ((add_le_add hφU hXbad).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have he := laneB3_rate_cmp_loglog (y := y) hcA hc₁0.le hKε hy9
    have h1 : A * 4 ^ K * Real.exp (-a * (3 * y / 4) ^ 2 / Real.log (3 * y / 4)) ≤
        A * 5 ^ K * Real.exp (-R) := by
      gcongr
    refine le_trans (add_le_add h1 le_rfl) (le_of_eq ?_)
    ring

end SupercriticalLQGUniqueness.B2.DG20Conc
