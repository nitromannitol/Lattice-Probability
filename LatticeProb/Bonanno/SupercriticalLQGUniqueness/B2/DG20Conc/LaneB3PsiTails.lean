/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PsiTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Base
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareFieldSplit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigRealUniform

 









set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

theorem laneB3_rectLen_toReal_le_exp {ξ M : ℝ} {f g : ℂ → ℝ} (hg : Continuous g)
    (h : ∀ x ∈ (rectAB 1 1).toSet, |f x - g x| ≤ M) :
    (rectLen ξ f (rectAB 1 1)).toReal ≤
      Real.exp (|ξ| * M) * (rectLen ξ g (rectAB 1 1)).toReal := by
  have hcmp : rectLen ξ f (rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * rectLen ξ g (rectAB 1 1) :=
    crossLenIn_le_of_abs_sub_le h
  have hfin : rectLen ξ g (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hg
  have hrhs : ENNReal.ofReal (Real.exp (|ξ| * M)) * rectLen ξ g (rectAB 1 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal := ENNReal.toReal_mono hrhs hcmp
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal

 

theorem laneB3_ae_lenObs_compare {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Qψ : PsiParams) (ξ : ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) ω ≤
        Real.exp (|ξ| * T20C.Xbig Qψ W P ω) * lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ∧
      lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
        Real.exp (|ξ| * T20C.Xbig Qψ W P ω) * lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) ω := by
  filter_upwards [T20D.ae_XAB_shift_ne_top hW Qψ T20C.cBig 5 5] with ω hfin n
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hψ := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le n)
  have hab : ∀ x ∈ (rectAB 1 1).toSet,
      |phiMN W P 0 n x ω - psiMN Qψ W P 0 n x ω| ≤ T20C.Xbig Qψ W P ω := fun x hx =>
    T20D.abs_sub_le_Xbig Qψ hfin n (laneB_unit_square_subset_bigBox hx)
  refine ⟨?_, ?_⟩
  · exact laneB3_rectLen_toReal_le_exp (hφ.cont ω) fun x hx => by
      rw [abs_sub_comm]; exact hab x hx
  · exact laneB3_rectLen_toReal_le_exp (hψ.cont ω) hab

 

theorem laneB3_phi_tails_ge (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {p : ℝ} (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (hunit : LaneA2HasUnitTails.{u} (ξ : ℝ) p)
    (ζ : ℝ) (hζ : 0 < ζ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A a T₀ : ℝ, ∃ K₀ : ℕ, 0 < A ∧ 0 < a ∧ Real.exp 9 ≤ T₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ K n : ℕ, K₀ ≤ K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ T : ℝ, T₀ ≤ T →
        P {ω | lenObs (ξ : ℝ) (phiMN W P 0 n) (rectAB 1 1) ω <
          T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
            lambdaN (ξ : ℝ) W P (n - K)} ≤
          ENNReal.ofReal (A * 4 ^ K * Real.exp (-a * (Real.log T) ^ 2)) ∧
        P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
            lambdaN (ξ : ℝ) W P (n - K) <
          lenObs (ξ : ℝ) (phiMN W P 0 n) (rectAB 1 1) ω} ≤
          ENNReal.ofReal (A * 4 ^ K *
            Real.exp (-a * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨A1, a1, T1, K1, hA1, ha1, hT1, hlow⟩ :=
    laneB3_phi_lower_tail ξ Q hQ hp hpHalf hunit ζ hζ C hC
  obtain ⟨A2, a2, T2, K2, hA2, ha2, hT2, hup⟩ :=
    laneB3_phi_upper_tail ξ Q hQ hp hpHalf hunit ζ hζ C hC
  obtain ⟨A3, a3, T3, hA3, ha3, hT3, hlow0⟩ := laneB3_phi_lower_tail_base ξ Q hQ ζ hζ
  obtain ⟨A4, a4, T4, hA4, ha4, hT4, hup0⟩ := laneB3_phi_upper_tail_base ξ Q hQ ζ hζ
  refine ⟨A1 + A2 + A3 + A4, min (min a1 a2) (min a3 a4), max (max T1 T2) (max T3 T4),
    max K1 K2, by positivity, by positivity,
    hT2.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  have hT1' : T1 ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2' : T2 ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT3' : T3 ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT4' : T4 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 9) (hT4.trans hT4')
  have hy9 : 9 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]; exact hT4.trans hT4'
  have hly : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  have h4 : (1 : ℝ) ≤ 4 ^ K := one_le_pow₀ (by norm_num)
  set a := min (min a1 a2) (min a3 a4) with hadef
  have hsq : 0 ≤ (Real.log T) ^ 2 := sq_nonneg _
  have hsq' : 0 ≤ (Real.log T) ^ 2 / Real.log (Real.log T) := div_nonneg hsq hly.le
  
  have mono1 : ∀ (A' a' : ℝ), 0 < A' → a ≤ a' → A' ≤ A1 + A2 + A3 + A4 →
      ENNReal.ofReal (A' * 4 ^ K * Real.exp (-a' * (Real.log T) ^ 2)) ≤
        ENNReal.ofReal ((A1 + A2 + A3 + A4) * 4 ^ K * Real.exp (-a * (Real.log T) ^ 2)) := by
    intro A' a' hA' ha' hAA
    refine ENNReal.ofReal_le_ofReal ?_
    have he : Real.exp (-a' * (Real.log T) ^ 2) ≤ Real.exp (-a * (Real.log T) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4' : (0 : ℝ) ≤ 4 ^ K := by positivity
    gcongr
  have mono2 : ∀ (A' a' : ℝ), 0 < A' → a ≤ a' → A' ≤ A1 + A2 + A3 + A4 →
      ENNReal.ofReal (A' * 4 ^ K *
          Real.exp (-a' * (Real.log T) ^ 2 / Real.log (Real.log T))) ≤
        ENNReal.ofReal ((A1 + A2 + A3 + A4) * 4 ^ K *
          Real.exp (-a * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
    intro A' a' hA' ha' hAA
    refine ENNReal.ofReal_le_ofReal ?_
    have he : Real.exp (-a' * (Real.log T) ^ 2 / Real.log (Real.log T)) ≤
        Real.exp (-a * (Real.log T) ^ 2 / Real.log (Real.log T)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff, mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right ha' hsq'
    gcongr
  have hbase : ∀ (A' : ℝ) (E : ℝ), 0 ≤ A' → 0 ≤ E →
      ENNReal.ofReal (A' * E) ≤ ENNReal.ofReal (A' * 4 ^ K * E) := by
    intro A' E hA' hE
    refine ENNReal.ofReal_le_ofReal ?_
    have h4A := mul_le_mul_of_nonneg_left h4 hA'
    have hE' := mul_le_mul_of_nonneg_right h4A hE
    simpa [mul_one, mul_assoc] using hE'
  by_cases hlt : K < n
  · refine ⟨(hlow P W hW K n ((le_max_left _ _).trans hK) hlt hH T hT1').trans ?_,
      (hup P W hW K n ((le_max_right _ _).trans hK) hlt hH T hT2').trans ?_⟩
    · exact mono1 A1 a1 hA1 ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    · exact mono2 A2 a2 hA2 ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  · obtain rfl : n = K := le_antisymm (not_lt.mp hlt) hKn
    simp only [Nat.sub_self]
    refine ⟨(hlow0 P W hW n T hT3').trans ?_, (hup0 P W hW n T hT4').trans ?_⟩
    · refine (hbase A3 _ hA3.le (Real.exp_pos _).le).trans ?_
      exact mono1 A3 a3 hA3 ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    · refine (hbase A4 _ hA4.le (Real.exp_pos _).le).trans ?_
      exact mono2 A4 a4 hA4 ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)

end SupercriticalLQGUniqueness.B2.DG20Conc
