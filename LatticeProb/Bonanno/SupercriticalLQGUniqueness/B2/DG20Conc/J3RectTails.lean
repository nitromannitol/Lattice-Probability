/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J3RectTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Defs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB4
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum

 












set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem j3_prob_mrectLen_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (ξ : ℝ) (K n : ℕ) (u : Circle) (c : ℂ)
    (a b : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 n x ω) K u c a b ∈ S} =
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB ((2 : ℝ)⁻¹ ^ K * a) ((2 : ℝ)⁻¹ ^ K * b)) ω ∈ S} := by
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have hS' : MeasurableSet (ENNReal.toReal ⁻¹' S) := ENNReal.measurable_toReal hS
  have hK : IsCompact ((fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' (rectAB a b).toSet) :=
    (rectAB a b).isCompact_toSet.image (continuous_const.mul continuous_id)
  have h1 := measure_crossLenIn_phiMN_motion (ξ := ξ) hW (Nat.zero_le n) u c hK
    (A := (fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' (rectAB a b).side₁)
    (B := (fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' (rectAB a b).side₂) hS'
  simp only [T20B.mrectLen, T20B.mot_image]
  change P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω)
      ((fun x => (u : ℂ) * x + c) '' ((fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' (rectAB a b).toSet))
      ((fun x => (u : ℂ) * x + c) '' ((fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' (rectAB a b).side₁))
      ((fun x => (u : ℂ) * x + c) '' ((fun x => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) '' (rectAB a b).side₂))
        ∈ ENNReal.toReal ⁻¹' S} = _
  rw [h1, image_mul_rectAB_toSet hr, image_mul_rectAB_side₁ hr, image_mul_rectAB_side₂ hr]
  rfl

 


theorem j3_mrectLen_tails (hJ2 : J2Defs.QuantileRatioAllP) (ξ : Set.Ioi (0 : ℝ)) (K : ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ (n : ℕ) (u : Circle) (c' : ℂ) (s : ℝ), 2 < s →
        P {ω | Real.exp s * lambdaN (ξ : ℝ) W P n ≤
            T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) K u c' a b} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) ∧
        P {ω | T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) K u c' a b ≤
            Real.exp (-s) * lambdaN (ξ : ℝ) W P n} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  have hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN (ξ : ℝ) W₀ P₀ n (ENNReal.ofReal p) ≤ B := by
    refine ⟨1 / 4, by norm_num, fun p hp hp4 => ?_⟩
    obtain ⟨B, hB⟩ := hJ2 ξ p hp (by linarith)
    exact ⟨B, hB P₀ W₀ hW₀⟩
  set r : ℝ := (2 : ℝ)⁻¹ ^ K with hr
  have hr0 : 0 < r := by positivity
  set A₀ : ℝ := r * min a b
  set B₀ : ℝ := r * max a b
  have hA₀ : 0 < A₀ := mul_pos hr0 (lt_min ha hb)
  obtain ⟨c₁, C₁, hc₁, hC₁, hR⟩ := S6AB.dyadic_right_AB hW₀ hξ hΛ (A₀ := A₀) (B₀ := B₀) hA₀
  obtain ⟨c₂, C₂, hc₂, hC₂, hL⟩ := S6AB.dyadic_left_AB hW₀ hξ hΛ (A₀ := A₀) (B₀ := B₀) hA₀
  have hxa : r * a ∈ Icc A₀ B₀ := ⟨mul_le_mul_of_nonneg_left (min_le_left _ _) hr0.le,
    mul_le_mul_of_nonneg_left (le_max_left _ _) hr0.le⟩
  have hyb : r * b ∈ Icc A₀ B₀ := ⟨mul_le_mul_of_nonneg_left (min_le_right _ _) hr0.le,
    mul_le_mul_of_nonneg_left (le_max_right _ _) hr0.le⟩
  refine ⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, ?_⟩
  intro Ω _ P W hW n u c' s hs
  have hlam : lambdaN (ξ : ℝ) W P n = lambdaN (ξ : ℝ) W₀ P₀ n := by
    unfold lambdaN lenN lenMN
    rw [laneA_law_lenObs_eq hW hW₀ (ξ : ℝ) n (rectAB 1 1)]
  have hs0 : 0 < s := by linarith
  have hls : 0 < Real.log s := Real.log_pos (by linarith)
  constructor
  · set t : ℝ := Real.exp s * lambdaN (ξ : ℝ) W P n with ht
    have e1 := j3_prob_mrectLen_eq hW (ξ : ℝ) K n u c' a b (measurableSet_Ici : MeasurableSet (Ici t))
    have e2 := laneA_prob_lenObs_eq hW hW₀ (ξ : ℝ) n
      (rectAB ((2 : ℝ)⁻¹ ^ K * a) ((2 : ℝ)⁻¹ ^ K * b)) (measurableSet_Ici : MeasurableSet (Ici t))
    change P {ω | T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) K u c' a b ∈ Ici t} ≤ _
    rw [e1, e2, ht, hlam]
    refine (hR (r * a) hxa (r * b) hyb n s hs).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (hC₁.le.trans (le_max_left _ _))
    have h1 : min c₁ c₂ * s ^ 2 / Real.log s ≤ c₁ * s ^ 2 / Real.log s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg s))
        hls.le
    have e2 : -c₁ * s ^ 2 / Real.log s = -(c₁ * s ^ 2 / Real.log s) := by ring
    have e3 : -min c₁ c₂ * s ^ 2 / Real.log s = -(min c₁ c₂ * s ^ 2 / Real.log s) := by ring
    linarith
  · set t : ℝ := Real.exp (-s) * lambdaN (ξ : ℝ) W P n with ht
    have e1 := j3_prob_mrectLen_eq hW (ξ : ℝ) K n u c' a b (measurableSet_Iic : MeasurableSet (Iic t))
    have e2 := laneA_prob_lenObs_eq hW hW₀ (ξ : ℝ) n
      (rectAB ((2 : ℝ)⁻¹ ^ K * a) ((2 : ℝ)⁻¹ ^ K * b)) (measurableSet_Iic : MeasurableSet (Iic t))
    change P {ω | T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) K u c' a b ∈ Iic t} ≤ _
    rw [e1, e2, ht, hlam]
    refine (hL (r * a) hxa (r * b) hyb n s hs).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (hC₁.le.trans (le_max_left _ _))
    have := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (sq_nonneg s)
    linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
