/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldAbsorbLarge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateShift

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem threshold_div_lower (C B T a : ℝ)
    (hC : 0 < C) (hCB : C ≤ B) (hT : 0 < T) (ha : 0 ≤ a) :
    T⁻¹ * a ≤ (T / B)⁻¹ * (C⁻¹ * a) := by
  have hB : 0 < B := lt_of_lt_of_le hC hCB
  have hcoeff : T⁻¹ ≤ (T / B)⁻¹ * C⁻¹ := by
    have heq : (T / B)⁻¹ * C⁻¹ = B / (T * C) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (mul_pos hT hC)).2
    field_simp
    exact hCB
  calc
    T⁻¹ * a ≤ ((T / B)⁻¹ * C⁻¹) * a :=
      mul_le_mul_of_nonneg_right hcoeff ha
    _ = (T / B)⁻¹ * (C⁻¹ * a) := by ring

private theorem threshold_div_upper (C B T b : ℝ)
    (hC : 0 < C) (hCB : C ≤ B) (hT : 0 < T) (hb : 0 ≤ b) :
    (T / B) * (C * b) ≤ T * b := by
  have hB : 0 < B := lt_of_lt_of_le hC hCB
  have hcoef : (T / B) * C ≤ T := by
    calc
      (T / B) * C = (T * C) / B := by ring
      _ ≤ T := (div_le_iff₀ hB).2
        (mul_le_mul_of_nonneg_left hCB hT.le)
  calc
    (T / B) * (C * b) = ((T / B) * C) * b := by ring
    _ ≤ T * b := mul_le_mul_of_nonneg_right hcoef hb

 

theorem perc_field_tail_event_div (C B T a b : ℝ)
    (hC : 0 < C) (hCB : C ≤ B) (hT : 0 < T)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    {Ω : Type} (D : Ω → ℝ≥0∞) (φ : Ω → ℝ) :
    {ω | D ω < ENNReal.ofReal (Real.exp (φ ω)) *
        ENNReal.ofReal (T⁻¹ * a)} ⊆
      {ω | D ω < ENNReal.ofReal (Real.exp (φ ω)) *
        ENNReal.ofReal ((T / B)⁻¹ * (C⁻¹ * a))} ∧
    {ω | ENNReal.ofReal (Real.exp (φ ω)) *
        ENNReal.ofReal (T * b) < D ω} ⊆
      {ω | ENNReal.ofReal (Real.exp (φ ω)) *
        ENNReal.ofReal ((T / B) * (C * b)) < D ω} := by
  have hlo := ENNReal.ofReal_le_ofReal (threshold_div_lower C B T a hC hCB hT ha)
  have hhi := ENNReal.ofReal_le_ofReal (threshold_div_upper C B T b hC hCB hT hb)
  constructor
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_lt_of_le hω (by gcongr)
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt (by gcongr) hω

 


theorem perc_field_bounded_large_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (hU : Bornology.IsBounded (U : Set ℂ))
    (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (hconnU : IsConnected (U : Set ℂ)) :
    ∃ B c₀ c₁ : ℝ, 1 ≤ B ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ,
        max (9 * B) (B ^ 2) < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) ∧
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨C, c, d, e, f, hC, hc, hd, he, hf, hbefore⟩ :=
    perc_field_bounded_rate_of_inputs hPerc hExp ξ Q hQ ζ hζ U hU
      K₁ K₂ hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  let B : ℝ := max C 1
  have hB : 1 ≤ B := le_max_right C 1
  have hCB : C ≤ B := le_max_left C 1
  let a : ℝ := e + c
  let α : ℝ := min f d / 4
  let β : ℝ := min (f * Real.log (Real.log 3)) d / 4
  let c₁ : ℝ := min α β / 4
  have ha : 0 < a := add_pos he hc
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hβ : 0 < β := by dsimp [β]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  refine ⟨B, a, c₁, hB, ha, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hT0 : 0 < T := by
    have : 9 * B < T := (le_max_left _ _).trans_lt hT
    nlinarith
  have hS9 : 9 < T / B := (lt_div_iff₀ hB0).2
    ((le_max_left _ _).trans_lt hT)
  obtain ⟨hlo, hhi⟩ := hbefore P W hW n k hkn (T / B) hS9
  let lo : ℝ := (2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n
  let hi : ℝ := (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n
  have hlam : 0 < lambdaN ξ W P n := lambdaN_pos hW n
  have hlo0 : 0 ≤ lo := by dsimp [lo]; positivity
  have hhi0 : 0 ≤ hi := by dsimp [hi]; positivity
  let D : Ω → ℝ≥0∞ := fun ω =>
    crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
      ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * z) '' U)
      ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * z) '' K₁)
      ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * z) '' K₂)
  let φ : Ω → ℝ := fun ω => (ξ : ℝ) * phiMN W P 0 k 0 ω
  have hevents := perc_field_tail_event_div C B T lo hi hC hCB hT0
    hlo0 hhi0 D φ
  dsimp at hlo hhi ⊢
  constructor
  · refine (measure_mono (by simpa only [D, φ, lo, mul_assoc] using hevents.1)).trans
      (hlo.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    change a * Real.exp (-α * (Real.log (T / B)) ^ 2) ≤
      a * Real.exp (-c₁ * (Real.log T) ^ 2)
    apply mul_le_mul_of_nonneg_left _ ha.le
    exact gaussian_rate_div_bound α B T hα hB hT |>.trans
      (Real.exp_le_exp.mpr (by
        have hcoef : c₁ ≤ α / 4 :=
          div_le_div_of_nonneg_right (min_le_left α β) (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) (sq_nonneg (Real.log T))]))
  · refine (measure_mono (by simpa only [D, φ, hi, mul_assoc] using hevents.2)).trans
      (hhi.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    change a * Real.exp (-β * (Real.log (T / B)) ^ 2 /
      Real.log (Real.log (T / B))) ≤
      a * Real.exp (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))
    apply mul_le_mul_of_nonneg_left _ ha.le
    exact gaussian_loglog_rate_div_bound β B T hβ hB hT |>.trans
      (Real.exp_le_exp.mpr (by
        have hcoef : c₁ ≤ β / 4 :=
          div_le_div_of_nonneg_right (min_le_right α β) (by norm_num)
        have hLL : 0 < Real.log (Real.log T) := by
          have hT3 : 3 < T := by
            have h9B : 9 * B < T := (le_max_left _ _).trans_lt hT
            nlinarith [hB]
          have hlogT : 1 < Real.log T :=
            (Real.lt_log_iff_exp_lt hT0).2
              (lt_trans Real.exp_one_lt_three hT3)
          exact Real.log_pos hlogT
        apply div_le_div_of_nonneg_right _ hLL.le
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) (sq_nonneg (Real.log T))]))

end SupercriticalLQGUniqueness.B2.DG20Pt
