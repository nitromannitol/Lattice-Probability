/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatLambdaDyadicPair at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianUniform

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_lambda_delta_dyadic_pair_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W →
        ∀ n₁ n₂ : ℕ, n₂ ≤ n₁ →
        ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ 1 →
          0 ≤ s₂ → s₂ ≤ 1 →
          B⁻¹ * (C⁻¹ *
            (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * ((n₁ - n₂ : ℕ) : ℝ)) *
            lambdaDelta ξ W P ((2 : ℝ) ^ (-((n₂ : ℝ) + s₂)))) ≤
            lambdaDelta ξ W P ((2 : ℝ) ^ (-((n₁ : ℝ) + s₁))) ∧
          lambdaDelta ξ W P ((2 : ℝ) ^ (-((n₁ : ℝ) + s₁))) ≤
            B * (C *
              (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * ((n₁ - n₂ : ℕ) : ℝ)) *
              lambdaDelta ξ W P ((2 : ℝ) ^ (-((n₂ : ℝ) + s₂)))) := by
  obtain ⟨C, hC, hscale⟩ := hExp ξ Q hQ ζ hζ
  obtain ⟨D, hmed⟩ := dg20_non_dyadic_median_compare_uniform_of_perc hPerc ξ
  let B : ℝ := Real.exp (2 * |D|)
  have hB : 0 < B := Real.exp_pos _
  refine ⟨C, B, hC, hB, ?_⟩
  intro Ω _ P _ W hW n₁ n₂ hn s₁ s₂ hs₁ hs₁' hs₂ hs₂'
  have hi : n₁ - (n₁ - n₂) = n₂ := by omega
  obtain ⟨hscaleLo, hscaleHi⟩ := hscale P W hW n₁ (n₁ - n₂) (Nat.sub_le _ _)
  rw [hi] at hscaleLo hscaleHi
  obtain ⟨hmed₁Lo, hmed₁Hi⟩ := hmed P W hW n₁ s₁ hs₁ hs₁'
  obtain ⟨hmed₂Lo, hmed₂Hi⟩ := hmed P W hW n₂ s₂ hs₂ hs₂'
  let l₁ : ℝ := lambdaDelta ξ W P ((2 : ℝ) ^ (-((n₁ : ℝ) + s₁)))
  let l₂ : ℝ := lambdaDelta ξ W P ((2 : ℝ) ^ (-((n₂ : ℝ) + s₂)))
  let L₁ : ℝ := lambdaN ξ W P n₁
  let L₂ : ℝ := lambdaN ξ W P n₂
  let Elo : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * ((n₁ - n₂ : ℕ) : ℝ))
  let Ehi : ℝ := (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * ((n₁ - n₂ : ℕ) : ℝ))
  have hD1 : Real.exp (-|D|) * L₁ ≤ l₁ := by
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (neg_le_neg (le_abs_self D)))
      (lambdaN_pos hW n₁).le).trans hmed₁Lo
  have hD1' : l₁ ≤ Real.exp |D| * L₁ := by
    exact hmed₁Hi.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (le_abs_self D)) (lambdaN_pos hW n₁).le)
  have hD2 : Real.exp (-|D|) * l₂ ≤ L₂ := by
    have hh := mul_le_mul_of_nonneg_left hmed₂Hi (Real.exp_pos (-|D|)).le
    calc
      Real.exp (-|D|) * l₂ ≤
          Real.exp (-|D|) * (Real.exp D * L₂) := hh
      _ ≤ Real.exp (-|D|) * (Real.exp |D| * L₂) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (le_abs_self D)) (lambdaN_pos hW n₂).le)
          (Real.exp_pos _).le
      _ = L₂ := by rw [← mul_assoc, ← Real.exp_add]; simp
  have hD2' : L₂ ≤ Real.exp |D| * l₂ := by
    have hl₂ : 0 ≤ l₂ :=
      (mul_nonneg (Real.exp_pos _).le (lambdaN_pos hW n₂).le).trans hmed₂Lo
    have hh := mul_le_mul_of_nonneg_left hmed₂Lo (Real.exp_pos D).le
    have hLe : Real.exp D * (Real.exp (-D) * L₂) = L₂ := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    calc
      L₂ = Real.exp D * (Real.exp (-D) * L₂) := hLe.symm
      _ ≤ Real.exp D * l₂ := hh
      _ ≤ Real.exp |D| * l₂ := by
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.2 (le_abs_self D)) hl₂
  have hBlo : B⁻¹ = Real.exp (-|D|) * Real.exp (-|D|) := by
    dsimp [B]
    rw [show 2 * |D| = |D| + |D| by ring, Real.exp_add,
      mul_inv_rev, Real.exp_neg]
  have hBhi : B = Real.exp |D| * Real.exp |D| := by
    dsimp [B]
    rw [show 2 * |D| = |D| + |D| by ring, Real.exp_add]
  constructor
  · calc
      B⁻¹ * (C⁻¹ * Elo * l₂) =
          Real.exp (-|D|) * (C⁻¹ * Elo *
            (Real.exp (-|D|) * l₂)) := by rw [hBlo]; ring
      _ ≤ Real.exp (-|D|) * (C⁻¹ * Elo * L₂) := by
        gcongr
      _ ≤ Real.exp (-|D|) * L₁ := by
        gcongr
      _ ≤ l₁ := hD1
  · calc
      l₁ ≤ Real.exp |D| * L₁ := hD1'
      _ ≤ Real.exp |D| * (C * Ehi * L₂) := by
        gcongr
      _ ≤ Real.exp |D| * (C * Ehi *
            (Real.exp |D| * l₂)) := by
        gcongr
      _ = B * (C * Ehi * l₂) := by rw [hBhi]; ring

end SupercriticalLQGUniqueness.B2.DG20Pt
