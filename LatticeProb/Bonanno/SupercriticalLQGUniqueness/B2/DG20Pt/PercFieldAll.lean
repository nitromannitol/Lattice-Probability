/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldAll at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldUnboundedLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldUnboundedUpper

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem perc_field_all_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Opens ℂ) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (hconnU : IsConnected (U : Set ℂ)) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
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
  obtain ⟨a₀, b₀, ha₀, hb₀, hlow⟩ :=
    perc_field_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ U K₁ K₂
      hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  obtain ⟨a₁, b₁, ha₁, hb₁, hhigh⟩ :=
    perc_field_upper_of_inputs hPerc hExp ξ Q hQ ζ hζ U K₁ K₂
      hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  let a := a₀ + a₁
  let b := min b₀ b₁
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := lt_min hb₀ hb₁
  refine ⟨a, b, ha, hb, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  have hl := hlow P W hW n k hkn T hT
  have hh := hhigh P W hW n k hkn T hT
  have hLLT : 0 < Real.log (Real.log T) := by
    have hlogT1 : 1 < Real.log T :=
      (Real.lt_log_iff_exp_lt (by linarith : 0 < T)).2
        (lt_trans Real.exp_one_lt_three hT)
    exact Real.log_pos hlogT1
  have hgauss :
      a₀ * Real.exp (-b₀ * (Real.log T) ^ 2) ≤
        a * Real.exp (-b * (Real.log T) ^ 2) := by
    have hrate : b * (Real.log T) ^ 2 ≤ b₀ * (Real.log T) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    calc
      _ ≤ a₀ * Real.exp (-b * (Real.log T) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ha₀.le
      _ ≤ a * Real.exp (-b * (Real.log T) ^ 2) :=
        mul_le_mul_of_nonneg_right (by dsimp [a]; linarith [ha₁]) (Real.exp_nonneg _)
  have hloglog :
      a₁ * Real.exp (-b₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) ≤
        a * Real.exp (-b * (Real.log T) ^ 2 / Real.log (Real.log T)) := by
    have hrate : b * (Real.log T) ^ 2 / Real.log (Real.log T) ≤
        b₁ * (Real.log T) ^ 2 / Real.log (Real.log T) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)) hLLT.le
    calc
      _ ≤ a₁ * Real.exp (-b * (Real.log T) ^ 2 / Real.log (Real.log T)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          calc
            -b₁ * (Real.log T) ^ 2 / Real.log (Real.log T) =
                -(b₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) := by ring
            _ ≤ -(b * (Real.log T) ^ 2 / Real.log (Real.log T)) := neg_le_neg hrate
            _ = -b * (Real.log T) ^ 2 / Real.log (Real.log T) := by ring)) ha₁.le
      _ ≤ a * Real.exp (-b * (Real.log T) ^ 2 / Real.log (Real.log T)) :=
        mul_le_mul_of_nonneg_right (by dsimp [a]; linarith [ha₀]) (Real.exp_nonneg _)
  dsimp at hl hh ⊢
  constructor
  · exact hl.trans (ENNReal.ofReal_le_ofReal hgauss)
  · exact hh.trans (ENNReal.ofReal_le_ofReal hloglog)

end SupercriticalLQGUniqueness.B2.DG20Pt

