/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossPercAdapter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossStrip
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BoxSideGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem square_cross_upper_tail_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Opens ℂ) (A B : Set ℂ)
    (hAc : IsCompact A) (hBc : IsCompact B)
    (hAi : IsConnected A) (hBi : IsConnected B)
    (hAn : A.Nontrivial) (hBn : B.Nontrivial)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hAB : Disjoint A B)
    (hUc : IsConnected (U : Set ℂ))
    (hStrip : ∀ z ∈ U, z.im ∈ Icc (0 : ℝ) 1)
    (hLeft : ∀ z ∈ A, z.re ≤ 0)
    (hRight : ∀ z ∈ B, 1 ≤ z.re) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          P {ω | T * lambdaN ξ W P n <
            lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    hPerc ξ U A B hAc hBc hAi hBi hAn hBn hAU hBU hAB hUc
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n T hT
  have hv := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hsub :
      {ω | T * lambdaN ξ W P n < lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} ⊆
      {ω | ENNReal.ofReal (T * lambdaN ξ W P n) <
        crossLenIn ξ (fun z => phiMN W P 0 n z ω) U A B} := by
    intro ω hω
    have hlen : 0 < lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω :=
      lenObs_pos hv.cont (rectAB 1 1)
        (by norm_num [rectAB]) (by norm_num [rectAB])
        (by norm_num [rectAB, MarkedRect.crossWidth]) ω
    have hreal : ENNReal.ofReal (T * lambdaN ξ W P n) <
        ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω) :=
      (ENNReal.ofReal_lt_ofReal_iff hlen).2 hω
    rw [ofReal_lenObs hv.cont (rectAB 1 1)
      (by norm_num [rectAB]) (by norm_num [rectAB]) ω] at hreal
    exact hreal.trans_le
      (rectLen_unit_le_crossLenIn_strip ξ
        (fun z => phiMN W P 0 n z ω) U A B hStrip hLeft hRight)
  exact (measure_mono hsub).trans (htail P W hW n T hT).2

 

theorem square_cross_lower_tail_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Opens ℂ) (A B : Set ℂ)
    (hAc : IsCompact A) (hBc : IsCompact B)
    (hAi : IsConnected A) (hBi : IsConnected B)
    (hAn : A.Nontrivial) (hBn : B.Nontrivial)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hAB : Disjoint A B)
    (hUc : IsConnected (U : Set ℂ))
    (hSq : (rectAB 1 1).toSet ⊆ U)
    (hLeft : (rectAB 1 1).side₁ ⊆ A)
    (hRight : (rectAB 1 1).side₂ ⊆ B) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
            T⁻¹ * lambdaN ξ W P n} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    hPerc ξ U A B hAc hBc hAi hBi hAn hBn hAU hBU hAB hUc
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n T hT
  have hv := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hq : 0 < T⁻¹ * lambdaN ξ W P n :=
    mul_pos (inv_pos.mpr (by linarith)) (lambdaN_pos hW n)
  have hsub :
      {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
        T⁻¹ * lambdaN ξ W P n} ⊆
      {ω | crossLenIn ξ (fun z => phiMN W P 0 n z ω) U A B <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    have hreal : ENNReal.ofReal
        (lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω) <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n) :=
      (ENNReal.ofReal_lt_ofReal_iff hq).2 hω
    rw [ofReal_lenObs hv.cont (rectAB 1 1)
      (by norm_num [rectAB]) (by norm_num [rectAB]) ω] at hreal
    exact (crossLenIn_le_rectLen_unit ξ
      (fun z => phiMN W P 0 n z ω) U A B hSq hLeft hRight).trans_lt hreal
  exact (measure_mono hsub).trans (htail P W hW n T hT).1

end SupercriticalLQGUniqueness.B2.DG20Pt
