/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointGeneralTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointUpperGeneral
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLowerMedian
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_general_tails
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
      let D := fun ω => lfppDOn (ξ : ℝ)
        (fun y => phiVer W P δ 1 y ω) U z w
      P {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω} ≤
        ENNReal.ofReal ε ∧
      P {ω | ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω <
        ENNReal.ofReal M⁻¹} ≤
        ENNReal.ofReal ε := by
  obtain ⟨Mup, hMup, hup⟩ :=
    dg20_non_dyadic_point_upper_general hPerc hExp hPos ξ Q hQ
      P W hW U hU hUc z w hz hw hzw ε hε
  obtain ⟨T, hT, hlow⟩ :=
    dg20_non_dyadic_point_lower_median_small hPerc ξ z w hzw ε hε
  let M : ℝ := max Mup T
  have hM : 0 < M := hMup.trans_le (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hδlt : δ < 1 := by
    dsimp [δ]
    exact (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).2
      (Or.inl ⟨by norm_num, by
        have hn := Nat.cast_nonneg (α := ℝ) n
        linarith⟩)
  have hLamD : 0 < lambdaDelta ξ W P δ :=
    LQGMetric.DDDF.S6Thm.lambdaDelta_pos_of_698 hW
      (dg20_non_dyadic_median_compare_of_perc hPerc ξ P W hW)
      ⟨hδ0, hδlt⟩
  let D : Ω → ℝ≥0∞ := fun ω =>
    lfppDOn (ξ : ℝ) (fun y => phiVer W P δ 1 y ω) U z w
  have hupperSub :
      {ω | ENNReal.ofReal M <
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω} ⊆
      {ω | ENNReal.ofReal Mup <
        ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω} := by
    intro ω hω
    exact (ENNReal.ofReal_le_ofReal (le_max_left Mup T)).trans_lt hω
  have hInv : M⁻¹ ≤ T⁻¹ :=
    inv_anti₀ (by linarith : 0 < T) (le_max_right Mup T)
  have hlowerSub :
      {ω | ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω <
        ENNReal.ofReal M⁻¹} ⊆
      {ω | D ω <
        ENNReal.ofReal (T⁻¹ * lambdaDelta ξ W P δ)} := by
    intro ω hω
    change ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω <
      ENNReal.ofReal M⁻¹ at hω
    exact pt_dist_rescale_lower_event
      (lambdaDelta ξ W P δ) T hLamD (by linarith) (D ω)
      (hω.trans_le (ENNReal.ofReal_le_ofReal hInv))
  exact ⟨(measure_mono hupperSub).trans (hup n s hs hs1),
    (measure_mono hlowerSub).trans (hlow P W hW U hU n s hs hs1)⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
