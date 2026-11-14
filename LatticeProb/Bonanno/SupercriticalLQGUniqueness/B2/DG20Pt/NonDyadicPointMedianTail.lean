/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointMedianTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointLambdaTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMedianNormCompare

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_median_tails
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U)
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
  let ε₀ : ℝ := ε / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  obtain ⟨c, hc⟩ := dg20_non_dyadic_median_compare_uniform_of_perc hPerc ξ
  let C : ℝ := Real.exp c
  have hC : 0 < C := Real.exp_pos c
  obtain ⟨M₀, hM₀, htail⟩ :=
    dg20_non_dyadic_point_lambda_tails hPerc hExp hPos
      ξ Q hQ P W hW U hU hUc hUb z w hz hw hzw ε₀ hε₀
  refine ⟨C * M₀, mul_pos hC hM₀, ?_⟩
  intro n s hs hs1
  dsimp only
  let δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + s))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hlam : 0 < lambdaN ξ W P n := lambdaN_pos hW n
  have hratio := hc P W hW n s hs.le hs1
  have hLow : C⁻¹ * lambdaN ξ W P n ≤ lambdaDelta ξ W P δ := by
    simpa only [C, Real.exp_neg] using hratio.1
  have hHigh : lambdaDelta ξ W P δ ≤ C * lambdaN ξ W P n := hratio.2
  have hδlam : 0 < lambdaDelta ξ W P δ :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hC) hlam) hLow
  let D : Ω → ℝ≥0∞ := fun ω => lfppDOn (ξ : ℝ)
    (fun y => phiVer W P δ 1 y ω) U z w
  let X : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (lambdaN ξ W P n)⁻¹ * D ω
  let Y : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (lambdaDelta ξ W P δ)⁻¹ * D ω
  have hcomp (ω : Ω) :
      Y ω ≤ ENNReal.ofReal C * X ω ∧
      X ω ≤ ENNReal.ofReal C * Y ω :=
    dg20_point_norm_compare_of_median_ratio
      (lambdaN ξ W P n) (lambdaDelta ξ W P δ) C
      hlam hδlam hC hLow hHigh (D ω)
  have hcmp : P {ω | ¬
      (Y ω ≤ ENNReal.ofReal C * X ω ∧
       X ω ≤ ENNReal.ofReal C * Y ω)} ≤
      ENNReal.ofReal ε₀ := by
    have hsub : {ω | ¬
        (Y ω ≤ ENNReal.ofReal C * X ω ∧
         X ω ≤ ENNReal.ofReal C * Y ω)} ⊆ ∅ := by
      intro ω hbad
      exact hbad (hcomp ω)
    exact (measure_mono hsub).trans (by simp)
  have hX := htail n s hs hs1
  have htrans := two_sided_tail_of_probabilistic_compare
    P X Y C M₀ ε₀ hC hM₀ hX.1 hX.2 hcmp
  have hsum : ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε₀.le hε₀.le]
    congr 1
    dsimp [ε₀]
    ring
  change P {ω | ENNReal.ofReal (C * M₀) < Y ω} ≤
      ENNReal.ofReal ε ∧
    P {ω | Y ω < ENNReal.ofReal (C * M₀)⁻¹} ≤
      ENNReal.ofReal ε
  simpa only [hsum] using htrans

end SupercriticalLQGUniqueness.B2.DG20Pt
