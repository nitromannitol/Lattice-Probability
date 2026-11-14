/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingUpperAll at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingCoarseTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_upper_tail_all_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      P {ω | ¬ lfppDOn (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) ≤
          ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
        ENNReal.ofReal ε := by
  obtain ⟨k₀, Mfine, hMfine, hfine⟩ :=
    pt_dist_moving_upper_tail_small_of_inputs
      hPerc hExp hPos ξ Q hQ U hU hUc z w hz hw ε hε
  have hcoarse (n : ℕ) : ∃ M : ℝ, 0 < M ∧
      ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
        P {ω | ¬ lfppDOn (ξ : ℝ)
          (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w) ≤
            ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
          ENNReal.ofReal ε :=
    pt_dist_moving_fixed_scale_upper_tail_small
      P W hW ξ U hU hUc z w hz hw n ε hε
  choose Mc hMc using hcoarse
  let M : ℝ := Mfine + ∑ n ∈ Finset.range k₀, Mc n
  have hsum : 0 ≤ ∑ n ∈ Finset.range k₀, Mc n :=
    Finset.sum_nonneg fun n _ => (hMc n).1.le
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨M, hM, ?_⟩
  intro n r hr1 hr2
  have hlam : 0 ≤ lambdaN ξ W P n := (lambdaN_pos hW n).le
  have hmono (m : ℝ) (hm : m ≤ M) :
      P {ω | ¬ lfppDOn (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) ≤
          ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
      P {ω | ¬ lfppDOn (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) ≤
          ENNReal.ofReal (m * lambdaN ξ W P n)} := by
    apply measure_mono
    intro ω hω hgood
    exact hω (hgood.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hm hlam)))
  by_cases hn : k₀ ≤ n
  · have hm : Mfine ≤ M := by dsimp [M]; linarith
    exact (hmono Mfine hm).trans
      (hfine (Ω := Ω) P W hW n hn r hr1 hr2)
  · have hn' : n ∈ Finset.range k₀ := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hsingle : Mc n ≤ ∑ j ∈ Finset.range k₀, Mc j :=
      Finset.single_le_sum (fun j _ => (hMc j).1.le) hn'
    have hm : Mc n ≤ M := by dsimp [M]; linarith
    exact (hmono (Mc n) hm).trans ((hMc n).2 r hr1 hr2)

end SupercriticalLQGUniqueness.B2.DG20Pt
