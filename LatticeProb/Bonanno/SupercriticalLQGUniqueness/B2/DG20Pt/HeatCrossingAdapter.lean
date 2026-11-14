/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingAdapter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCrossingComparison

 

set_option autoImplicit false
noncomputable section

open Set LQGMetric LQGMetric.DDDF LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private lemma square_eq_rect :
    unitSquare = (rectAB 1 1).toSet := by
  ext z
  simp only [unitSquare, rectAB, MarkedRect.toSet, Complex.mem_reProdIm, Set.mem_Icc,
    zero_add, Set.mem_setOf_eq]
  tauto

private lemma left_eq_rect :
    LQGMetric.leftSide = (rectAB 1 1).side₁ := by
  ext z
  simp [LQGMetric.leftSide, rectAB, MarkedRect.side₁,
    Complex.mem_reProdIm, Set.mem_Icc]

private lemma right_eq_rect :
    LQGMetric.rightSide = (rectAB 1 1).side₂ := by
  ext z
  simp [LQGMetric.rightSide, rectAB, MarkedRect.side₂,
    Complex.mem_reProdIm, Set.mem_Icc]

theorem dg20_lfppCrossingLength_eq_rectLen (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    lfppCrossingLength ξ φ = rectLen ξ φ (rectAB 1 1) := by
  rw [rectLen, crossLenIn_eq_biInf]
  simp only [lfppCrossingLength, crossingLFPP]
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun P hP => ?_
    obtain ⟨z, hz, w, hw, hPW, hU⟩ := hP
    have hz0 : P 0 = z := hPW.source
    have hw1 : P 1 = w := hPW.target
    exact iInf₂_le P ⟨by simpa only [hz0, hw1] using hPW,
      by simpa only [hz0, left_eq_rect] using hz,
      by simpa only [hw1, right_eq_rect] using hw,
      by simpa only [square_eq_rect] using hU⟩
  · refine le_iInf₂ fun P hP => ?_
    exact (iInf₂_le P (show AdmPath (rectAB 1 1).toSet
      (rectAB 1 1).side₁ (rectAB 1 1).side₂ P from by
      refine ⟨P 0, ?_, P 1, ?_, hP.1, ?_⟩
      · simpa only [left_eq_rect] using hP.2.1
      · simpa only [right_eq_rect] using hP.2.2.1
      · simpa only [square_eq_rect] using hP.2.2.2))

theorem dg20_lfppCrossingLength_eq_ofReal_lenObs
    {Ω : Type*} (ξ : ℝ) (Y : Ω → C(ℂ, ℝ)) (ω : Ω) :
    lfppCrossingLength ξ (Y ω) =
      ENNReal.ofReal (lenObs ξ (fun z ω => Y ω z) (rectAB 1 1) ω) := by
  rw [dg20_lfppCrossingLength_eq_rectLen]
  exact (ofReal_lenObs (fun ω => (Y ω).continuous) (rectAB 1 1)
    (by norm_num [rectAB]) (by norm_num [rectAB]) ω).symm

theorem dg20_lfppCrossingLength_compare_of_square_sup
    (ξ : ℝ) (X Φ : C(ℂ, ℝ)) (M : ℝ)
    (hfield : ∀ z ∈ closedUnitSquare, |X z - Φ z| ≤ M) :
    lfppCrossingLength ξ X ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppCrossingLength ξ Φ ∧
      lfppCrossingLength ξ Φ ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppCrossingLength ξ X := by
  simpa only [dg20_lfppCrossingLength_eq_rectLen, rectLen,
    ← square_eq_rect, show closedUnitSquare = unitSquare from rfl] using
    dg20_heat_phi_crossLen_compare_on_compact ξ X Φ
      closedUnitSquare closedUnitSquare (rectAB 1 1).side₁
      (rectAB 1 1).side₂ M Subset.rfl hfield

end SupercriticalLQGUniqueness.B2.DG20Pt
