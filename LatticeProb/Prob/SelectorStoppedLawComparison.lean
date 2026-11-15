import LatticeProb.Prob.SelectorWalkReconstruction
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton

/-! # Stopped law comparison through excursion reconstructions -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- A comparison of reconstructed laws transfers to the original stopped laws,
with errors for the two reconstructions under the original joint marginals. -/
theorem selector_stopped_laws_le_of_reconstructed
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (hd : 1 ≤ d)
    (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) (a : ℝ) (n : ℕ) (P : TimePartition n)
    (U : Set (Euc d)) (hU : IsOpen U) {δ : ℝ} (hδ : 0 < δ)
    (hactive : ∀ i x, x ∈ cthickening δ U → select i x ≠ none)
    {b c : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : c + b ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddle : levyProkhorovEDist
      ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).fst.map (reconstructedVertexStoppedCurve U n))
      ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).snd.map (reconstructedBrownianStoppedCurve U P)) ≤ rMiddle) :
    levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (rWalk + rMiddle + rBrownian : ℝ≥0) := by
  have hnone : ∀ i x, brownianSelectorForWalk select i x = none → x ∉ U := by
    intro i x hn hx
    have hx' : x ∈ cthickening δ U := (Metric.self_subset_cthickening U) hx
    exact hactive (i - 1) x hx' hn
  have hleft := selector_stopped_walk_reconstruction_le N hd pos hinj B hB W hW hWb μ hμ
    select hs m E hE hdE hBA hA haccess initial v z a n U hU.measurableSet hδ
    hactive hfailure htail rWalk hrWalk hwalkBudget
  have hmarg := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  have hright : levyProkhorovEDist
      ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).snd.map (reconstructedBrownianStoppedCurve U P))
      (stoppedBrownianLaw U z μ) ≤ (rBrownian : ℝ≥0∞) := by
    rw [levyProkhorovEDist_comm, hmarg.2]
    apply levyProkhorov_stoppedBrownian_reconstruction_le hd hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1)) hU hnone n P rBrownian hrBrownian
    simpa only [brownianSkeletonExcursion_flag] using htail.trans hbrownianBudget
  have htriangle := (levyProkhorovEDist_triangle
    ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
    ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
      initial v z).fst.map (reconstructedVertexStoppedCurve U n)) (stoppedBrownianLaw U z μ)).trans
      (add_le_add hleft ((levyProkhorovEDist_triangle _ _ _).trans
        (add_le_add hmiddle hright)))
  simpa only [ENNReal.coe_add, add_assoc] using htriangle

end LatticeProb
