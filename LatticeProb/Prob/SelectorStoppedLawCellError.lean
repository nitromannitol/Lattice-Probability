import LatticeProb.Prob.SelectorStoppedLawComparison
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! # Stopped law comparison with finite coupling errors -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- A bound on the cellwise endpoint errors controls the finite coupling
failure in the stopped-law comparison. The reconstructed-law estimate is
retained as an explicit hypothesis. -/
theorem selector_stopped_laws_le_of_cell_errors
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
    (choice : ∀ i, Fin (m i) → Option J)
    (hselect : ∀ i, select i = cellSelector (E i) (choice i))
    {b : ℝ} (hb : 0 ≤ b)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hinside : ∀ i < n, ∀ k j, choice i k = some j → E i k ⊆ W j)
    (hcover : ∀ i ≤ n, ∀ j, closure (W j) ⊆ ⋃ k, E i k)
    (herror : ∀ i < n, ∀ k j, choice i k = some j →
      ∀ w : V, pos w ∈ E i k → ∀ y ∈ E i k, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) w).map pos) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1))
    (hz : z ∈ W initial)
    (hinit : ∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map pos)
      (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint)
        (E 0 i)).toReal| ≤ b / (m 0 + 1))
    {c : ℝ≥0∞}
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : c + (n + 1 : ℝ≥0∞) * ENNReal.ofReal b ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddle : levyProkhorovEDist
      ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).fst.map (reconstructedVertexStoppedCurve U n))
      ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).snd.map (reconstructedBrownianStoppedCurve U P)) ≤ rMiddle) :
    levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (rWalk + rMiddle + rBrownian : ℝ≥0) := by
  have hfailure := N.walkBrownianJointLaw_firstFailure_le hd pos hinj B hB W hW hWb μ hμ
    select hs m E hE hdE choice hselect n hb hdiam hinside hcover herror initial v z hz hinit
  exact selector_stopped_laws_le_of_reconstructed N hd pos hinj B hB W hW hWb μ hμ
    select hs m E hE hdE hBA hA haccess initial v z a n P U hU hδ hactive
    hfailure htail rWalk rMiddle rBrownian hrWalk hrBrownian hwalkBudget hbrownianBudget hmiddle

end LatticeProb
