import LatticeProb.Bonanno.BouRabeeGwynne.ActualStoppedLawComparison
import LatticeProb.Walk.NestedFrontierStoppedBrownianLaw

/-! # Nested stopped laws from excursion comparisons -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- The excursion comparison for an outer walk controls the stopped curve of
an inner walk, with the frontier and exit-tail errors made explicit. -/
theorem levyProkhorov_nested_actual_stopped_laws_le (N : FiniteConductanceNetwork V)
    (hd : 1 ≤ d) (pos : V → Euc d) (hinj : Function.Injective pos)
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
    (initial : J) (v : V) (z : Euc d) (n : ℕ) (P : TimePartition n)
    {U : Set (Euc d)} (hU : IsOpen U) {a R S ε mesh δ η : ℝ}
    (hε : 0 < ε) (hmesh : 0 ≤ mesh) (hbuffer : ε + mesh < δ)
    (hnone : ∀ i x, select i x = none → x ∉ Metric.thickening δ U)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a) (hpoint : R + a + S ≤ ε)
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ k,
      dist (pos (ω k)) (pos (ω (k + 1))) ≤ mesh)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω i).2 ∈
        curveOscillationLe R)
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S)
    {b c o : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (hosc : μ {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => (brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω).2)) ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (ε + η) < (rMiddle : ℝ≥0∞))
    (p : V → Euc d) (hsub : p ⁻¹' U ⊆ A)
    (hinner : ∀ x ∈ p ⁻¹' U, 0 < N.totalConductance x)
    (D : ℝ) (r : ℝ≥0) (hdist : ∀ x, dist (p x) (pos x) ≤ D)
    (hdr : D < (r : ℝ)) (nFront : ℕ)
    (hbound : (N.trajectoryLaw A hA v)
        {ω | (nFront : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (pos ⁻¹' U) ω} +
      ∑ k ∈ Finset.range nFront, (N.trajectoryLaw A hA v)
        {ω | pos (ω k) ∈ Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist
      ((N.trajectoryLaw (p ⁻¹' U) hinner v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤
      (r : ℝ≥0∞) + ((rWalk + rMiddle + rBrownian : ℝ≥0) : ℝ≥0∞) := by
  have hsource := N.levyProkhorov_actual_stopped_laws_le hd pos hinj B hB W hW hWb
    μ hμ select hs m E hE hdE hBA hA haccess initial v z n P hU hε hmesh hbuffer
    hnone hdiam hnear hpoint hsteps hwrange hbrange hfailure htail hosc
    rWalk rMiddle rBrownian hrWalk hrBrownian hwalkBudget hbrownianBudget hmiddleBudget hsmall
  exact LatticeProb.levyProkhorov_nested_stoppedBrownian_le_of_frontier_cutoff
    N A hA v p pos U z hsub hinner μ D r hdist hdr nFront hbound
    ((rWalk + rMiddle + rBrownian : ℝ≥0) : ℝ≥0∞) hsource

end BouRabeeGwynne.FiniteConductanceNetwork
end
