import LatticeProb.Bonanno.BouRabeeGwynne.ActualStoppedLawComparison
import LatticeProb.Walk.FiniteSourceSharpMeshCurveLaw
import LatticeProb.Walk.NestedFrontierContinuousCurveLaw

/-! # Exit-curve comparison for nested finite-network laws -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov BouRabeeGwynne.FiniteConductanceNetwork
open scoped NNReal ENNReal unitInterval

namespace LatticeProb.CellConfigInterpolation

/-- A stopped Brownian comparison under a larger active law controls the
continuous exit curve of the nested active law, with explicit error bounds. -/
theorem levyProkhorov_continuousExitCurve_le_of_nested_actual_source {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig)
    [Countable H.cells] [MeasurableSpace H.cells] [MeasurableSingletonClass H.cells]
    (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v)
    (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hpos : ∀ K, 0 < H.holding K) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (R : Set H.cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R)
    (hAB : ∀ v : R, v ∈ A ↔ (ε : ℝ) • p v ∈ U)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance v)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → H.c v w = 0)
    (hpaths : ∀ v ∈ A, ∃ w : H.cells, (ε : ℝ) • p w ∉ U ∧
      Relation.ReflTransGen (fun x y : H.cells => 0 < H.c x y) (v : H.cells) w)
    (C : Set R) (hAC : A ⊆ C)
    (hC : ∀ v ∈ C, 0 < (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance v)
    (v : R) (hv : v ∈ A) (P : Measure (ℕ → H.cells))
    (hP : P = ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
      (fun q n => (q n : H.cells)))
    (W : Set Plane) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ U, Metric.closedBall x ((ε : ℝ) * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), (ε : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (q : R → Plane) (z : Plane) (μ : Measure (BrownianPath 2))
    (d : ℝ) (r : ℝ≥0)
    (hd : ∀ x : R, dist ((ε : ℝ) • p x) (q x) ≤ d) (hdr : d < (r : ℝ))
    (n : ℕ)
    (hbound : ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw C hC v)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω} +
      ∑ k ∈ Finset.range n, ((finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw C hC v)
        {ω | q (ω k) ∈ Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞))
    (hinj : Function.Injective q)
    (N : FiniteConductanceNetwork R)
    (hN : N = finiteConductanceRestriction (fun v w : H.cells => H.c v w)
      hsymm hnonneg hloop R)
    (B : J → Set R) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (Wsrc : J → Set (Plane)) (hWsrc : ∀ j, IsOpen (Wsrc j))
    (hWbsrc : ∀ j, Bornology.IsBounded (Wsrc j))
    [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Plane → Option J) (hs : ∀ i, Measurable (select i))
    (mExc : ℕ → ℕ) (E : ∀ i, Fin (mExc i) → Set (Plane))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    (hBC : ∀ j, B j ⊆ C) (hNC : ∀ x ∈ C, 0 < N.totalConductance x)
    (haccess : N.BoundaryAccessible C)
    (initial : J) (nExc : ℕ) (T : TimePartition nExc)
    {a Rsrc S εSrc meshSrc δSrc η : ℝ}
    (hεSrc : 0 < εSrc) (hmeshSrc : 0 ≤ meshSrc) (hbufferSrc : εSrc + meshSrc < δSrc)
    (hnone : ∀ i x, select i x = none → x ∉ Metric.thickening δSrc U)
    (hdiam : ∀ i ≤ nExc, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnearSrc : dist (q v) z ≤ a) (hpointSrc : Rsrc + a + S ≤ εSrc)
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw C hNC v, ∀ k,
      dist (q (ω k)) (q (ω (k + 1))) ≤ meshSrc)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw C hNC v, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence q B initial select ω i).2 ∈
        curveOscillationLe Rsrc)
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion Wsrc z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S)
    {b c o : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw q hinj B hB Wsrc hWsrc μ select hs mExc E hE hdE initial v z
      {p | ∃ i ≤ nExc, (p.1 i, p.2 i) ∉ goodExcursionPair q (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion Wsrc z initial
      (brownianSelectorForWalk select) nExc ω).1 = false} ≤ c)
    (hosc : μ {ω | T.concatenate (ExcursionTrajectory.prefixChain nExc 2
      (fun k => (brownianSkeletonExcursion Wsrc z initial
        (brownianSelectorForWalk select) k ω).2)) ∈
      unitCurveExitOscillationBad (innerDomain U εSrc) (Metric.thickening δSrc U) η} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (εSrc + η) < (rMiddle : ℝ≥0∞)) :
    levyProkhorovEDist
      (P.map (fun ω : ℕ → H.cells =>
        let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))) (stoppedBrownianLaw U z μ) ≤
      ENNReal.ofReal (4 * ((ε : ℝ) * δ)) + ((r + (rWalk + rMiddle + rBrownian) : ℝ≥0) : ℝ≥0∞) := by
  subst N
  have hsource := (finiteConductanceRestriction (fun v w : H.cells => H.c v w)
    hsymm hnonneg hloop R).levyProkhorov_actual_stopped_laws_le
    (by decide) q hinj B hB Wsrc hWsrc hWbsrc μ hμ select hs mExc E hE hdE
    hBC hNC haccess initial v z nExc T hU hεSrc hmeshSrc hbufferSrc
    hnone hdiam hnearSrc hpointSrc hsteps hwrange hbrange hfailure htail hosc
    rWalk rMiddle rBrownian hrWalk hrBrownian hwalkBudget hbrownianBudget hmiddleBudget hsmall
  exact levyProkhorov_continuousExitCurve_le_of_nested_frontier_finite_source
    H hH hsymm hnonneg hloop p hp hpos hε hm hU hconv R A hAB hA hretain hpaths
    C hAC hC v hv P hP W δ hδ hbuffer hmesh q z μ d r
    (rWalk + rMiddle + rBrownian) hd hdr n hbound hsource

end LatticeProb.CellConfigInterpolation
end
