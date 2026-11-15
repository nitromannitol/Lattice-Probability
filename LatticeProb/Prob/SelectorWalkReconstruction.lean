import LatticeProb.Prob.SelectorStoppedWalkBudget
import LatticeProb.Bonanno.BouRabeeGwynne.WalkReconstructionLaw

/-! # Stopped walk reconstruction under a joint excursion law -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- Selector coverage and bounds on Brownian activity and joint coupling failure
control the distance between the stopped walk law and its finite reconstruction
under the walk marginal of the original joint excursion law. -/
theorem selector_stopped_walk_reconstruction_le
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
    (initial : J) (v : V) (z : Euc d) (a : ℝ) (n : ℕ)
    (U : Set (Euc d)) (hU : MeasurableSet U) {δ : ℝ} (hδ : 0 < δ)
    (hactive : ∀ i x, x ∈ cthickening δ U → select i x ≠ none)
    {b c : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (r : ℝ≥0) (hr : 0 < r) (hbudget : c + b ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).fst.map (reconstructedVertexStoppedCurve U n)) ≤ r := by
  obtain ⟨_, hselect, _, _, hwalk⟩ :=
    selector_stopping_and_walk_active_le N hd pos hinj B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA haccess initial v z a n U hδ hactive hfailure htail
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  rw [hm.1]
  exact N.trajectoryLaw_reconstructedStopped_le pos B hBA hA haccess initial select U hU
    hselect v n r hr (hwalk.trans hbudget)

end LatticeProb
