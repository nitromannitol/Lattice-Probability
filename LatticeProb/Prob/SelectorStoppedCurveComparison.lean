import LatticeProb.Prob.SelectorBrownianStoppedEndpoint
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteStoppedCurveComparison

/-! # Stopped curves under a joint excursion law -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- On a full-measure event for the joint excursion law, a stopped Brownian
prefix can be compared to every nearby walk prefix satisfying the stated
vertex-exit geometry and Brownian oscillation conditions. -/
theorem jointLaw_stopped_curve_comparison_of_selector
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
    (initial : J) (v : V) (z : Euc d) (U : Set (Euc d)) (hU : IsOpen U)
    {ε mesh δ η : ℝ} (hε : 0 < ε) (hmesh : 0 ≤ mesh) (hbuffer : ε + mesh < δ)
    (hactive : ∀ i x, x ∈ cthickening δ U → select i x ≠ none)
    (n : ℕ) (P : TimePartition n) :
    ∀ᵐ p ∂N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z,
      (p.2 n).1 = true →
      ∀ (f : C(unitInterval, Euc d)) (a : unitInterval),
        (∀ t, dist (f t) (P.concatenate
          (ExcursionTrajectory.prefixChain n d (fun k => (p.2 k).2)) t) ≤ ε) →
        (∀ t < a, f t ∈ cthickening mesh U) → f a ∉ U →
        P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (p.2 k).2)) ∉
          unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η →
        edist (BouRabeeGwynne.CurveSpace.project (prefixUnitCurve f a))
          (unitCurveExitProjection U (P.concatenate
            (ExcursionTrajectory.prefixChain n d (fun k => (p.2 k).2)))) ≤
          ENNReal.ofReal (ε + η) := by
  have hδ : 0 < δ := (add_pos_of_pos_of_nonneg hε hmesh).trans hbuffer
  have hend := jointLaw_brownian_stopped_endpoint_outside_thickening N hd pos hinj B hB
    W hW hWb μ hμ select hs m E hE hdE hBA hA haccess initial v z U hδ hactive n P
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hend] with p hp
  intro hflag f a hclose hpre hout hgood
  exact curveSpace_edist_prefix_unitExit_le_of_endpoint_outside hU f _ a
    hε hmesh hbuffer hclose hpre hout (hp hflag) hgood

end LatticeProb
