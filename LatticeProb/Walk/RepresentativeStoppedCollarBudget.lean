import LatticeProb.Walk.SourceRepresentativeStoppedLaw
import LatticeProb.Walk.ObservableStoppedCollar
import LatticeProb.Walk.StoppedSelectorCouplingPath

/-! # Representative stopped laws with a stopped collar budget -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal NNReal

namespace LatticeProb

/-- A stopped collar budget and pre-exit mesh bound give a representative
stopped-law comparison on the lifted coupling. -/
theorem exists_representativeStopped_coupling_of_stopped_collar_budget
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (hd : 1 ≤ d)
    (q : V → Euc d) (hinj : Function.Injective q)
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
    (p : V → Euc d) {U : Set (Euc d)} (hU : IsOpen U)
    (hsub : p ⁻¹' U ⊆ A) (hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v)
    {a e mesh δ η R S : ℝ} (ha : 0 ≤ a) (he : 0 < e) (hmesh : 0 ≤ mesh)
    (hbuffer : a + e + mesh < δ) (hpq : ∀ v, dist (p v) (q v) ≤ a)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (q v) z ≤ a) (hpoint : R + a + S ≤ e)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select ω i).2 ∈ curveOscillationLe R)
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S)
    (hnone : ∀ i x, select i x = none → x ∉ thickening δ U)
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
      (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω →
      dist (p (ω (j + 1))) (p (ω j)) ≤ mesh)
    (r : ℝ≥0)
    (hbudget : (N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE initial v z
        {x | ∃ i ≤ n, (x.1 i, x.2 i) ∉ goodExcursionPair q (E i) a} +
      μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad
          (innerDomain U (a + e)) (thickening δ U) η}) +
      (μ {ω | (brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) n ω).1 = false} +
      N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE initial v z
        {x | ∃ i ≤ n, (x.1 i, x.2 i) ∉ goodExcursionPair q (E i) a}) ≤ (r : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞)) :
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)),
      IsProbabilityMeasure ρ ∧ ρ.fst = N.trajectoryLaw A hA v ∧
      ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select x.1, x.2)) =
        (N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE initial v z).map
          (fun x => (x.1, pastedBrownianCurve P x.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P) ∧
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (((μ.map (fun ω k => brownianSkeletonExcursion W z initial
          (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P)).map
            (unitCurveExitProjection U)) ≤ (r : ℝ≥0∞) := by
  let T := pastedStoppedCollarBad P e (innerDomain U (a + e)) (thickening δ U) η
  have hT : MeasurableSet T :=
    measurableSet_pastedStoppedCollarBad P e (isOpen_innerDomain U (a + e)) isOpen_thickening η
  have hbad : ((N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE
      initial v z).map (fun x => (x.1, pastedBrownianCurve P x.2))) T ≤ (r : ℝ≥0∞) :=
    (pastedStoppedCollarBad_map_le N hd q hinj B hB W hW hWb μ hμ select hs m E hE hdE
      hBA hA haccess initial v z P (isOpen_innerDomain U (a + e)) isOpen_thickening
      (fun k x h => hnone (k - 1) x h) hdiam hnear hpoint hwrange hbrange).trans hbudget
  obtain ⟨ρ, hprob, hfst, hjoint, hsnd, hcompare⟩ :=
    exists_representativeStopped_coupling_of_observable_event N hd q hinj B hB W hW hWb
      μ hμ select hs m E hE hdE hBA hA haccess initial v z n P p hU hsub hUpos
      ha he hmesh hbuffer hpq T hT r hbad hsmall
  refine ⟨ρ, hprob, hfst, hjoint, hsnd, ?_⟩
  have haδ : a < δ := by linarith
  have hstop : ∀ᵐ x ∂ρ, x ∉ {x | (FiniteConductanceNetwork.actualWalkExcursionSequence
      q B initial select x.1, x.2) ∈ T} →
      (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).2.1 = true ∧
      ∃ t, x.2 t ∉ thickening δ U := by
    filter_upwards with x hx
    have hgood := pastedStoppedCollar_good_of_not_mem P hx
    exact ⟨hgood.2.2.1, 1, hgood.2.2.2⟩
  have hpath := representativeCoupling_goodPath_of_stopped_stage N p q B hBA hA haccess
    initial select v n ρ hfst U haδ hpq hnone hsteps
    {x | (FiniteConductanceNetwork.actualWalkExcursionSequence q B initial select x.1, x.2) ∈ T}
    hstop
  apply hcompare
  filter_upwards [hpath] with x hx hnot
  obtain ⟨hstage, k, hk, hexit, hmesh', hout⟩ := hx hnot
  have hgood := pastedStoppedCollar_good_of_not_mem P hnot
  exact ⟨hstage, k, hk, hexit, hmesh', hgood.1, hout, hgood.2.1⟩

end LatticeProb
end
