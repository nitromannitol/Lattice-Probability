import LatticeProb.Walk.ActualPastedCurveLift
import LatticeProb.Walk.RepresentativeCoupledStoppedLaw

/-! # Representative stopped laws and observable coupling events -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal NNReal

namespace LatticeProb

/-- The source excursion coupling lifts to the original walk and transfers an
observable exceptional event. The representative comparison applies whenever
the stated original-path conditions hold outside that event. -/
theorem exists_representativeStopped_coupling_of_observable_event
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
    {a e mesh δ η : ℝ} (ha : 0 ≤ a) (he : 0 < e) (hmesh : 0 ≤ mesh)
    (hbuffer : a + e + mesh < δ) (hpq : ∀ v, dist (p v) (q v) ≤ a)
    (S : Set ((ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)))
    (hS : MeasurableSet S) (r : ℝ≥0)
    (hbad : ((N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE
      initial v z).map (fun x => (x.1, pastedBrownianCurve P x.2))) S ≤ (r : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞)) :
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)),
      IsProbabilityMeasure ρ ∧ ρ.fst = N.trajectoryLaw A hA v ∧
      ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select x.1, x.2)) =
        (N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE initial v z).map
          (fun x => (x.1, pastedBrownianCurve P x.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P) ∧
      ((∀ᵐ x ∂ρ, (FiniteConductanceNetwork.actualWalkExcursionSequence
          q B initial select x.1, x.2) ∉ S →
        (FiniteConductanceNetwork.actualWalkStage q B initial
          (fun i w => select i (q w)) n x.1).1 ≠ ⊤ ∧
        ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
          (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        (∀ j < k, dist (p (x.1 (j + 1))) (p (x.1 j)) ≤ mesh) ∧
        (∀ t, dist (pastedWalkCurve P
          (FiniteConductanceNetwork.actualWalkExcursionSequence q B initial select x.1) t)
          (x.2 t) ≤ e) ∧
        (∃ t, x.2 t ∉ thickening δ U) ∧
        x.2 ∉ unitCurveExitOscillationBad (innerDomain U (a + e)) (thickening δ U) η) →
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (((μ.map (fun ω k => brownianSkeletonExcursion W z initial
          (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P)).map
            (unitCurveExitProjection U)) ≤ (r : ℝ≥0∞)) := by
  obtain ⟨ρ, hρprob, hρfst, hρjoint, hρsnd⟩ :=
    exists_actualWalk_pastedBrownian_joint_lift N hd q hinj B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA haccess initial v z P
  refine ⟨ρ, hρprob, hρfst, hρjoint, hρsnd, ?_⟩
  intro hgood
  have hobs : Measurable (fun x : (ℕ → V) × C(unitInterval, Euc d) =>
      (FiniteConductanceNetwork.actualWalkExcursionSequence q B initial select x.1, x.2)) :=
    ((FiniteConductanceNetwork.measurable_actualWalkExcursionSequence q B initial select).comp
      measurable_fst).prodMk measurable_snd
  have hbad' : ρ ((fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
      q B initial select x.1, x.2)) ⁻¹' S) ≤ (r : ℝ≥0∞) := by
    rw [← Measure.map_apply hobs hS, hρjoint]
    exact hbad
  have h := levyProkhorov_representativeStopped_le_of_coupling N p q B initial select n P hU
    hsub hA hUpos v ρ hρfst ha he hmesh hbuffer hpq
    ((fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
      q B initial select x.1, x.2)) ⁻¹' S) r hbad' hsmall hgood
  rw [hρsnd] at h
  exact h

end LatticeProb
end
