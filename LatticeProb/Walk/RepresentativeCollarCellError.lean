import LatticeProb.Walk.RepresentativeCollarBudget
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! # Representative stopped laws with cellwise errors -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal NNReal

namespace LatticeProb

/-- Endpoint cell estimates and a Brownian oscillation bound supply the
observable collar budget for the original-path representative comparison. -/
theorem exists_representativeStopped_coupling_of_cell_errors
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
    (choice : ∀ i, Fin (m i) → Option J)
    (hselect : ∀ i, select i = cellSelector (E i) (choice i))
    {b : ℝ} (hb : 0 ≤ b)
    (hinside : ∀ i < n, ∀ k j, choice i k = some j → E i k ⊆ W j)
    (hcover : ∀ i ≤ n, ∀ j, closure (W j) ⊆ ⋃ k, E i k)
    (herror : ∀ i < n, ∀ k j, choice i k = some j →
      ∀ w : V, q w ∈ E i k → ∀ y ∈ E i k, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) w).map q) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1))
    (hz : z ∈ W initial)
    (hinit : ∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map q)
      (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint)
        (E 0 i)).toReal| ≤ b / (m 0 + 1))
    {o : ℝ≥0∞}
    (hosc : μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad
          (innerDomain U (a + e)) (thickening δ U) η} ≤ o)
    (r : ℝ≥0)
    (hbudget : (n + 1 : ℝ≥0∞) * ENNReal.ofReal b + o ≤ (r : ℝ≥0∞))
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
          q B initial select x.1, x.2) ∉
            pastedCollarBad P e (innerDomain U (a + e)) (thickening δ U) η →
        (FiniteConductanceNetwork.actualWalkStage q B initial
          (fun i w => select i (q w)) n x.1).1 ≠ ⊤ ∧
        ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
          (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        (∀ j < k, dist (p (x.1 (j + 1))) (p (x.1 j)) ≤ mesh) ∧
        ∃ t, x.2 t ∉ thickening δ U) →
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (((μ.map (fun ω k => brownianSkeletonExcursion W z initial
          (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P)).map
            (unitCurveExitProjection U)) ≤ (r : ℝ≥0∞)) := by
  have hfailure := N.walkBrownianJointLaw_firstFailure_le hd q hinj B hB W hW hWb μ hμ
    select hs m E hE hdE choice hselect n hb hdiam hinside hcover herror initial v z hz hinit
  exact exists_representativeStopped_coupling_of_collar_budget N hd q hinj B hB W hW hWb
    μ hμ select hs m E hE hdE hBA hA haccess initial v z n P p hU hsub hUpos
    ha he hmesh hbuffer hpq hdiam hnear hpoint hwrange hbrange r
    ((add_le_add hfailure hosc).trans hbudget) hsmall

end LatticeProb
end
