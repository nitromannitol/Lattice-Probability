import LatticeProb.Walk.ShiftedBrownianOscillation
import LatticeProb.Walk.RepresentativeCollarCellError

/-! # Uniform Brownian bounds over finite vertex types -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal NNReal

namespace LatticeProb

/-- The Brownian oscillation budget can be chosen uniformly before the
network, domains and selectors in the representative stopped-law comparison. -/
theorem uniform_vertex_representativeStopped_coupling_of_cell_errors
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {U : Set (Euc d)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ c > 0, ∀ a e δ : ℝ, 0 ≤ a → 0 < e → a + e ≤ c → 0 < δ → δ ≤ c →
    ∀ T : Set (Euc d), Bornology.IsBounded T → U ⊆ T → ∀ margin : ℝ, 0 < margin →
    ∃ n : ℕ, ∀ (V : Type*) [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V)
    (q : V → Euc d) (hinj : Function.Injective q)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (_hWb : ∀ j, Bornology.IsBounded (W j))
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (_hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (_haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) (P : TimePartition n)
    (p : V → Euc d)
    (_hsub : p ⁻¹' U ⊆ A) (hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v)
    {mesh R S : ℝ} (_hmesh : 0 ≤ mesh)
    (_hbuffer : a + e + mesh < δ) (_hpq : ∀ v, dist (p v) (q v) ≤ a)
    (_hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (_hnear : dist (q v) z ≤ a) (_hpoint : R + a + S ≤ e)
    (_hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select ω i).2 ∈ curveOscillationLe R)
    (_hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S)
    (choice : ∀ i, Fin (m i) → Option J)
    (_hselect : ∀ i, select i = cellSelector (E i) (choice i))
    {b : ℝ} (_hb : 0 ≤ b)
    (_hinside : ∀ i < n, ∀ k j, choice i k = some j → E i k ⊆ W j)
    (_hcover : ∀ i ≤ n, ∀ j, closure (W j) ⊆ ⋃ k, E i k)
    (_herror : ∀ i < n, ∀ k j, choice i k = some j →
      ∀ w : V, q w ∈ E i k → ∀ y ∈ E i k, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) w).map q) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1))
    (_hz : z ∈ W initial)
    (_hinit : ∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map q)
      (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint)
        (E 0 i)).toReal| ≤ b / (m 0 + 1))
    (_hWT : ∀ j, W j ⊆ T) (_hzU : z ∈ U)
    (_hmargin : ∀ k x j, select k x = some j → ball x (margin / 2) ⊆ W j)
    (_hnone : ∀ k x, select k x = none → x ∉ thickening δ U)
    (r : ℝ≥0)
    (_hbudget : (n + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ) ≤ (r : ℝ≥0∞))
    (_hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞)),
    μ {ω | (brownianSkeletonClock W z initial (brownianSelectorForWalk select) n ω).1 =
      false} ≤ ENNReal.ofReal τ ∧
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
  obtain ⟨c, hc, hcprop⟩ := uniform_shiftedBrownianSkeleton_probability (J := J)
    hd hL hU hUb hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  obtain ⟨n, hn⟩ := hcprop (a + e) (by linarith) hae δ hδ hδc T hT hUT margin hmarginpos
  refine ⟨n, ?_⟩
  intro V _ _ _ N q hinj B hB W hW hWb select hs m E hE hdE A hBA hA haccess
    initial v z P p hsub hUpos mesh R S hmesh hbuffer hpq hdiam hnear
    hpoint hwrange hbrange choice hselect b hb hinside hcover herror hz hinit
    hWT hzU hmargin hnone r hbudget hsmall
  have hp := hn W hW hWT z hzU initial select hs hmargin hnone P
  refine ⟨hp.1, ?_⟩
  exact exists_representativeStopped_coupling_of_cell_errors N hd q hinj B hB W hW hWb
    μ hμ select hs m E hE hdE hBA hA haccess initial v z n P p hU hsub hUpos
    ha he hmesh hbuffer hpq hdiam hnear hpoint hwrange hbrange choice hselect
    hb hinside hcover herror hz hinit hp.2 r hbudget hsmall

end LatticeProb
end
