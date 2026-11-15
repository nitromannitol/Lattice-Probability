import LatticeProb.Walk.UniformRepresentativeBrownianPath
import LatticeProb.Walk.CellNetworkLocalPreExitMesh

/-! # Uniform stopped-curve comparison for finite cell networks -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open scoped unitInterval ENNReal NNReal

namespace LatticeProb

/-- Local cell diameters bound the walk steps in a uniform stopped-curve
comparison. The coupled exit-index and outer-collar conditions remain explicit. -/
theorem uniform_cellNetwork_stopped_brownian_of_local_mesh
    {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    {U : Set (Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath 2)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ c > 0, ∀ a e δ : ℝ, 0 ≤ a → 0 < e → a + e ≤ c → 0 < δ → δ ≤ c →
    ∀ T : Set (Euc 2), Bornology.IsBounded T → U ⊆ T → ∀ margin : ℝ, 0 < margin →
    ∃ n : ℕ, ∀
    (H : CellConfig) (_hH : H.IsCellConfiguration)
    (rep : H.cells → Plane) (_hrep : ∀ C, rep C ∈ (C.1 : Set Plane))
    (cell : V → H.cells) (N : FiniteConductanceNetwork V)
    (_hedge : ∀ v w, 0 < N.a v w → H.Adj (cell v) (cell w))
    (q : V → Euc 2) (hinj : Function.Injective q)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc 2)) (hW : ∀ j, IsOpen (W j))
    (_hWb : ∀ j, Bornology.IsBounded (W j))
    (select : ℕ → Euc 2 → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc 2))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (_hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (_haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc 2) (P : TimePartition n)
    (p : V → Euc 2)
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
    (φ : Plane → Euc 2) (_hφ : Isometry φ) (Wmesh : Set Plane)
    (scale diameter : ℝ) (_hscale : 0 ≤ scale) (_hdiameter : 0 ≤ diameter)
    (_hp : p = fun x : V => φ (scale • rep (cell x)))
    (_hcellBuffer : ∀ x ∈ φ ⁻¹' U, Metric.closedBall x (scale * diameter) ⊆ Wmesh)
    (_hcellMesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane), scale • z ∈ Wmesh) →
      Metric.diam (C.1 : Set Plane) ≤ diameter)
    (_hstepMesh : 2 * (scale * diameter) ≤ mesh)
    (r : ℝ≥0)
    (_hbudget : (n + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ) ≤ (r : ℝ≥0∞))
    (_hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞)),
    μ {ω | (brownianSkeletonClock W z initial (brownianSelectorForWalk select) n ω).1 =
      false} ≤ ENNReal.ofReal τ ∧
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, Euc 2)),
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
        ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
          (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        ∃ t, x.2 t ∉ thickening δ U) →
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) + ENNReal.ofReal τ) := by
  obtain ⟨c, hc, hcprop⟩ := uniform_representativeStopped_brownian_of_marginal_steps
    (d := 2) (V := V) (J := J) (by omega) hL hU hUb μ hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  obtain ⟨n, hn⟩ := hcprop a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  refine ⟨n, ?_⟩
  intro H hH rep hrep cell N hedge q hinj B hB W hW hWb select hs m E hE hdE A hBA hA haccess
    initial v z P p hsub hUpos mesh R S hmesh hbuffer hpq hdiam hnear hpoint
    hwrange hbrange choice hselect b hb hinside hcover herror hz hinit hWT hzU
    hmargin hnone φ hφ Wmesh scale diameter hscale hdiameter hp hcellBuffer
    hcellMesh hstepMesh r hbudget hsmall
  have hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
      (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω →
      dist (p (ω (j + 1))) (p (ω j)) ≤ mesh := by
    subst p
    filter_upwards [CellConfigInterpolation.trajectoryLaw_ae_preExit_step_le_local_mesh
      H hH rep hrep cell N hedge A hA v φ hφ U Wmesh scale diameter
      hscale hdiameter hcellBuffer hcellMesh] with ω hω
    intro j hj
    exact (hω j hj).trans hstepMesh
  exact hn N q hinj B hB W hW hWb select hs m E hE hdE hBA hA haccess
    initial v z P p hsub hUpos hmesh hbuffer hpq hdiam hnear hpoint hwrange
    hbrange choice hselect hb hinside hcover herror hz hinit hWT hzU hmargin
    hnone hsteps r hbudget hsmall

end LatticeProb
end
