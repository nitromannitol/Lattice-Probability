import LatticeProb.Walk.UniformVertexCellNetworkStoppedCollar
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton

/-! # Uniform stopped-collar comparison for finite cell networks -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open scoped unitInterval ENNReal NNReal

universe u

namespace LatticeProb

/-- Cell diameter bounds yield the pre-exit mesh in a uniform stopped-collar
comparison. Cell errors, Brownian oscillation and the active tail are budgeted
separately; the Brownian reconstruction adds its active-clock tail. -/
theorem uniform_vertex_cellNetwork_stopped_collar_brownian_all_indices
    {U : Set (Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath 2)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ c > 0, ∀ (J : Type u) [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)],
    ∀ a e δ : ℝ, 0 ≤ a → 0 < e → a + e ≤ c → 0 < δ → δ ≤ c →
    ∀ T : Set (Euc 2), Bornology.IsBounded T → U ⊆ T → ∀ margin : ℝ, 0 < margin →
    ∃ n : ℕ, ∀ (V : Type*) [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
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
    (_hbudget : ((n + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
      (ENNReal.ofReal τ + (n + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞))
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
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) + ENNReal.ofReal τ := by
  obtain ⟨c, hc, hcprop⟩ :=
    uniform_vertex_cellNetwork_stopped_collar_cell_errors_all_indices hL hU hUb μ hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro J _ _ _ a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  obtain ⟨n, hn⟩ := hcprop J a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  refine ⟨n, ?_⟩
  intro V _ _ _ H hH rep hrep cell N hedge q hinj B hB W hW hWb select hs m E hE hdE A hBA hA haccess
    initial v z P p hsub hUpos mesh R S hmesh hbuffer hpq hdiam hnear hpoint
    hwrange hbrange choice hselect b hb hinside hcover herror hz hinit hWT hzU
    hmargin hnone φ hφ Wmesh scale diameter hscale hdiameter hp hcellBuffer
    hcellMesh hstepMesh r hbudget hsmall
  obtain ⟨htail, ρ, hρprob, hρfst, hρjoint, hρsnd, hcomparison⟩ :=
    hn V H hH rep hrep cell N hedge q hinj B hB W hW hWb select hs m E hE hdE
      hBA hA haccess initial v z P p hsub hUpos hmesh hbuffer hpq hdiam hnear
      hpoint hwrange hbrange choice hselect hb hinside hcover herror hz hinit hWT
      hzU hmargin hnone φ hφ Wmesh scale diameter hscale hdiameter hp hcellBuffer
      hcellMesh hstepMesh r hbudget hsmall
  refine ⟨htail, ρ, hρprob, hρfst, hρjoint, hρsnd, ?_⟩
  have hnone' : ∀ i x, brownianSelectorForWalk select i x = none → x ∉ U := by
    intro i x hn hx
    exact hnone (i - 1) x hn (self_subset_thickening hδ U hx)
  have hr : (0 : ℝ≥0) < τ.toNNReal := Real.toNNReal_pos.mpr hτ
  have hright : levyProkhorovEDist
      (((μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P)).map
          (unitCurveExitProjection U)) (stoppedBrownianLaw U z μ) ≤ ENNReal.ofReal τ := by
    rw [levyProkhorovEDist_comm]
    rw [Measure.map_map (measurable_unitCurveExitProjection hU) (measurable_pastedBrownianCurve P)]
    change levyProkhorovEDist (stoppedBrownianLaw U z μ)
      ((μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map
          (reconstructedBrownianStoppedCurve U P)) ≤ ENNReal.ofReal τ
    have hrec := levyProkhorov_stoppedBrownian_reconstruction_le (by omega) hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1)) hU hnone' n P τ.toNNReal hr
      (by simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal τ (le_of_lt hτ)] using htail)
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal τ (le_of_lt hτ)] using hrec
  exact (levyProkhorovEDist_triangle _ _ _).trans (add_le_add hcomparison hright)

end LatticeProb
end
