import LatticeProb.Walk.RepresentativePastedStopped
import LatticeProb.Walk.NestedStoppedCurveLaw
import LatticeProb.Bonanno.BouRabeeGwynne.ReconstructedLawComparison

/-! # Coupled laws of representative stopped curves -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory BouRabeeGwynne
open scoped unitInterval ENNReal NNReal

namespace LatticeProb

/-- An original-path coupling and a finite-stage collar estimate compare the
representative stopped walk law with the stopped law of the coupled curve.
The walk may be absorbed on a larger set than its representative exit set. -/
theorem levyProkhorov_representativeStopped_le_of_coupling
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (p q : V → Euc d)
    (B : J → Set V) (initial : J) (select : ℕ → Euc d → Option J)
    (n : ℕ) (P : TimePartition n) {U : Set (Euc d)} (hU : IsOpen U)
    {A : Set V} (hsub : p ⁻¹' U ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v) (v : V)
    (ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)))
    (hρ : ρ.fst = N.trajectoryLaw A hA v)
    {a e mesh δ η : ℝ} (ha : 0 ≤ a) (he : 0 < e) (hmesh : 0 ≤ mesh)
    (hbuffer : a + e + mesh < δ) (hpq : ∀ v, dist (p v) (q v) ≤ a)
    (E : Set ((ℕ → V) × C(unitInterval, Euc d))) (r : ℝ≥0)
    (hbad : ρ E ≤ (r : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞))
    (hgood : ∀ᵐ x ∂ρ, x ∉ E →
      (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1 ≠ ⊤ ∧
      ∃ m : ℕ, m ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
      FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (m : WithTop ℕ) ∧
      (∀ k < m, dist (p (x.1 (k + 1))) (p (x.1 k)) ≤ mesh) ∧
      (∀ t, dist (pastedWalkCurve P
        (FiniteConductanceNetwork.actualWalkExcursionSequence q B initial select x.1) t)
        (x.2 t) ≤ e) ∧
      (∃ t, x.2 t ∉ thickening δ U) ∧
      x.2 ∉ unitCurveExitOscillationBad (innerDomain U (a + e)) (thickening δ U) η) :
    levyProkhorovEDist
      ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (ρ.snd.map (unitCurveExitProjection U)) ≤ (r : ℝ≥0∞) := by
  have hcompare := trajectoryLaw_map_stoppedPolygonalCurve_of_subset N p hsub hA hUpos v
  rw [← hcompare, ← hρ]
  change levyProkhorovEDist
    ((ρ.map Prod.fst).map (stoppedPolygonalCurve p (p ⁻¹' U)))
    ((ρ.map Prod.snd).map (unitCurveExitProjection U)) ≤ _
  rw [Measure.map_map (measurable_stoppedPolygonalCurve p (p ⁻¹' U)) measurable_fst,
    Measure.map_map (measurable_unitCurveExitProjection hU) measurable_snd]
  apply levyProkhorov_curveLaws_le_of_ae_good ρ _ _
    ((measurable_stoppedPolygonalCurve p (p ⁻¹' U)).comp measurable_fst).aemeasurable
    ((measurable_unitCurveExitProjection hU).comp measurable_snd).aemeasurable E r hbad
  filter_upwards [hgood] with x hx
  intro hxE
  obtain ⟨hfinite, m, hm, hτ, hedge, hclose, hexit, hosc⟩ := hx hxE
  exact (edist_stoppedPolygonalCurve_le_of_pastedWalkCurve p q B initial select n x.1
    hfinite hm hU hτ ha he hmesh hbuffer hpq hedge P x.2 hclose hexit hosc).trans_lt hsmall

end LatticeProb
end
