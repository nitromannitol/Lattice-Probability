import LatticeProb.LQG.NormalizedSpliceAreaIndependence

/-! # Independence of local cone area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- Restricting the area of a measure to a fixed measurable set is measurable. -/
theorem measurable_measure_restrict {α : Type*} [MeasurableSpace α]
    (s : Set α) (hs : MeasurableSet s) :
    Measurable (fun μ : Measure α => μ.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)

/-- The local cone area, splice field and inner path retain their joint
independence from a given observation. -/
theorem indepFun_normalized_splice_and_local_cone_area
    {Ω : Type} {A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXB : IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P)
    {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hWp : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    {Z : Ω → A} (hZm : Measurable Z)
    (hind : IndepFun (fun ω => (replField X
      (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω,
        W ω)) Z P) :
    let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
    let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
      (replField X (fun ω => twoSided (W ω) (V ω)) ω)
    IndepFun (fun ω => ((F ω,
      (lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
        (fun t => B' t ω))).restrict (ball 0 1)), W ω)) Z P := by
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
    (replField X (fun ω => twoSided (W ω) (V ω)) ω)
  obtain ⟨hjoint, hlocal⟩ := normalized_splice_area_local_and_independent
    hγ hγ2 hX hB hB' hBB' hXB hRm hR hWm hWp hXW hW hZm hind
  have hmap : Measurable (fun p : (DistC × Measure ℂ) × C(ℝ≥0, ℝ) =>
      ((p.1.1, p.1.2.restrict (ball 0 1)), p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_measure_restrict (ball 0 1) isOpen_ball.measurableSet).comp
        (measurable_snd.comp measurable_fst)) |>.prodMk measurable_snd
  have hres := hjoint.comp hmap measurable_id
  apply hres.congr _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [hlocal] with ω hω
  have heq := hω.2 ⟨ball 0 1, isOpen_ball⟩ (Subset.rfl)
  change (lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
    (fun t => B' t ω))).restrict (ball 0 1) =
      (lqgArea γ (F ω)).restrict (ball 0 1) at heq
  change ((F ω, (lqgArea γ (F ω)).restrict (ball 0 1)), W ω) = _
  rw [heq]

end LatticeProb.LQG
