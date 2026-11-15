import LatticeProb.Topology.CompactImagesArcWitness
import LatticeProb.Topology.MovingIntervalCurve
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Disk-shaped curve segments -/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped unitInterval

namespace LatticeProb

/-- Disk-shaped ranges of continuous unit-interval paths form an analytic set. -/
theorem analyticSet_disk_shaped_curve_range :
    AnalyticSet {f : C(unitInterval, ℂ) |
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ range f)} := by
  let D := closedBall (0 : ℂ) 1
  let J := unitInterval
  have : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have : PolishSpace C(J, ℂ) := LQGMetric.polishSpace_continuousMap J ℂ
  have : PolishSpace C(D, ℂ) := LQGMetric.polishSpace_continuousMap D ℂ
  let A : Set (C(J, ℂ) × C(D, ℂ)) := {p |
    Function.Injective p.2 ∧ range p.2 = range p.1}
  have h₁ : IsClosed {p : C(J, ℂ) × C(D, ℂ) | range p.2 ⊆ range p.1} := by
    have h := isClosed_path_range_subset_compact_image (J := D)
      (fun p : C(J, ℂ) × J => p.1 p.2) (by fun_prop)
    convert h using 1
    ext p
    simp only [mem_ofPred_eq, range_subset_iff, mem_range, eq_comm]
  have h₂ : IsClosed {p : C(J, ℂ) × C(D, ℂ) | range p.1 ⊆ range p.2} := by
    have h := isClosed_path_range_subset_compact_image (J := J)
      (fun p : C(D, ℂ) × D => p.1 p.2) (by fun_prop)
    have h' := h.preimage (continuous_snd.prodMk continuous_fst)
    convert h' using 1
    ext p
    simp only [mem_ofPred_eq, mem_preimage,
      range_subset_iff, mem_range, eq_comm]
  have hA : MeasurableSet A := by
    have heq : A = {p | Function.Injective p.2} ∩
        ({p | range p.2 ⊆ range p.1} ∩ {p | range p.1 ⊆ range p.2}) := by
      ext p
      simp only [A, mem_ofPred_eq, mem_inter_iff, subset_antisymm_iff]
    rw [heq]
    exact (measurableSet_injective_continuousMap.preimage measurable_snd).inter
      (h₁.measurableSet.inter h₂.measurableSet)
  have heq : {f : C(J, ℂ) | Nonempty (D ≃ₜ range f)} = Prod.fst '' A := by
    ext f
    constructor
    · rintro ⟨e⟩
      let g : C(D, ℂ) := ⟨fun x => e x, continuous_subtype_val.comp e.continuous⟩
      have hg : Function.Injective g := fun x y h => e.injective (Subtype.ext h)
      have hr : range g = range f := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          exact (e x).property
        · intro hz
          refine ⟨e.symm ⟨z, hz⟩, ?_⟩
          exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
      exact ⟨(f, g), ⟨hg, hr⟩, rfl⟩
    · rintro ⟨⟨f', g⟩, ⟨hg, hr⟩, rfl⟩
      have e : D ≃ₜ range g :=
        (g.continuous.isClosedEmbedding hg).isEmbedding.toHomeomorph
      change Nonempty (D ≃ₜ range f')
      rw [← hr]
      exact ⟨e⟩
  rw [heq]
  exact hA.analyticSet.image_of_continuous continuous_fst

/-- A fixed curve segment is disk-shaped on a null-measurable event. -/
theorem nullMeasurableSet_disk_shaped_curve_segment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → C(ℝ, ℂ)) (hf : Measurable f) (a b : ℝ) :
    NullMeasurableSet {ω | Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f ω '' uIcc a b))} P := by
  let F : Ω → C(unitInterval, ℂ) := fun ω => movingIntervalCurve (f ω) a b
  have hF : Measurable F :=
    continuous_movingIntervalCurve.measurable.comp (hf.prodMk (measurable_const.prodMk measurable_const))
  have : IsFiniteMeasure (P.map F) := P.isFiniteMeasure_map F
  have h := (AnalyticSet.nullMeasurableSet (P.map F) analyticSet_disk_shaped_curve_range).preimage
    (hF.quasiMeasurePreserving P)
  change NullMeasurableSet {ω | Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
    range (movingIntervalCurve (f ω) a b))} P at h
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [range_movingIntervalCurve]

end LatticeProb
