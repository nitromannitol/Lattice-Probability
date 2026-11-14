import LatticeProb.Prob.BrownianOpenExit
import LatticeProb.Prob.ContinuousMapUnboundedRange
import LatticeProb.Topology.IntervalReparamMeasurableVarying
import LatticeProb.Topology.LocalCurveIntervalDistance
import Mathlib.Topology.Maps.Proper.Basic

/-! # Ball exits and the local interval-distance integrand -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.UnboundedRayIntervalIntegrand

variable {d : ℕ}

abbrev Path (d : ℕ) := C(ℝ≥0, EuclideanSpace ℝ (Fin d))

/-- Continuous paths with unbounded range. -/
abbrev UnboundedRay (d : ℕ) := {f : Path d // ¬ Bornology.IsBounded (Set.range f)}

/-- First exit from a ball centered at the origin. -/
noncomputable def ballClock (f : Path d) (r : ℝ) : ℝ≥0∞ :=
  openExitTime (fun t (f : Path d) => f t) (ball 0 r) f

/-- Unbounded paths exit every ball in finite time. -/
theorem ballClock_ne_top (f : UnboundedRay d) (r : ℝ) : ballClock f.1 r ≠ ⊤ := by
  have hn : ¬ Set.range f.1 ⊆ ball 0 r := by
    intro h
    exact f.2 (Metric.isBounded_ball.subset h)
  obtain ⟨x, hx, hxb⟩ := Set.not_subset.mp hn
  obtain ⟨t, rfl⟩ := hx
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem hxb)

/-- Finite sublevels of the ball clock are closed jointly in the path and radius. -/
theorem isClosed_ballClock_le (t : ℝ≥0) :
    IsClosed {p : Path d × ℝ | ballClock p.1 p.2 ≤ (t : ℝ≥0∞)} := by
  have hcompact : IsCompact (Set.Iic t : Set ℝ≥0) := by
    have heq : Set.Iic t = Set.Icc 0 t := by
      ext u
      simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
    rw [heq]
    exact isCompact_Icc
  let : CompactSpace (Set.Iic t) := isCompact_iff_compactSpace.mp hcompact
  let A : Set ((Path d × ℝ) × Set.Iic t) :=
    {p | p.1.2 ≤ dist (p.1.1 p.2) 0}
  have heval : Continuous (fun p : (Path d × ℝ) × Set.Iic t => p.1.1 p.2) :=
    (ContinuousEval.continuous_eval (F := Path d)).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed A :=
    isClosed_le (continuous_snd.comp continuous_fst) (heval.dist continuous_const)
  have hproj := isClosedMap_fst_of_compactSpace A hclosed
  convert hproj using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · intro h
    have hfin : ballClock p.1 p.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    have hout := openExitTime_not_mem (B := fun t (f : Path d) => f t)
      (ω := p.1) (isOpen_ball : IsOpen (ball (0 : EuclideanSpace ℝ (Fin d)) p.2))
      p.1.continuous hfin
    refine ⟨⟨(ballClock p.1 p.2).toNNReal, ?_⟩, ?_⟩
    · exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfin] using h)
    · change p.2 ≤ dist (p.1 (ballClock p.1 p.2).toNNReal) 0
      simpa only [Metric.mem_ball, not_lt, ballClock] using hout
  · rintro ⟨s, hs⟩
    change p.2 ≤ dist (p.1 s) 0 at hs
    have hout : p.1 s ∉ ball (0 : EuclideanSpace ℝ (Fin d)) p.2 := by
      simpa only [Metric.mem_ball, not_lt] using hs
    exact (openExitTime_le_of_not_mem hout).trans (ENNReal.coe_le_coe.mpr s.2)

/-- The ball exit clock is jointly Borel in a path and radius. -/
theorem measurable_ballClock : Measurable (fun p : Path d × ℝ => ballClock p.1 p.2) := by
  apply measurable_of_Iic
  intro a
  by_cases ha : a = ⊤
  · subst a
    simp only [Set.preimage, Set.mem_Iic, le_top, ofPred_true]
    exact MeasurableSet.univ
  · rw [← ENNReal.coe_toNNReal ha]
    exact (isClosed_ballClock_le a.toNNReal).measurableSet

/-- The weighted truncated interval distance is jointly measurable on unbounded rays. -/
theorem measurable_weighted_intervalEDist :
    Measurable (fun p : (UnboundedRay d × UnboundedRay d) × ℝ =>
      ENNReal.ofReal (Real.exp (-p.2)) *
        min 1 (IntervalReparamEDist.intervalEDist p.1.1.1 p.1.2.1
          (ballClock p.1.1.1 p.2) (ballClock p.1.2.1 p.2))) := by
  have hf : Measurable (fun p : (UnboundedRay d × UnboundedRay d) × ℝ => p.1.1.1) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
  have hg : Measurable (fun p : (UnboundedRay d × UnboundedRay d) × ℝ => p.1.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)
  have hc := measurable_ballClock.comp (hf.prodMk measurable_snd)
  have he := measurable_ballClock.comp (hg.prodMk measurable_snd)
  have hd := IntervalReparamEDist.measurable_intervalEDist_of_measurable_finite
    _ _ _ _ hf hg hc he (fun p => ballClock_ne_top p.1.1 p.2)
    (fun p => ballClock_ne_top p.1.2 p.2)
  exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (measurable_snd.neg))).mul (measurable_const.min hd)

end LatticeProb.UnboundedRayIntervalIntegrand
