import LatticeProb.Topology.RadialScaleSelection
import LatticeProb.Topology.LocalizedFirstExitTrace
import LatticeProb.Topology.LocalizedCurveHalfTrace

/-! # Scale and first-exit estimates for localized curve segments -/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- Each localized segment has its own exponential scale. At that scale its
 diameter is controlled and its measure dominates both first-exit bounds. -/
theorem localized_segment_scale_and_measure {X : Type*} [MetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (η : ℝ → X) (hη : Continuous η)
    (z : X) {ε t₀ L U : ℝ} (hL : 0 < L)
    (hleft : ¬ η '' Icc (t₀ - ε / 2) t₀ ⊆ ball z L)
    (hright : ¬ η '' Icc t₀ (t₀ + ε / 2) ⊆ ball z L)
    (hwindow : η '' Icc (t₀ - ε) (t₀ + ε) ⊆ closedBall z U)
    (A : ℤ → ℝ≥0∞)
    (htrace : ∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log U →
      A k ≤ min (μ (η '' Icc (sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ ball z (Real.exp k)}) t₀))
        (μ (η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z (Real.exp k)})))) :
    ∀ s ∈ Icc t₀ (t₀ + ε), ∃ k : ℤ,
      Real.log L - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.log U ∧
      diam (η '' Icc (s - ε) s) < 2 * Real.exp ((k : ℝ) + 1) ∧
      A k ≤ μ (η '' Icc (s - ε) s) := by
  intro s hs
  have hcontain := localized_interval_contains_half hs
  have ha : s - ε ≤ t₀ := by linarith [hs.2]
  have hb : t₀ ≤ s := hs.1
  have hne : (η '' Icc (s - ε) s).Nonempty := ⟨η t₀, ⟨t₀, ⟨ha, hb⟩, rfl⟩⟩
  have hcompact : IsCompact (η '' Icc (s - ε) s) := isCompact_Icc.image hη
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne
    (continuous_id.dist continuous_const).continuousOn
  have hsub : η '' Icc (s - ε) s ⊆ closedBall z (dist x z) := by
    intro y hy
    exact hmax hy
  have hesc : ¬ η '' Icc (s - ε) s ⊆ ball z L :=
    localized_curve_segment_not_subset η (ball z L) hs hleft hright
  obtain ⟨y, hy, hyout⟩ := not_subset.mp hesc
  have hLR : L ≤ dist x z := by
    have hyL : L ≤ dist y z := le_of_not_gt hyout
    exact hyL.trans (hmax hy)
  have hRU : dist x z ≤ U := by
    apply hwindow
    exact (image_mono hcontain.1) hx
  obtain ⟨k, hklo, hkhi, hkesc, hkdiam⟩ :=
    exists_radial_exponential_scale (η '' Icc (s - ε) s) z hL hLR hRU hsub ⟨x, hx, rfl⟩
  exact ⟨k, hklo, hkhi, hkdiam,
    (htrace k hklo hkhi).trans (min_first_exit_trace_measure_le μ η _ ha hb hkesc)⟩

end LatticeProb
