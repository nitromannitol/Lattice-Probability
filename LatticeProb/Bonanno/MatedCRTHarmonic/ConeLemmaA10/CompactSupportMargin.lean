/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CompactSupportMargin at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Uniform distance from the normalization boundary

A compact set contained in the open unit disk stays a positive distance from its boundary.
For continuous test functions, the topological support is compact whenever it is contained in
that disk, so this gives a single circle-radius margin valid over the whole support.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace MatedCRTHarmonic.ConeLemmaA10

/-- The norm on a compact subset of the open unit disk has a maximum strictly below one. -/
lemma exists_radius_bound_of_compact_subset_unitDisk {K : Set ℂ}
    (hKcompact : IsCompact K) (hKsubset : K ⊆ ball (0 : ℂ) 1) :
    ∃ R : ℝ, R < 1 ∧ ∀ z ∈ K, ‖z‖ ≤ R := by
  by_cases hKempty : K = ∅
  · refine ⟨0, by norm_num, ?_⟩
    intro z hz
    simp [hKempty] at hz
  · have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    obtain ⟨x, hxK, hxmax⟩ := hKcompact.exists_isMaxOn hKne
      (continuous_norm.continuousOn : ContinuousOn (fun z : ℂ => ‖z‖) K)
    have hxball : x ∈ ball (0 : ℂ) 1 := hKsubset hxK
    have hxlt : ‖x‖ < 1 := by simpa using Metric.mem_ball.mp hxball
    refine ⟨‖x‖, hxlt, ?_⟩
    intro z hz
    exact hxmax hz

/-- A compactly supported test inside the open unit disk admits a positive uniform radius
margin: every point of its support has its radius plus `ε` still strictly below one. -/
lemma exists_uniform_tsupport_margin {f : ℂ → ℝ} (_hf : Continuous f)
    (hfs : tsupport f ⊆ ball (0 : ℂ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ tsupport f, ‖z‖ + ε < 1 := by
  have hKcompact : IsCompact (tsupport f) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f)
      (Metric.isBounded_ball.subset hfs)
  obtain ⟨R, hRlt, hR⟩ :=
    exists_radius_bound_of_compact_subset_unitDisk hKcompact hfs
  refine ⟨(1 - R) / 2, by linarith, ?_⟩
  intro z hz
  have hzR := hR z hz
  linarith

end MatedCRTHarmonic.ConeLemmaA10

