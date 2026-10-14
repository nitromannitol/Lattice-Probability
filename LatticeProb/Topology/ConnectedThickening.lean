/-
# Connected metric neighborhoods of continua

A positive metric thickening of a connected subset of a real normed space is
connected. Two disjoint compact continua therefore admit disjoint connected open
neighborhoods inside any prescribed open neighborhoods.
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.Thickening



open Metric Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive thickening is connected even when the original set has no paths. -/
theorem isConnected_thickening {K : Set E} (hK : IsConnected K) {r : ℝ} (hr : 0 < r) :
    IsConnected (thickening r K) := by
  obtain ⟨x, hx⟩ := hK.nonempty
  have hsub : K ⊆ thickening r K := self_subset_thickening hr K
  refine ⟨⟨x, hsub hx⟩, isPreconnected_of_forall x ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  refine ⟨K ∪ ball z r, union_subset hsub (ball_subset_thickening hz r),
    Or.inl hx, Or.inr hyz, ?_⟩
  exact (hK.union ⟨z, hz, mem_ball_self hr⟩
    ((convex_ball z r).isConnected ⟨z, mem_ball_self hr⟩)).isPreconnected

/-- **Separated connected neighborhoods.** Disjoint compact continua have disjoint connected open metric neighborhoods,
with a single radius and contained in prescribed open sets. -/
theorem exists_disjoint_connected_open_thickenings {K L U V : Set E}
    (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKL : Disjoint K L)
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hLV : L ⊆ V) :
    ∃ r > 0, Disjoint (thickening r K) (thickening r L) ∧
      thickening r K ⊆ U ∧ thickening r L ⊆ V ∧
      IsOpen (thickening r K) ∧ IsOpen (thickening r L) ∧
      IsConnected (thickening r K) ∧ IsConnected (thickening r L) := by
  obtain ⟨d, hd, hsep⟩ := hKL.exists_thickenings hK hL.isClosed
  obtain ⟨a, ha, hKa⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨b, hb, hLb⟩ := hL.exists_thickening_subset_open hV hLV
  let r := min d (min a b)
  have hr : 0 < r := lt_min hd (lt_min ha hb)
  have hrd : r ≤ d := min_le_left _ _
  have hra : r ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨r, hr, hsep.mono (thickening_mono hrd K) (thickening_mono hrd L),
    (thickening_mono hra K).trans hKa, (thickening_mono hrb L).trans hLb,
    isOpen_thickening, isOpen_thickening,
    isConnected_thickening hKc hr, isConnected_thickening hLc hr⟩

end LatticeProb.Topology
