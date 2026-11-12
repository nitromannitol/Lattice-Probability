/-
# Compactness of a polygonal ray with its limit point

If `v n → a`, the union of the segments `[v n, v (n + 1)]` together with `a` is compact: it is the image of
`[0, 1]` under the continuous parametrisation of the polygonal ray.
-/
import LatticeProb.Topology.BiinfiniteChain

open Set Filter Topology

namespace LatticeProb.Topology

/-- **Closure of a polygonal ray.** If `v n → a`, the trace of the polygonal ray through `v 0, v 1, …`
together with its limit point `a` is compact. -/
theorem isCompact_insert_iUnion_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → E} {a : E} (hv : Filter.Tendsto v Filter.atTop (nhds a)) :
    IsCompact (insert a (⋃ n, segment ℝ (v n) (v (n + 1)))) := by
  obtain ⟨β, hβc, hβ⟩ := exists_polygonalRay_param hv
  have himg : β '' Icc (0 : ℝ) 1 = insert a (⋃ n, segment ℝ (v n) (v (n + 1))) := by
    rw [← Ico_insert_right (zero_le_one' ℝ), image_insert_eq, hβ.1, hβ.image_Ico]
  rw [← himg]
  exact isCompact_Icc.image_of_continuousOn hβc

end LatticeProb.Topology
