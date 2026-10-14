/-
# Polygonal approximation of arbitrary disk continua

The disk is the closed Euclidean disk given by the sum of the coordinate squares,
regardless of the ambient product norm. Inward scaling places both continua in
its open interior, where disjoint finite polygonal connections can be constructed.
-/
import LatticeProb.Topology.PolygonalApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring



open Set

namespace LatticeProb.Topology

/-- Inward scaling maps the algebraic closed unit disk into its open interior. -/
theorem smul_mem_open_unit_disk {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (s • z).1 ^ 2 + (s • z).2 ^ 2 < 1 := by
  change (s * z.1) ^ 2 + (s * z.2) ^ 2 < 1
  calc
    (s * z.1) ^ 2 + (s * z.2) ^ 2 = s ^ 2 * (z.1 ^ 2 + z.2 ^ 2) := by ring
    _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hz (sq_nonneg s)
    _ < 1 := by
      rw [mul_one]
      exact (sq_lt_one_iff₀ hs).mpr hs1

/-- **Disjoint polygonal disk approximation.** Arbitrary compact connected subsets of the closed algebraic unit disk,
when disjoint, yield disjoint compact connected polygonal chains in its open
interior between each prescribed pair of inward-scaled points. -/
theorem exists_disjoint_polygonal_chains_in_disk {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKL : Disjoint K L)
    (hKd : K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hLd : L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    {a b c d : ℝ × ℝ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ L) (hd : d ∈ L) :
    ∃ vs ws : List (ℝ × ℝ), ∃ hv : vs ≠ [], ∃ hw : ws ≠ [],
      vs.head hv = (1 / 2 : ℝ) • a ∧ vs.getLast hv = (1 / 2 : ℝ) • b ∧
      ws.head hw = (1 / 2 : ℝ) • c ∧ ws.getLast hw = (1 / 2 : ℝ) • d ∧
      polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
      polygonalChain ws ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
      Disjoint (polygonalChain vs) (polygonalChain ws) ∧
      IsCompact (polygonalChain vs) ∧ IsConnected (polygonalChain vs) ∧
      IsCompact (polygonalChain ws) ∧ IsConnected (polygonalChain ws) := by
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (1 / 2 : ℝ) • z
  have hf : Continuous f := continuous_id.const_smul (1 / 2 : ℝ)
  have hfi : Function.Injective f := smul_right_injective _ (by norm_num)
  have hU : IsOpen {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < 1} :=
    isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
  have hKU : f '' K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact smul_mem_open_unit_disk (hKd hz) (by norm_num) (by norm_num)
  have hLU : f '' L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact smul_mem_open_unit_disk (hLd hz) (by norm_num) (by norm_num)
  obtain ⟨r, _hr, vs, ws, hv, hw, hhead, hlast, whead, wlast,
      hvs, hws, hKr, hLr, _hsep, hdisj⟩ :=
    exists_disjoint_polygonal_chains (hK.image hf) (hKc.image f hf.continuousOn)
      (hL.image hf) (hLc.image f hf.continuousOn) (disjoint_image_of_injective hfi hKL)
      hU hU hKU hLU (mem_image_of_mem f ha) (mem_image_of_mem f hb)
      (mem_image_of_mem f hc) (mem_image_of_mem f hd)
  exact ⟨vs, ws, hv, hw, hhead, hlast, whead, wlast,
    hvs.trans hKr, hws.trans hLr, hdisj,
    isCompact_polygonal_chain vs, isConnected_polygonal_chain hv,
    isCompact_polygonal_chain ws, isConnected_polygonal_chain hw⟩

end LatticeProb.Topology
