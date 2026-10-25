module

/-
# Polygonal completions outside the coordinate disk

Two prescribed points of the original unit circle can be joined by a finite
polygonal chain which meets the closed coordinate disk exactly at its endpoints.
The construction joins their doubled points in the open exterior, then adds
outward radial segments. The exterior connection follows from the continuous
radius-two circle and polygonal connectedness of open connected components.
-/
public import LatticeProb.Topology.PolygonalChainEndpoints
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Tactic.Ring

@[expose] public section



open Set

namespace LatticeProb.Topology

/-- Squared coordinate radius scales by the square of the scalar. -/
theorem coordinate_square_smul (r : ℝ) (z : ℝ × ℝ) :
    (r • z).1 ^ 2 + (r • z).2 ^ 2 = r ^ 2 * (z.1 ^ 2 + z.2 ^ 2) := by
  change (r * z.1) ^ 2 + (r * z.2) ^ 2 = r ^ 2 * (z.1 ^ 2 + z.2 ^ 2)
  ring

/-- An outward radial segment from a unit-circle point is strictly outside the
coordinate disk except at its original endpoint. -/
theorem one_lt_coordinate_square_of_mem_outward_segment {a w : ℝ × ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1)
    (hw : w ∈ segment ℝ a ((2 : ℝ) • a)) (hne : w ≠ a) :
    1 < w.1 ^ 2 + w.2 ^ 2 := by
  obtain ⟨u, v, _, hv, huv, rfl⟩ := hw
  have hform : u • a + v • ((2 : ℝ) • a) = (1 + v) • a := by
    rw [smul_smul, ← add_smul]
    congr 1
    calc
      u + v * 2 = (u + v) + v := by ring
      _ = 1 + v := by rw [huv]
  rw [hform] at hne ⊢
  have hvne : v ≠ 0 := by
    intro h
    apply hne
    rw [h, add_zero, one_smul]
  have hvpos : 0 < v := lt_of_le_of_ne hv hvne.symm
  rw [coordinate_square_smul, ha, mul_one]
  exact (one_lt_sq_iff₀ (add_nonneg zero_le_one hv)).mpr
    (lt_add_of_pos_right 1 hvpos)

/-- The doubled points of any two original circle angles can be joined by a
finite polygonal chain entirely in the open exterior of the coordinate disk. -/
theorem exists_polygonal_chain_outside_coordinate_disk (θ φ : ℝ) :
    ∃ vs : List (ℝ × ℝ), ∃ hv : vs ≠ [],
      vs.head hv = (2 : ℝ) • (Real.cos θ, Real.sin θ) ∧
      vs.getLast hv = (2 : ℝ) • (Real.cos φ, Real.sin φ) ∧
      polygonalChain vs ⊆ {z | 1 < z.1 ^ 2 + z.2 ^ 2} := by
  let f : ℝ → ℝ × ℝ := fun t => (2 : ℝ) • (Real.cos t, Real.sin t)
  let U : Set (ℝ × ℝ) := {z | 1 < z.1 ^ 2 + z.2 ^ 2}
  have hf : Continuous f := by fun_prop
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hfU : range f ⊆ U := by
    rintro z ⟨t, rfl⟩
    change 1 < ((2 : ℝ) • (Real.cos t, Real.sin t)).1 ^ 2 +
      ((2 : ℝ) • (Real.cos t, Real.sin t)).2 ^ 2
    rw [coordinate_square_smul, Real.cos_sq_add_sin_sq, mul_one]
    norm_num
  have hsub : range f ⊆ connectedComponentIn U (f θ) :=
    (isPreconnected_range hf).subset_connectedComponentIn ⟨θ, rfl⟩ hfU
  obtain ⟨vs, hv, hvs, hhead, hlast⟩ :=
    exists_polygonal_chain_of_isPreconnected hU.connectedComponentIn
      isPreconnected_connectedComponentIn (hsub ⟨θ, rfl⟩) (hsub ⟨φ, rfl⟩)
  exact ⟨vs, hv, hhead, hlast, hvs.trans (connectedComponentIn_subset U (f θ))⟩

/-- **Outside polygonal completion.** Any two original unit-circle endpoints
have a finite polygonal connection whose intersection with the closed coordinate
disk is exactly those endpoints. Every other trace point is strictly outside. -/
theorem exists_polygonal_outside_completion (θ φ : ℝ) :
    ∃ vs : List (ℝ × ℝ), ∃ hv : vs ≠ [],
      vs.head hv = (Real.cos θ, Real.sin θ) ∧
      vs.getLast hv = (Real.cos φ, Real.sin φ) ∧
      polygonalChain vs \ {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} ⊆
        {z | 1 < z.1 ^ 2 + z.2 ^ 2} ∧
      polygonalChain vs ∩ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} =
        {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} := by
  obtain ⟨vs, hv, hhead, hlast, hsub⟩ :=
    exists_polygonal_chain_outside_coordinate_disk θ φ
  let a : ℝ × ℝ := (Real.cos θ, Real.sin θ)
  let b : ℝ × ℝ := (Real.cos φ, Real.sin φ)
  let ws := (a :: vs) ++ [b]
  have hw : ws ≠ [] := by simp [ws]
  have hfirst : ws.head hw = a := by
    rw [List.head_append_of_ne_nil (List.cons_ne_nil a vs)]
    rfl
  have hfinal : ws.getLast hw = b := List.getLast_concat
  have htrace : polygonalChain ws =
      (segment ℝ a ((2 : ℝ) • a) ∪ polygonalChain vs) ∪
        segment ℝ ((2 : ℝ) • b) b := by
    rw [polygonal_chain_add_endpoints a b hv, hhead, hlast]
  have hout : polygonalChain ws \ {a, b} ⊆ {z | 1 < z.1 ^ 2 + z.2 ^ 2} := by
    rintro z ⟨hz, hzne⟩
    have hza : z ≠ a := fun h => hzne (h ▸ mem_insert a {b})
    have hzb : z ≠ b := fun h => hzne (by
      rw [h]
      exact mem_insert_of_mem a (mem_singleton b))
    rw [htrace] at hz
    rcases hz with (hz | hz) | hz
    · exact one_lt_coordinate_square_of_mem_outward_segment
        (Real.cos_sq_add_sin_sq θ) hz hza
    · exact hsub hz
    · rw [segment_symm] at hz
      exact one_lt_coordinate_square_of_mem_outward_segment
        (Real.cos_sq_add_sin_sq φ) hz hzb
  refine ⟨ws, hw, hfirst, hfinal, hout, subset_antisymm ?_ ?_⟩
  · rintro z ⟨hz, hzD⟩
    by_contra hzne
    exact (not_lt_of_ge (show z.1 ^ 2 + z.2 ^ 2 ≤ 1 from hzD)) (hout ⟨hz, hzne⟩)
  · intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · refine ⟨?_, (Real.cos_sq_add_sin_sq θ).le⟩
      change a ∈ polygonalChain ws
      rw [← hfirst]
      exact head_mem_polygonal_chain hw
    · have hzb : z = b := mem_singleton_iff.mp hz
      subst z
      refine ⟨?_, (Real.cos_sq_add_sin_sq φ).le⟩
      change b ∈ polygonalChain ws
      rw [← hfinal]
      exact getLast_mem_polygonal_chain hw

end LatticeProb.Topology
