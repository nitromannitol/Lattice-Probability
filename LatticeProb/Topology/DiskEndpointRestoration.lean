module

/-
# Finite disk chains with their original boundary endpoints

Choose an inward scaling from the separation of the original continua. Interior
chains are constructed in neighborhoods of the scaled continua lying inside the
original disjoint neighborhoods and the open disk. Adding the two radial endpoint
segments preserves disjointness and leaves only the original endpoints on the circle.
-/
public import LatticeProb.Topology.PolygonalApproximation
public import LatticeProb.Topology.PolygonalChainEndpoints
public import LatticeProb.Topology.DiskRadialGeometry

@[expose] public section



open Metric Set

namespace LatticeProb.Topology

/-- **Restored original endpoints.** Two disjoint compact connected disk sets admit disjoint finite chains joining
their original prescribed circle endpoints. The chains stay in disjoint original
neighborhoods, and every trace point other than the endpoints is strictly interior. -/
theorem exists_disjoint_polygonal_chains_with_original_endpoints {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKL : Disjoint K L)
    (hKd : K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hLd : L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    {a b c d : ℝ × ℝ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ L) (hd : d ∈ L)
    (haC : a.1 ^ 2 + a.2 ^ 2 = 1) (hbC : b.1 ^ 2 + b.2 ^ 2 = 1)
    (hcC : c.1 ^ 2 + c.2 ^ 2 = 1) (hdC : d.1 ^ 2 + d.2 ^ 2 = 1) :
    ∃ δ > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 - ρ < δ ∧
      Disjoint (thickening δ K) (thickening δ L) ∧
      ∃ vs ws : List (ℝ × ℝ), ∃ hv : vs ≠ [], ∃ hw : ws ≠ [],
      vs.head hv = a ∧ vs.getLast hv = b ∧ ws.head hw = c ∧ ws.getLast hw = d ∧
      polygonalChain vs ⊆ thickening δ K ∧ polygonalChain ws ⊆ thickening δ L ∧
      polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧
      polygonalChain ws ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧
      polygonalChain vs \ {a, b} ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
      polygonalChain ws \ {c, d} ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
      Disjoint (polygonalChain vs) (polygonalChain ws) := by
  obtain ⟨δ, hδ, ρ, hρ0, hρ1, hshort, hsep, hKrad, hLrad⟩ :=
    exists_scaling_in_original_thickenings hK hL hKL hKd hLd
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun z => ρ • z
  have hf : Continuous f := continuous_id.const_smul ρ
  let D : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 < 1}
  have hDo : IsOpen D :=
    isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
  have hKU : f '' K ⊆ thickening δ K ∩ D := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hKrad z hz (right_mem_segment ℝ z (ρ • z)),
      smul_mem_open_unit_disk (hKd hz) hρ0.le hρ1⟩
  have hLU : f '' L ⊆ thickening δ L ∩ D := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hLrad z hz (right_mem_segment ℝ z (ρ • z)),
      smul_mem_open_unit_disk (hLd hz) hρ0.le hρ1⟩
  have hscaled : Disjoint (f '' K) (f '' L) :=
    hsep.mono (hKU.trans inter_subset_left) (hLU.trans inter_subset_left)
  obtain ⟨r, _hr, vs, ws, hv, hw, hhead, hlast, whead, wlast,
      hvsr, hwsr, hKr, hLr, _hscaledsep, _hinnersep⟩ :=
    exists_disjoint_polygonal_chains (hK.image hf) (hKc.image f hf.continuousOn)
      (hL.image hf) (hLc.image f hf.continuousOn) hscaled
      (isOpen_thickening.inter hDo) (isOpen_thickening.inter hDo) hKU hLU
      (mem_image_of_mem f ha) (mem_image_of_mem f hb)
      (mem_image_of_mem f hc) (mem_image_of_mem f hd)
  have hvs : polygonalChain vs ⊆ thickening δ K ∩ D := hvsr.trans hKr
  have hws : polygonalChain ws ⊆ thickening δ L ∩ D := hwsr.trans hLr
  have hveq : polygonalChain ((a :: vs) ++ [b]) =
      (segment ℝ a (ρ • a) ∪ polygonalChain vs) ∪ segment ℝ b (ρ • b) := by
    rw [polygonal_chain_add_endpoints a b hv, hhead, hlast, segment_symm ℝ (ρ • b) b]
  have hweq : polygonalChain ((c :: ws) ++ [d]) =
      (segment ℝ c (ρ • c) ∪ polygonalChain ws) ∪ segment ℝ d (ρ • d) := by
    rw [polygonal_chain_add_endpoints c d hw, whead, wlast, segment_symm ℝ (ρ • d) d]
  have hvn : polygonalChain ((a :: vs) ++ [b]) ⊆ thickening δ K := by
    rw [hveq]
    exact union_subset (union_subset (hKrad a ha) (hvs.trans inter_subset_left)) (hKrad b hb)
  have hwn : polygonalChain ((c :: ws) ++ [d]) ⊆ thickening δ L := by
    rw [hweq]
    exact union_subset (union_subset (hLrad c hc) (hws.trans inter_subset_left)) (hLrad d hd)
  have hvD : polygonalChain ((a :: vs) ++ [b]) ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} := by
    rw [hveq]
    exact union_subset (union_subset
      (segment_self_smul_subset_coordinate_disk haC hρ0.le hρ1)
      (fun z hz => (show z.1 ^ 2 + z.2 ^ 2 < 1 from (hvs hz).2).le))
      (segment_self_smul_subset_coordinate_disk hbC hρ0.le hρ1)
  have hwD : polygonalChain ((c :: ws) ++ [d]) ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} := by
    rw [hweq]
    exact union_subset (union_subset
      (segment_self_smul_subset_coordinate_disk hcC hρ0.le hρ1)
      (fun z hz => (show z.1 ^ 2 + z.2 ^ 2 < 1 from (hws hz).2).le))
      (segment_self_smul_subset_coordinate_disk hdC hρ0.le hρ1)
  have hvI : polygonalChain ((a :: vs) ++ [b]) \ {a, b} ⊆ D := by
    rintro z ⟨hz, hzne⟩
    have hza : z ≠ a := fun h => hzne (by simp [h])
    have hzb : z ≠ b := fun h => hzne (by simp [h])
    rw [hveq] at hz
    rcases hz with (hz | hz) | hz
    · exact mem_open_disk_of_mem_radial_segment_of_ne haC hρ0.le hρ1 hz hza
    · exact (hvs hz).2
    · exact mem_open_disk_of_mem_radial_segment_of_ne hbC hρ0.le hρ1 hz hzb
  have hwI : polygonalChain ((c :: ws) ++ [d]) \ {c, d} ⊆ D := by
    rintro z ⟨hz, hzne⟩
    have hzc : z ≠ c := fun h => hzne (by simp [h])
    have hzd : z ≠ d := fun h => hzne (by simp [h])
    rw [hweq] at hz
    rcases hz with (hz | hz) | hz
    · exact mem_open_disk_of_mem_radial_segment_of_ne hcC hρ0.le hρ1 hz hzc
    · exact (hws hz).2
    · exact mem_open_disk_of_mem_radial_segment_of_ne hdC hρ0.le hρ1 hz hzd
  exact ⟨δ, hδ, ρ, hρ0, hρ1, hshort, hsep,
    (a :: vs) ++ [b], (c :: ws) ++ [d], by simp, by simp,
    by simp, by simp, by simp, by simp,
    hvn, hwn, hvD, hwD, hvI, hwI, hsep.mono hvn hwn⟩

end LatticeProb.Topology
