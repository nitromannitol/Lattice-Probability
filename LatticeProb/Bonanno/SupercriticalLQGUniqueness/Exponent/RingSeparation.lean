/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.RingSeparation at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Top3
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect




 





set_option autoImplicit false

open Set

namespace SupercriticalLQGUniqueness.Exponent.RingSeparation

open LQGMetric

private theorem adm_geom (R : DDDF.MarkedRect) {P : ℝ → ℂ}
    (hP : DDDF.AdmPath R.toSet R.side₁ R.side₂ P) :
    IsPathConnected (P '' Icc (0 : ℝ) 1) ∧
      P '' Icc (0 : ℝ) 1 ⊆ R.toSet ∧
      ((P '' Icc (0 : ℝ) 1) ∩ R.side₁).Nonempty ∧
      ((P '' Icc (0 : ℝ) 1) ∩ R.side₂).Nonempty := by
  obtain ⟨z, hz, w, hw, hpc, hmem⟩ := hP
  have hpc' : IsPathConnected (P '' Icc (0 : ℝ) 1) :=
    ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.mpr zero_le_one)).image'
      hpc.continuousOn
  refine ⟨hpc', ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hmem t ht
  · refine ⟨P 0, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, ?_⟩
    rw [hpc.source]
    exact hz
  · refine ⟨P 1, ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, ?_⟩
    rw [hpc.target]
    exact hw


private theorem hit_image_of_hit_preimage {P : ℝ → ℂ} {S : Set ℂ}
    (h : (Icc (0 : ℝ) 1 ∩ P ⁻¹' S).Nonempty) :
    ((P '' Icc (0 : ℝ) 1) ∩ S).Nonempty := by
  obtain ⟨t, ht, hs⟩ := h
  exact ⟨P t, ⟨t, ht, rfl⟩, hs⟩


 
theorem siteCirc_union_pathHit {ξ : ℝ} {f : ℂ → ℝ} {c : ENNReal}
    (C : DDDF.SiteCirc ξ f (0, 0) c) :
    LQGMetric.Disconnects
      (C.B '' Icc (0 : ℝ) 1 ∪ C.T '' Icc (0 : ℝ) 1 ∪
        C.L '' Icc (0 : ℝ) 1 ∪ C.R '' Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1)
      (Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2)ᶜ := by
  have hB := adm_geom (DDDF.sB (0, 0)) C.hB
  have hT := adm_geom (DDDF.sT (0, 0)) C.hT
  have hL := adm_geom (DDDF.sL (0, 0)) C.hL
  have hR := adm_geom (DDDF.sR (0, 0)) C.hR
  norm_num [DDDF.sB, DDDF.sT, DDDF.sL, DDDF.sR,
    DDDF.MarkedRect.toSet, DDDF.MarkedRect.side₁, DDDF.MarkedRect.side₂] at hB hT hL hR
  intro p q γ hp hq
  have hγ : IsPathConnected (Set.range γ) := by
    rw [← γ.extend_range]
    exact isPathConnected_range γ.continuous_extend
  have hp' : γ (0 : unitInterval) ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    simpa using hp
  have hq' : γ (1 : unitInterval) ∉ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2 := by
    simpa using hq
  have hmeet := LQGMetric.DZZ.dzz_ring_sep
    (x₀ := -1) (x₁ := 0) (x₂ := 1) (x₃ := 2)
    (y₀ := -1) (y₁ := 0) (y₂ := 1) (y₃ := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hB.1 (Set.image_subset_iff.mpr hB.2.1)
    (hit_image_of_hit_preimage hB.2.2.1) (hit_image_of_hit_preimage hB.2.2.2)
    hT.1 (Set.image_subset_iff.mpr hT.2.1)
    (hit_image_of_hit_preimage hT.2.2.1) (hit_image_of_hit_preimage hT.2.2.2)
    hL.1 (Set.image_subset_iff.mpr hL.2.1)
    (hit_image_of_hit_preimage hL.2.2.1) (hit_image_of_hit_preimage hL.2.2.2)
    hR.1 (Set.image_subset_iff.mpr hR.2.1)
    (hit_image_of_hit_preimage hR.2.2.1) (hit_image_of_hit_preimage hR.2.2.2)
    hγ (Set.mem_range_self (0 : unitInterval))
    (Set.mem_range_self (1 : unitInterval)) hp' hq'
  simpa only [Set.union_assoc] using hmeet


 
end SupercriticalLQGUniqueness.Exponent.RingSeparation
