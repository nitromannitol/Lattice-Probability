import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutRadial

/-! The inverse of a punctured topological disk retracts onto its boundary. -/

noncomputable section

open Set Metric
open LQGMetric.Topo.Crosscut

namespace LatticeProb

/-- Inversion takes a punctured based topological disk to a set which retracts
continuously onto the inverse image of its boundary. -/
theorem exists_inverted_disk_boundary_retraction {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K)
    (he : (e ⟨0, mem_closedBall_self (by norm_num)⟩ : ℂ) = 0) :
    ∃ r : {w : ℂ // w ≠ 0 ∧ w⁻¹ ∈ K} → ℂ,
      Continuous r ∧
      (∀ w, r w ∈ (fun z => (e z : ℂ)⁻¹) ''
        {z | (z : ℂ) ∈ sphere 0 1}) ∧
      (∀ w : {w : ℂ // w ≠ 0 ∧ w⁻¹ ∈ K}, (w : ℂ) ∈ (fun z => (e z : ℂ)⁻¹) ''
        {z | (z : ℂ) ∈ sphere 0 1} → r w = w) := by
  let c : closedBall (0 : ℂ) 1 := ⟨0, mem_closedBall_self (by norm_num)⟩
  let f : {w : ℂ // w ≠ 0 ∧ w⁻¹ ∈ K} → ℂ := fun w =>
    (e.symm ⟨(w : ℂ)⁻¹, w.2.2⟩ : ℂ)
  have hf : Continuous f := by
    apply Continuous.subtype_val
    apply e.symm.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_subtype_val.inv₀ (fun w => w.2.1)
  have hf0 : ∀ w, f w ≠ 0 := by
    intro w hw
    have h : e.symm ⟨(w : ℂ)⁻¹, w.2.2⟩ = c := Subtype.ext hw
    have h' := congrArg (fun z => (e z : ℂ)) h
    have : (w : ℂ)⁻¹ = 0 := by simpa [c, he] using h'
    exact (inv_ne_zero w.2.1) this
  let g : {w : ℂ // w ≠ 0 ∧ w⁻¹ ∈ K} → closedBall (0 : ℂ) 1 := fun w =>
    ⟨rproj 0 1 (f w), sphere_subset_closedBall (rproj_mem_sphere (by norm_num) (hf0 w))⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (continuousOn_rproj 0 1).comp_continuous hf (fun w => hf0 w)
  have hg0 : ∀ w, (e (g w) : ℂ) ≠ 0 := by
    intro w h
    have hg_eq : g w = c := e.injective (Subtype.ext (by simpa [c, he] using h))
    have hs := rproj_mem_sphere (show (0 : ℝ) ≤ 1 by norm_num) (hf0 w)
    have : (g w : ℂ) = 0 := congrArg Subtype.val hg_eq
    rw [← show (g w : ℂ) = rproj 0 1 (f w) from rfl, this] at hs
    simp at hs
  refine ⟨fun w => (e (g w) : ℂ)⁻¹, ((e.continuous.comp hg).subtype_val).inv₀ hg0, ?_, ?_⟩
  · intro w
    exact ⟨g w, rproj_mem_sphere (by norm_num) (hf0 w), rfl⟩
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hw
    have hwz : (w : ℂ)⁻¹ = (e z : ℂ) := by rw [← hzw, inv_inv]
    have hfz : f w = (z : ℂ) := by
      change (e.symm ⟨(w : ℂ)⁻¹, w.2.2⟩ : ℂ) = z
      have : (⟨(w : ℂ)⁻¹, w.2.2⟩ : K) = e z := Subtype.ext hwz
      rw [this, e.symm_apply_apply]
    have hg_eq : g w = z := by
      apply Subtype.ext
      change rproj 0 1 (f w) = z
      rw [hfz, rproj_of_mem (by norm_num) hz]
    change (e (g w) : ℂ)⁻¹ = (w : ℂ)
    rw [hg_eq]
    exact hzw

end LatticeProb
