import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutRadial

/-! A punctured topological closed disk retracts continuously onto its boundary. -/

noncomputable section

open Set Metric
open LQGMetric.Topo.Crosscut

namespace LatticeProb

/-- A closed disk with its centre removed admits a continuous retraction onto the
image of its boundary circle under any homeomorphism. -/
theorem exists_punctured_disk_boundary_retraction {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K) :
    ∃ r : {x : K // x ≠ e ⟨0, mem_closedBall_self (by norm_num)⟩} → K,
      Continuous r ∧
      (∀ x, (r x : ℂ) ∈ (fun z => (e z : ℂ)) ''
        {z | (z : ℂ) ∈ sphere 0 1}) ∧
      (∀ x, (x.1 : ℂ) ∈ (fun z => (e z : ℂ)) ''
        {z | (z : ℂ) ∈ sphere 0 1} → r x = x.1) := by
  let c : closedBall (0 : ℂ) 1 := ⟨0, mem_closedBall_self (by norm_num)⟩
  let f : {x : K // x ≠ e c} → ℂ := fun x => (e.symm x.1 : ℂ)
  have hf : Continuous f := e.symm.continuous.comp continuous_subtype_val |>.subtype_val
  have hf0 : ∀ x, f x ≠ 0 := by
    intro x h
    have he : e.symm x.1 = c := Subtype.ext h
    exact x.2 (by simpa using congrArg e he)
  let g : {x : K // x ≠ e c} → closedBall (0 : ℂ) 1 := fun x =>
    ⟨rproj 0 1 (f x), sphere_subset_closedBall (rproj_mem_sphere (by norm_num) (hf0 x))⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (continuousOn_rproj 0 1).comp_continuous hf (fun x => hf0 x)
  refine ⟨fun x => e (g x), e.continuous.comp hg, ?_, ?_⟩
  · intro x
    exact ⟨g x, rproj_mem_sphere (by norm_num) (hf0 x), rfl⟩
  · intro x hx
    obtain ⟨z, hz, he⟩ := hx
    have hxz : x.1 = e z := Subtype.ext he.symm
    have hfz : f x = (z : ℂ) := by simp [f, hxz]
    have hgx : g x = z := by
      apply Subtype.ext
      change rproj 0 1 (f x) = z
      rw [hfz, rproj_of_mem (by norm_num) hz]
    change e (g x) = x.1
    rw [hgx, hxz]

end LatticeProb
