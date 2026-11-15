import LatticeProb.Topology.EmbeddedDiskJordan

/-! Invariance of domain in the complex plane. -/

set_option autoImplicit false

noncomputable section

open Set Metric Topology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan

namespace LatticeProb

/-- A continuous injective map on an open subset of the plane has open image. -/
theorem isOpen_image_of_continuousOn_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hi : InjOn f U) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hx
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hsub : closedBall x r ⊆ U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRU
  let L := Arcs.complexLIE
  let A : closedBall (0 : Plane) 1 → ℂ := fun p => x + r • L.symm p
  have hA : ∀ p, A p ∈ U := by
    intro p
    apply hsub
    rw [mem_closedBall, dist_eq_norm]
    dsimp [A]
    rw [add_sub_cancel_left]
    change ‖r • L.symm (p : Plane)‖ ≤ r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, L.symm.norm_map]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp p.2) hr.le).trans_eq (mul_one r)
  have hAc : Continuous A := by
    dsimp [A]
    fun_prop
  let g : closedBall (0 : Plane) 1 → ℂ := f ∘ A
  have hgc : Continuous g := hf.comp_continuous hAc hA
  have hgi : Function.Injective g := by
    intro p q hpq
    have heq : A p = A q := hi (hA p) (hA q) hpq
    dsimp [A] at heq
    have heq' : L.symm (p : Plane) = L.symm (q : Plane) :=
      (smul_right_injective ℂ hr.ne') (add_left_cancel heq)
    exact Subtype.ext (L.symm.injective heq')
  let : CompactSpace (closedBall (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let e : closedBall (0 : Plane) 1 ≃ₜ Set.range g :=
    (hgc.isClosedEmbedding hgi).isEmbedding.toHomeomorph
  let V : Set ℂ := Subtype.val '' (e '' {z | (z : Plane) ∈ ball 0 1})
  have hVo : IsOpen V := isOpen_embedded_open_disk e
  have hxV : f x ∈ V := by
    let p : closedBall (0 : Plane) 1 := ⟨0, by simp⟩
    refine ⟨e p, ⟨p, ?_, rfl⟩, ?_⟩
    · simp [p]
    · change g p = f x
      simp [g, A, p]
  have hVU : V ⊆ f '' U := by
    rintro _ ⟨_, ⟨p, _, rfl⟩, rfl⟩
    exact ⟨A p, hA p, rfl⟩
  exact Filter.mem_of_superset (hVo.mem_nhds hxV) hVU

end LatticeProb
