import Mathlib

/-! # Second-order Peano expansion

A differentiable gradient yields a second-order expansion with symmetric coefficient.
-/

open Filter Asymptotics Metric Set
open scoped Topology InnerProductSpace

namespace LatticeProb.PegdenSmart

/-- A second-order expansion with a self-adjoint coefficient. -/
def PeanoAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : E → ℝ) (x : E) : Prop :=
  ∃ (p : E) (B : E →L[ℝ] E), IsSelfAdjoint B ∧
    (fun y => u y - u x - ⟪p, y - x⟫_ℝ - 1 / 2 * ⟪B (y - x), y - x⟫_ℝ) =o[𝓝 x]
      fun y => ‖y - x‖ ^ 2

/-- A differentiable gradient has a symmetric derivative and gives a Peano expansion. -/
theorem peano_of_fderiv (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u : E → ℝ) (V : E → E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hu : ∀ᶠ y in 𝓝 x, HasFDerivAt u (V y) y) (hV : HasFDerivAt V H x) :
    (∀ v w, H v w = H w v) ∧
      (fun y => u y - u x - V x (y - x) - 1 / 2 * H (y - x) (y - x)) =o[𝓝 x]
        (fun y => ‖y - x‖ ^ 2) ∧ PeanoAt u x := by
  have hs : ∀ v w, H v w = H w v := second_derivative_symmetric_of_eventually hu hV
  have hr : (fun y => u y - u x - V x (y - x) - 1 / 2 * H (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
    let R : E → ℝ := fun y => u y - u x - V x (y - x) - 1 / 2 * H (y - x) (y - x)
    let R' : E → E →L[ℝ] ℝ := fun y => V y - V x - H (y - x)
    have hd : ∀ y ∈ ball x r, HasFDerivWithinAt R (R' y) (ball x r) y := by
      intro y hy
      have hyu := hball hy
      have hid : HasFDerivAt (fun z : E => z - x) (ContinuousLinearMap.id ℝ E) y := by
        simpa using (hasFDerivAt_id y).sub_const x
      have hq := ((H.hasFDerivAt.comp y hid).clm_apply hid).const_mul (1 / 2 : ℝ)
      have hl := (V x).hasFDerivAt.comp y hid
      have h := ((hyu.sub_const (u x)).sub hl).sub hq
      apply HasFDerivAt.hasFDerivWithinAt
      convert h using 1
      · rfl
      · ext z
        simp only [R', sub_apply, smul_apply, add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.flip_apply, Function.comp_apply, smul_eq_mul]
        rw [hs z (y - x)]
        ring
    have ho : R' =o[𝓝[ball x r] x] fun y => ‖y - x‖ ^ 1 := by
      have h := hV.isLittleO.mono (nhdsWithin_le_nhds (s := ball x r))
      simpa only [R', pow_one, isLittleO_norm_right] using h
    have h := (convex_ball x r).isLittleO_pow_succ (mem_ball_self hr) hd ho
    rw [nhdsWithin_eq_nhds.mpr (ball_mem_nhds x hr)] at h
    simpa [R] using h
  refine ⟨hs, hr, ?_⟩
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (V x),
    InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) H, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro v w
    rw [ContinuousLinearMap.coe_coe, InnerProductSpace.continuousLinearMapOfBilin_apply,
      real_inner_comm, InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact hs v w
  · refine hr.congr_left fun y => ?_
    rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.continuousLinearMapOfBilin_apply]

end LatticeProb.PegdenSmart
