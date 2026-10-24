import LatticeProb.Analysis.Elliptic.Examples
import LatticeProb.Analysis.Elliptic.EuclideanTransport

/-!
# Regularity of Euclidean balls in coordinates

Every positive-radius Euclidean ball has a regular quadratic defining function with locally
finite Euclidean Hölder norms. The coordinate image is connected and contains its center.
-/

namespace LatticeProb.Elliptic

open LatticeProb.Euclidean.Lattice
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The coordinate derivative of a translated quadratic defining function. -/
theorem partialDeriv_ball_quadratic (c : Fin d → ℝ) (R : ℝ)
    (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (fun y => (∑ k, (y k - c k) ^ 2) - R ^ 2) x =
      2 * (x i - c i) := by
  have heq : (fun y : Fin d → ℝ => (∑ k, (y k - c k) ^ 2) - R ^ 2) =
      (fun y => -(R ^ 2) + 1 * ∑ k, y k ^ 2) ∘ (fun y => y - c) := by
    ext y
    simp only [Function.comp_apply, Pi.sub_apply]
    ring
  rw [heq, partialDeriv]
  change fderiv ℝ (fun y => -(R ^ 2) + 1 * ∑ k, (y - c) k ^ 2) x _ = _
  rw [fderiv_comp_sub (f := fun y : Fin d → ℝ =>
    -(R ^ 2) + 1 * ∑ k, y k ^ 2) c]
  change partialDeriv i (fun y => -(R ^ 2) + 1 * ∑ k, y k ^ 2) (x - c) = _
  rw [partialDeriv_affine_sum_sq]
  simp only [mul_one, Pi.sub_apply]

/-- The Hessian of the ball defining function is twice the identity matrix. -/
theorem secondPartial_ball_quadratic (c : Fin d → ℝ) (R : ℝ)
    (i j : Fin d) (x : Fin d → ℝ) :
    secondPartial i j (fun y => (∑ k, (y k - c k) ^ 2) - R ^ 2) x =
      if i = j then 2 else 0 := by
  rw [secondPartial_eq_fderiv_partialDeriv (by fun_prop)]
  rw [show partialDeriv j (fun y => (∑ k, (y k - c k) ^ 2) - R ^ 2) =
    (fun y => 2 * (y j - c j)) from funext (partialDeriv_ball_quadratic c R j)]
  rw [(((hasFDerivAt_apply (𝕜 := ℝ) j x).sub_const (c j)).const_mul 2).fderiv]
  simp [Pi.single_apply, eq_comm]

/-- The translated quadratic has finite `C^{2,σ}` norm on every bounded set. -/
theorem c2HolderNorm_ball_quadratic_lt_top (σ : ℝ) (c : Fin d → ℝ) (R : ℝ)
    {S : Set (Fin d → ℝ)} (hS : Bornology.IsBounded S) :
    c2HolderNorm σ S (fun y => (∑ k, (y k - c k) ^ 2) - R ^ 2) < ⊤ := by
  have hp (i : Fin d) := funext (partialDeriv_ball_quadratic c R i)
  have hs (i j : Fin d) := funext (secondPartial_ball_quadratic c R i j)
  simp only [c2HolderNorm, ENNReal.add_lt_top, ENNReal.sum_lt_top, Finset.mem_univ,
    forall_const]
  refine ⟨⟨⟨supNorm_lt_top_of_continuous hS (by fun_prop), ?_⟩, ?_⟩, ?_⟩
  · intro i
    rw [hp]
    exact supNorm_lt_top_of_continuous hS (by fun_prop)
  · intro i j
    rw [hs]
    exact supNorm_lt_top_of_continuous hS continuous_const
  · intro i j
    rw [hs, holderSeminorm_const]
    exact ENNReal.zero_lt_top

/-- Positive-radius coordinate balls have the quadratic sublevel description. -/
theorem radius_sub_ball_eq (c : Fin d → ℝ) {R : ℝ} (hR : 0 < R) :
    {x | radius (x - c) < R} = {x | ∑ k, (x k - c k) ^ 2 < R ^ 2} := by
  ext x
  change radius (x - c) < R ↔ _
  rw [← sq_lt_sq₀ (radius_nonneg _) hR.le, radius_sq]
  rfl

/-- Every positive-radius Euclidean ball is a regular `C^{2,σ}` domain in coordinates. -/
theorem isC2HolderDomain_ball (σ : ℝ) (c : Fin d → ℝ) {R : ℝ} (hR : 0 < R) :
    IsC2HolderDomain σ {x | radius (x - c) < R} := by
  let q := EuclideanSpace.equiv (Fin d) ℝ
  have heq : {x | radius (x - c) < R} = q '' Metric.ball (q.symm c) R := by
    rw [image_ball_eq _ hR, radius_sub_ball_eq c hR]
    simp only [q, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨isOpen_lt ((radius_continuous d).comp (continuous_id.sub continuous_const))
    continuous_const, ?_, ?_, ?_⟩
  · rw [heq]
    exact (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hR) |>.image q
      q.continuous.continuousOn
  · rw [heq]
    exact q.lipschitz.isBounded_image Metric.isBounded_ball
  · refine ⟨fun x => (∑ k, (x k - c k) ^ 2) - R ^ 2, by fun_prop, ?_, ?_, ?_⟩
    · intro T
      exact c2HolderNorm_ball_quadratic_lt_top σ c R (isBounded_radius_sublevel T)
    · rw [radius_sub_ball_eq c hR]
      ext x
      simp only [Set.mem_setOf_eq, sub_lt_zero]
    · intro x hx hz
      change (∑ k, (x k - c k) ^ 2) - R ^ 2 = 0 at hx
      have hex : ∃ i, x i - c i ≠ 0 := by
        by_contra! h
        have hsum : (∑ k, (x k - c k) ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [h k]
          norm_num
        rw [hsum] at hx
        nlinarith [sq_pos_of_pos hR]
      obtain ⟨i, hi⟩ := hex
      have hp := partialDeriv_ball_quadratic c R i x
      rw [partialDeriv, hz] at hp
      simp only [zero_apply] at hp
      exact hi (by linarith)

/-- The coordinate image of a positive-radius Euclidean ball is a regular domain. -/
theorem isC2HolderDomain_image_ball (σ : ℝ) (c : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 < R) :
    IsC2HolderDomain σ ((EuclideanSpace.equiv (Fin d) ℝ) '' Metric.ball c R) := by
  rw [image_ball_eq c hR, ← radius_sub_ball_eq _ hR]
  exact isC2HolderDomain_ball σ _ hR

/-- A positive-radius coordinate ball is connected, in every dimension. -/
theorem isConnected_radius_sub_ball (c : Fin d → ℝ) {R : ℝ} (hR : 0 < R) :
    IsConnected {x | radius (x - c) < R} :=
  (isC2HolderDomain_ball 0 c hR).2.1

/-- The center witnesses nonemptiness of a positive-radius coordinate ball. -/
theorem center_mem_radius_sub_ball (c : Fin d → ℝ) {R : ℝ} (hR : 0 < R) :
    c ∈ {x | radius (x - c) < R} := by
  simpa [radius] using hR

end

end LatticeProb.Elliptic
