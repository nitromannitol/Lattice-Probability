import LatticeProb.Analysis.HessianLpReduction

/-! # Scaling of the local Hessian estimate

The affine change of variables `y ↦ x + ρ • y` carries the local estimate on the balls about `0`
of radii `1 / 2` and `4 / 3` to the balls about `x` of radii `ρ / 2` and `4 * ρ / 3`.

## Main statements

* `HessianAdapter.L5_scale`: `LocalUnitStmt d` implies `LocalBallStmt d`.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace HessianAdapter

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated derivatives of `y ↦ w (x + ρ • y)`. -/
theorem iteratedFDeriv_comp_affine (w : E → ℝ) (x : E) {ρ : ℝ} (hρ : ρ ≠ 0) (n : ℕ) (y : E) :
    iteratedFDeriv ℝ n (fun z => w (x + ρ • z)) y =
      ρ ^ n • iteratedFDeriv ℝ n w (x + ρ • y) := by
  let g : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 ρ hρ)
  have hg : ∀ z, g z = ρ • z := fun z => by simp [g, Units.smul_def]
  have hcomp : (fun z => w (x + ρ • z)) = (fun z => w (x + z)) ∘ g := by
    funext z
    simp [hg]
  have hh := g.iteratedFDerivWithin_comp_right (fun z => w (x + z)) (s := Set.univ)
    uniqueDiffOn_univ (x := y) (Set.mem_univ _) n
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hh
  rw [hcomp, hh, iteratedFDeriv_comp_add_left, hg]
  ext m
  have hs := (iteratedFDeriv ℝ n w (x + ρ • y)).map_smul_univ (fun _ => ρ) m
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hs
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, hg]
  exact hs

/-- The Hessian norm of `y ↦ w (x + ρ • y)`. -/
theorem norm_hessian_comp_affine (w : E → ℝ) (x : E) {ρ : ℝ} (hρ : ρ ≠ 0) (y : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z => w (x + ρ • z))) y‖ =
      ρ ^ 2 * ‖fderiv ℝ (fderiv ℝ w) (x + ρ • y)‖ := by
  have h := congrArg norm (iteratedFDeriv_comp_affine w x hρ 2 y)
  rw [norm_smul, ← norm_iteratedFDeriv_fderiv (n := 1),
    ← norm_iteratedFDeriv_fderiv (n := 1)] at h
  simpa only [norm_iteratedFDeriv_one, norm_pow, Real.norm_eq_abs, sq_abs] using h

end Calculus

/-- The Laplacian of `y ↦ w (x + ρ • y)`. -/
theorem laplacian_comp_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (w : E → ℝ) (x : E) {ρ : ℝ} (hρ : ρ ≠ 0) (y : E) :
    Δ (fun z => w (x + ρ • z)) y = ρ ^ 2 * Δ w (x + ρ • y) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_affine w x hρ, smul_apply, smul_eq_mul,
    Finset.mul_sum]

/-- The preimage of `B(x, ρ R)` under `y ↦ x + ρ • y`. -/
theorem preimage_affine_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) :
    (fun y => x + ρ • y) ⁻¹' ball x (ρ * R) = ball (0 : E) R := by
  ext y
  simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
    Real.norm_of_nonneg hρ.le]
  exact mul_lt_mul_iff_right₀ hρ

/-- The image of Lebesgue measure on `B(0, R)` under `y ↦ x + ρ • y`. -/
theorem map_restrict_affine {d : ℕ} (x : Euc d) {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) :
    (volume.restrict (ball (0 : Euc d) R)).map (fun y => x + ρ • y) =
      ENNReal.ofReal |(ρ ^ d)⁻¹| • volume.restrict (ball x (ρ * R)) := by
  have hmeas : Measurable (fun y : Euc d => x + ρ • y) :=
    (continuous_const.add (continuous_const_smul ρ)).measurable
  have hmap : (volume : Measure (Euc d)).map (fun y => x + ρ • y) =
      ENNReal.ofReal |(ρ ^ d)⁻¹| • volume := by
    have h1 : (fun y : Euc d => x + ρ • y) = (fun z => x + z) ∘ (fun y => ρ • y) := rfl
    rw [h1, ← Measure.map_map (measurable_const_add x) (measurable_const_smul ρ),
      Measure.map_addHaar_smul volume hρ.ne', finrank_euclideanSpace_fin, Measure.map_smul,
      map_add_left_eq_self]
    exact (measurable_const_add x).aemeasurable
  rw [← Measure.restrict_smul, ← hmap, Measure.restrict_map hmeas measurableSet_ball,
    preimage_affine_ball x hρ R]

/-- `L^p` norms on balls under `y ↦ x + ρ • y`. -/
theorem eLpNorm_comp_affine {d : ℕ} (f : Euc d → ℝ) (x : Euc d) {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ)
    (p : ℝ≥0∞) :
    eLpNorm (fun y => f (x + ρ • y)) p (volume.restrict (ball (0 : Euc d) R)) =
      ENNReal.ofReal |(ρ ^ d)⁻¹| ^ (1 / p).toReal *
        eLpNorm f p (volume.restrict (ball x (ρ * R))) := by
  have hT : MeasurableEmbedding (fun y : Euc d => x + ρ • y) :=
    ((Homeomorph.smulOfNeZero ρ hρ.ne').trans (Homeomorph.addLeft x)).measurableEmbedding
  have hc : ENNReal.ofReal |(ρ ^ d)⁻¹| ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [← smul_eq_mul, ← eLpNorm_smul_measure_of_ne_zero hc, ← map_restrict_affine x hρ R,
    hT.eLpNorm_map_measure]
  rfl

/-- L5. Change of variables `y ↦ x + ρ y`. -/
theorem L5_scale (d : ℕ) (h : LocalUnitStmt d) : LocalBallStmt d := by
  intro p hp hpt ρ hρ
  obtain ⟨K, hK, hbound⟩ := h p hp hpt
  set c : ℝ≥0∞ := ENNReal.ofReal |(ρ ^ d)⁻¹|
  set a : ℝ≥0∞ := ‖ρ ^ 2‖ₑ * c ^ (1 / p).toReal with ha_def
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 :=
    mul_ne_zero (enorm_ne_zero.2 (pow_ne_zero _ hρ.ne'))
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hct).ne'
  have hat : a ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hct)
  refine ⟨K * max 1 a⁻¹, ENNReal.mul_ne_top hK (max_ne_top ENNReal.one_ne_top
    (ENNReal.inv_ne_top.2 ha0)), ?_⟩
  intro x w hw hfin
  have r1 : ρ * (4 / 3) = 4 * ρ / 3 := by ring
  have r2 : ρ * (1 / 2) = ρ / 2 := by ring
  have hv : ContDiffOn ℝ ∞ (fun y => w (x + ρ • y)) (ball (0 : Euc d) (4 / 3)) := by
    refine hw.comp (contDiff_const.add (contDiff_const_smul ρ)).contDiffOn ?_
    intro y hy
    rw [← preimage_affine_ball x hρ, r1] at hy
    exact hy
  have hlap : Δ (fun y => w (x + ρ • y)) = (ρ ^ 2) • fun y => Δ w (x + ρ • y) := by
    funext y
    rw [laplacian_comp_affine w x hρ.ne', Pi.smul_apply, smul_eq_mul]
  have hhess : (fun y => ‖fderiv ℝ (fderiv ℝ (fun z => w (x + ρ • z))) y‖) =
      (ρ ^ 2) • fun y => ‖fderiv ℝ (fderiv ℝ w) (x + ρ • y)‖ := by
    funext y
    rw [norm_hessian_comp_affine w x hρ.ne', Pi.smul_apply, smul_eq_mul]
  have e1 : eLpNorm (Δ (fun y => w (x + ρ • y))) p (volume.restrict (ball (0 : Euc d) (4 / 3))) =
      a * eLpNorm (Δ w) p (volume.restrict (ball x (4 * ρ / 3))) := by
    rw [hlap, eLpNorm_const_smul, eLpNorm_comp_affine (Δ w) x hρ, r1, ha_def, mul_assoc]
  have e2 : eLpNorm (fun y => w (x + ρ • y)) ⊤ (volume.restrict (ball (0 : Euc d) (4 / 3))) =
      eLpNorm w ⊤ (volume.restrict (ball x (4 * ρ / 3))) := by
    rw [eLpNorm_comp_affine w x hρ, r1]
    simp
  have e3 : eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ (fun z => w (x + ρ • z))) y‖) p
      (volume.restrict (ball (0 : Euc d) (1 / 2))) =
      a * eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p (volume.restrict (ball x (ρ / 2))) := by
    rw [hhess, eLpNorm_const_smul,
      eLpNorm_comp_affine (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) x hρ, r2, ha_def, mul_assoc]
  obtain ⟨hL, hW⟩ := ENNReal.add_ne_top.1 hfin
  have hfin' : eLpNorm (Δ (fun y => w (x + ρ • y))) p
      (volume.restrict (ball (0 : Euc d) (4 / 3))) +
      eLpNorm (fun y => w (x + ρ • y)) ⊤ (volume.restrict (ball (0 : Euc d) (4 / 3))) ≠ ⊤ := by
    rw [e1, e2]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hat hL, hW⟩
  have hb := hbound _ hv hfin'
  rw [e1, e2, e3] at hb
  set L := eLpNorm (Δ w) p (volume.restrict (ball x (4 * ρ / 3)))
  set W := eLpNorm w ⊤ (volume.restrict (ball x (4 * ρ / 3)))
  set H := eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p (volume.restrict (ball x (ρ / 2)))
  have key : a * L + W ≤ a * (max 1 a⁻¹ * (L + W)) := by
    rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc]
    refine add_le_add ?_ ?_
    · calc a * L = a * 1 * L := by rw [mul_one]
        _ ≤ a * max 1 a⁻¹ * L := by gcongr; exact le_max_left _ _
    · calc W = a * a⁻¹ * W := by rw [ENNReal.mul_inv_cancel ha0 hat, one_mul]
        _ ≤ a * max 1 a⁻¹ * W := by gcongr; exact le_max_right _ _
  have hb' : a * H ≤ a * (K * max 1 a⁻¹ * (L + W)) := by
    calc a * H ≤ K * (a * L + W) := hb
      _ ≤ K * (a * (max 1 a⁻¹ * (L + W))) := by gcongr
      _ = a * (K * max 1 a⁻¹ * (L + W)) := by ring
  calc H = a⁻¹ * (a * H) := by rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
    _ ≤ a⁻¹ * (a * (K * max 1 a⁻¹ * (L + W))) := by gcongr
    _ = K * max 1 a⁻¹ * (L + W) := by rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]

end HessianAdapter
