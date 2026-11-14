import Mathlib

/-!
# A cutoff identity

Integration by parts gives the energy identity for a smooth function and a smooth compactly
supported cutoff.
-/

open MeasureTheory
open scoped BigOperators ContDiff InnerProductSpace
open Laplacian

namespace LatticeProb.PegdenSmart

private theorem contDiff_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem integral_mul_fderiv_eq_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {F ψ : E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (v : E) :
    ∫ x, F x * fderiv ℝ ψ x v ∂μ = -∫ x, fderiv ℝ F x v * ψ x ∂μ := by
  have hF'c : Continuous fun x => fderiv ℝ F x v := (contDiff_fderiv_apply hF v).continuous
  have hψ'c : Continuous fun x => fderiv ℝ ψ x v := (contDiff_fderiv_apply hψ v).continuous
  have hψ'cs : HasCompactSupport fun x => fderiv ℝ ψ x v := hc.fderiv_apply ℝ v
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hF.differentiable (by simp) x) (fun x _ => hψ.differentiable (by simp) x)
  · exact (hF'c.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hF.continuous.mul hψ'c).integrable_of_hasCompactSupport hψ'cs.mul_left
  · exact (hF.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left

private theorem laplacian_eq_sum_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Δ ψ = fun y => ∑ i, fderiv ℝ (fun y' => fderiv ℝ ψ y' (stdOrthonormalBasis ℝ E i)) y
      (stdOrthonormalBasis ℝ E i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  rw [fderiv_clm_apply hd (differentiableAt_const (stdOrthonormalBasis ℝ E i))]
  simp

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 400000 in
/-- The cutoff energy identity, with derivatives expressed in an orthonormal basis. -/
theorem integral_cutoff_sq_grad_sq {w θ : E → ℝ} (hw : ContDiff ℝ ∞ w)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ x, θ x ^ 2 * ∑ i, (fderiv ℝ w x (stdOrthonormalBasis ℝ E i)) ^ 2) =
      -(∫ x, θ x ^ 2 * w x * Δ w x) -
        2 * ∫ x, θ x * w x * ∑ i,
          fderiv ℝ θ x (stdOrthonormalBasis ℝ E i) *
            fderiv ℝ w x (stdOrthonormalBasis ℝ E i) := by
  let b := stdOrthonormalBasis ℝ E
  let D := fun (f : E → ℝ) (i) (x : E) => fderiv ℝ f x (b i)
  have hD : ∀ i, ContDiff ℝ ∞ (D w i) := fun i => contDiff_fderiv_apply hw (b i)
  have hT : ∀ i, ContDiff ℝ ∞ (D θ i) := fun i => contDiff_fderiv_apply hθ (b i)
  have ha : ∀ i, Integrable (fun x => θ x ^ 2 * (D w i x) ^ 2) := by
    intro i
    have hcont : Continuous (fun x => θ x ^ 2 * (D w i x) ^ 2) := by fun_prop
    apply hcont.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hc
    intro x hx
    have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hz]
  have hb : ∀ i, Integrable (fun x => θ x ^ 2 * w x * D (D w i) i x) := by
    intro i
    have hd : Continuous (D (D w i) i) := (contDiff_fderiv_apply (hD i) (b i)).continuous
    have hcont : Continuous (fun x => θ x ^ 2 * w x * D (D w i) i x) := by fun_prop
    apply hcont.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hc
    intro x hx
    have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hz]
  have ht : ∀ i, Integrable (fun x => θ x * w x * (D θ i x * D w i x)) := by
    intro i
    have hcont : Continuous (fun x => θ x * w x * (D θ i x * D w i x)) := by fun_prop
    apply hcont.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hc
    intro x hx
    have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hz]
  have hψ : ContDiff ℝ ∞ (fun x => θ x ^ 2 * w x) := (hθ.pow 2).mul hw
  have hψc : HasCompactSupport (fun x => θ x ^ 2 * w x) := by
    apply HasCompactSupport.intro hc
    intro x hx
    have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hz]
  have hcoord : ∀ i, (∫ x, θ x ^ 2 * (D w i x) ^ 2) =
      -(∫ x, θ x ^ 2 * w x * D (D w i) i x) -
      2 * ∫ x, θ x * w x * (D θ i x * D w i x) := by
    intro i
    have hp : ∀ x, fderiv ℝ (fun x => θ x ^ 2 * w x) x (b i) =
        2 * θ x * D θ i x * w x + θ x ^ 2 * D w i x := by
      intro x
      change fderiv ℝ ((fun x => θ x ^ 2) * w) x (b i) = _
      rw [fderiv_mul ((hθ.pow 2).differentiable (by simp) x) (hw.differentiable (by simp) x),
        fderiv_fun_pow 2 (hθ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      dsimp [D]
      ring
    have h := integral_mul_fderiv_eq_neg (μ := (volume : Measure E)) (F := D w i)
      (hD i) hψ hψc (b i)
    simp_rw [hp] at h
    have he : (fun x => D w i x * (2 * θ x * D θ i x * w x + θ x ^ 2 * D w i x)) =
        fun x => 2 * (θ x * w x * (D θ i x * D w i x)) + θ x ^ 2 * (D w i x) ^ 2 := by
      funext x; ring
    have he' : (fun x => D (D w i) i x * (θ x ^ 2 * w x)) =
        fun x => θ x ^ 2 * w x * D (D w i) i x := by
      funext x; simp only [D]; ring
    rw [he, he', integral_add ((ht i).const_mul 2) (ha i), integral_const_mul] at h
    linarith
  rw [laplacian_eq_sum_fderiv hw]
  change (∫ x, θ x ^ 2 * ∑ i, (D w i x) ^ 2) =
    -(∫ x, θ x ^ 2 * w x * ∑ i, D (D w i) i x) -
      2 * ∫ x, θ x * w x * ∑ i, D θ i x * D w i x
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => ha i), integral_finsetSum _ (fun i _ => hb i),
    integral_finsetSum _ (fun i _ => ht i)]
  simp_rw [hcoord]
  simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]

end LatticeProb.PegdenSmart
