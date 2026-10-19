import LatticeProb.Analysis.HarmonicBridge
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Harmonicity under an affine change of variables

For a `C²` function `f` on a finite-dimensional real inner product space, the Laplacian of
`w ↦ f (x + c • w)` is `c ^ 2` times the Laplacian of `f` at `x + c • w`. Consequently a function
harmonic on an open set `U` is harmonic on the preimage of `U` under `w ↦ x + c • w`.
-/

open Set Function Filter
open scoped Topology
open Laplacian

namespace LatticeProb

/-- The Laplacian of `w ↦ f (x + c • w)` at `w` equals `c ^ 2` times the Laplacian of `f` at
`x + c • w`, for a `C²` function `f`. -/
theorem laplacian_affine_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) (c : ℝ) (w : E) :
    Δ (fun w ↦ f (x + c • w)) w = c ^ 2 * Δ f (x + c • w) := by
  have hF : ContDiff ℝ 2 (fun z ↦ f (x + z)) :=
    hf.comp (by fun_prop)
  have hD : iteratedFDeriv ℝ 2 (fun w ↦ f (x + c • w)) w =
      c ^ 2 • iteratedFDeriv ℝ 2 f (x + c • w) := by
    rw [congrFun (iteratedFDeriv_comp_const_smul (i := 2) c hF) w]
    show c ^ 2 • iteratedFDeriv ℝ 2 (fun z ↦ f (x + z)) (c • w) = _
    rw [iteratedFDeriv_comp_add_left]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun w ↦ f (x + c • w)),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f]
  simp only [hD, smul_apply, smul_eq_mul, Finset.mul_sum]

/-- A function harmonic on an open set `U` is harmonic, after the affine change of variables
`w ↦ x + c • w`, on the preimage of `U`. -/
theorem IsHarmonicOn.comp_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {h : E → ℝ} {U : Set E} (hU : IsOpen U) (hh : IsHarmonicOn h U)
    (x : E) (c : ℝ) :
    IsHarmonicOn (fun w ↦ h (x + c • w)) ((fun w ↦ x + c • w) ⁻¹' U) := by
  have hφ : ContDiff ℝ 2 (fun w : E ↦ x + c • w) := by fun_prop
  refine ⟨hh.1.comp hφ.contDiffOn (mapsTo_preimage _ _), fun w hw ↦ ?_⟩
  have hwU : x + c • w ∈ U := hw
  obtain ⟨g, V, hV, hKV, -, hg, -, -, heq, -⟩ :=
    hh.exists_compactSupport_eq_near_compact isCompact_singleton hU
      (singleton_subset_iff.mpr hwU)
  have hVw : (fun y ↦ x + c • y) ⁻¹' V ∈ 𝓝 w :=
    (hφ.continuous.continuousAt).preimage_mem_nhds (hV.mem_nhds (hKV (mem_singleton _)))
  have hcongr : (fun y ↦ h (x + c • y)) =ᶠ[𝓝 w] (fun y ↦ g (x + c • y)) := by
    filter_upwards [hVw] with y hy
    exact (heq (show x + c • y ∈ V from hy)).symm
  have hgh : g =ᶠ[𝓝 (x + c • w)] h := by
    filter_upwards [hV.mem_nhds (hKV (mem_singleton _))] with y hy
    exact heq hy
  rw [(InnerProductSpace.laplacian_congr_nhds hcongr).eq_of_nhds,
    laplacian_affine_comp hg x c w, (InnerProductSpace.laplacian_congr_nhds hgh).eq_of_nhds,
    hh.laplacian_eq_zero hwU, mul_zero]

namespace HarmonicScalingExample

/-- Domain test: the preimage of the open unit ball of `EuclideanSpace ℝ (Fin 2)` under
`w ↦ (√2)⁻¹ • w` is the open ball of radius `√2` about the origin. -/
theorem preimage_ball_scale_sqrt_two :
    (fun w : EuclideanSpace ℝ (Fin 2) ↦ (Real.sqrt 2)⁻¹ • w) ⁻¹' Metric.ball 0 1 =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt 2) := by
  ext w
  have hpos : 0 < (Real.sqrt 2)⁻¹ := by positivity
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hpos]
  rw [inv_mul_lt_iff₀ (Real.sqrt_pos.mpr two_pos), mul_one]

/-- The affine transfer of the Laplacian applies to the quadratic function `y ↦ ‖y‖ ^ 2` on
`EuclideanSpace ℝ (Fin 2)`, at any base point and scale. -/
theorem laplacian_affine_comp_sq_norm (x w : EuclideanSpace ℝ (Fin 2)) (c : ℝ) :
    Δ (fun v ↦ ‖x + c • v‖ ^ 2) w =
      c ^ 2 * Δ (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) (x + c • w) :=
  laplacian_affine_comp (contDiff_norm_sq ℝ) x c w

/-- The affine transfer of harmonicity applies to the constant harmonic function `1` on the open
unit ball of `EuclideanSpace ℝ (Fin 2)`, at any base point and scale. -/
theorem const_comp_affine_isHarmonicOn (x : EuclideanSpace ℝ (Fin 2)) (c : ℝ) :
    IsHarmonicOn (fun w ↦ (fun _ : EuclideanSpace ℝ (Fin 2) ↦ (1 : ℝ)) (x + c • w))
      ((fun w ↦ x + c • w) ⁻¹' Metric.ball 0 1) :=
  IsHarmonicOn.comp_affine Metric.isOpen_ball HarmonicBridgeExample.const_isHarmonicOn_ball x c

end HarmonicScalingExample

end LatticeProb
