/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/HessianTaylorRemainder.lean.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A C² Taylor remainder from oscillation of the actual Hessian

The estimate uses the mean value inequality twice. In particular it does not
require a third derivative.
-/

open Set
namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a convex set `S` where `f` is twice differentiable and the Hessian of `f` varies
by at most `ε` in operator norm, the second-order Taylor remainder of `f` at `x` in the
direction `y` is bounded by `ε * ‖y‖ ^ 2`. -/
theorem taylor_remainder_le_of_hessian_oscillation
    {f : E → ℝ} {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hf' : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ f) z)
    {x y : E} (hx : x ∈ S) (hxy : x + y ∈ S)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hH : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) x‖ ≤ ε) :
    |f (x + y) - f x - fderiv ℝ f x y - (1 / 2 : ℝ) *
      fderiv ℝ (fderiv ℝ f) x y y| ≤ ε * ‖y‖ ^ 2 := by
  let H := fderiv ℝ (fderiv ℝ f) x
  let q : ℝ → ℝ := fun s ↦ f (x + s • y) - f x - s * fderiv ℝ f x y -
    (s ^ 2 / 2) * H y y
  let q' : ℝ → ℝ := fun s ↦ (fderiv ℝ f (x + s • y) - fderiv ℝ f x - H (s • y)) y
  have hq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt q (q' s) s := by
    have hpath : HasDerivAt (fun r : ℝ ↦ x + r • y) y s := by
      simpa using ((hasDerivAt_id s).smul_const y).const_add x
    have hcomp := (hf _ (hS.add_smul_mem hx hxy hs)).hasFDerivAt.comp_hasDerivAt s hpath
    have hquad := ((hasDerivAt_pow 2 s).div_const 2).mul_const (H y y)
    have h := ((hcomp.sub_const (f x)).sub ((hasDerivAt_id s).mul_const
      (fderiv ℝ f x y))).sub hquad
    apply h.congr_deriv
    dsimp [q']
    simp only [sub_apply, map_smul, smul_apply, smul_eq_mul]
    ring
  have hqbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) : ‖q' s‖ ≤ ε * ‖y‖ ^ 2 := by
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hgradient : ‖fderiv ℝ f (x + s • y) - fderiv ℝ f x - H (s • y)‖ ≤
        ε * ‖s • y‖ := by
      simpa only [add_sub_cancel_left] using
        hS.norm_image_sub_le_of_norm_fderiv_le' hf' hH hx
          (hS.add_smul_mem hx hxy hs')
    have hnorm : ‖s • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg y) hs.2.le
    calc
      ‖q' s‖ ≤ ‖fderiv ℝ f (x + s • y) - fderiv ℝ f x - H (s • y)‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ y
      _ ≤ (ε * ‖s • y‖) * ‖y‖ := mul_le_mul_of_nonneg_right hgradient (norm_nonneg y)
      _ ≤ (ε * ‖y‖) * ‖y‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnorm hε) (norm_nonneg y)
      _ = ε * ‖y‖ ^ 2 := by ring
  have hfinal := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs ↦ (hq s hs).hasDerivWithinAt) hqbound
  simpa [q, H, Real.norm_eq_abs] using hfinal

omit [NormedSpace ℝ E] in
/-- A local small quadratic bound and a global quadratic bound give a single
quadratic-plus-quartic estimate: the local constant `ε` multiplies `‖y‖ ^ 2`, and the
global constant `M` is rescaled by `r⁻²` in front of `‖y‖ ^ 4`. -/
theorem quadratic_remainder_le_quadratic_add_quartic
    {R : E → ℝ} {ε M r : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) (hr : 0 < r)
    (hsmall : ∀ y, ‖y‖ ≤ r → |R y| ≤ ε * ‖y‖ ^ 2)
    (hglobal : ∀ y, |R y| ≤ M * ‖y‖ ^ 2) (y : E) :
    |R y| ≤ ε * ‖y‖ ^ 2 + (M / r ^ 2) * ‖y‖ ^ 4 := by
  by_cases hy : ‖y‖ ≤ r
  · exact (hsmall y hy).trans (le_add_of_nonneg_right (by positivity))
  · have hyr : r ≤ ‖y‖ := (lt_of_not_ge hy).le
    have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
    have hsquare : r ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hr.le hyr 2
    have hratio : M ≤ (M / r ^ 2) * ‖y‖ ^ 2 := by
      calc
        M = (M / r ^ 2) * r ^ 2 := (div_mul_cancel₀ M (ne_of_gt hrsq)).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsquare (by positivity)
    calc
      |R y| ≤ M * ‖y‖ ^ 2 := hglobal y
      _ ≤ ((M / r ^ 2) * ‖y‖ ^ 2) * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
      _ ≤ ε * ‖y‖ ^ 2 + (M / r ^ 2) * ‖y‖ ^ 4 := by
        nlinarith [mul_nonneg hε (sq_nonneg ‖y‖)]

/-- A bounded uniformly continuous actual Hessian gives a uniform Taylor
remainder at every starting point, with an explicit quartic tail. -/
theorem uniform_taylor_remainder_of_uniformContinuous_hessian
    {f : E → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (fderiv ℝ f))
    (hHuc : UniformContinuous (fderiv ℝ (fderiv ℝ f)))
    {M : ℝ} (hM : 0 ≤ M) (hHbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x y : E,
      |f (x + y) - f x - fderiv ℝ f x y - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ f) x y y| ≤
          ε * ‖y‖ ^ 2 + (2 * M / r ^ 2) * ‖y‖ ^ 4 := by
  obtain ⟨r, hr, hdist⟩ := (Metric.uniformContinuous_iff_le
    (f := fderiv ℝ (fderiv ℝ f))).mp hHuc ε hε
  refine ⟨r, hr, fun x y ↦ ?_⟩
  let R : E → ℝ := fun z ↦ f (x + z) - f x - fderiv ℝ f x z - (1 / 2 : ℝ) *
    fderiv ℝ (fderiv ℝ f) x z z
  have hlocal (z : E) (hz : ‖z‖ ≤ r) : |R z| ≤ ε * ‖z‖ ^ 2 := by
    apply taylor_remainder_le_of_hessian_oscillation (convex_closedBall x r)
      (fun w _ ↦ hf w) (fun w _ ↦ hf' w)
      (Metric.mem_closedBall_self hr.le) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
      hε.le
    intro w hw
    calc
      ‖fderiv ℝ (fderiv ℝ f) w - fderiv ℝ (fderiv ℝ f) x‖ =
          dist (fderiv ℝ (fderiv ℝ f) w) (fderiv ℝ (fderiv ℝ f) x) :=
        (dist_eq_norm (fderiv ℝ (fderiv ℝ f) w) (fderiv ℝ (fderiv ℝ f) x)).symm
      _ ≤ ε := hdist (Metric.mem_closedBall.mp hw)
  have hglobal (z : E) : |R z| ≤ (2 * M) * ‖z‖ ^ 2 := by
    apply taylor_remainder_le_of_hessian_oscillation convex_univ
      (fun w _ ↦ hf w) (fun w _ ↦ hf' w) (mem_univ x) (mem_univ (x + z))
      (by positivity)
    intro w hw
    calc
      ‖fderiv ℝ (fderiv ℝ f) w - fderiv ℝ (fderiv ℝ f) x‖ ≤
          ‖fderiv ℝ (fderiv ℝ f) w‖ + ‖fderiv ℝ (fderiv ℝ f) x‖ :=
        norm_sub_le (fderiv ℝ (fderiv ℝ f) w) (fderiv ℝ (fderiv ℝ f) x)
      _ ≤ M + M := add_le_add (hHbound w) (hHbound x)
      _ = 2 * M := by ring
  exact quadratic_remainder_le_quadratic_add_quartic hε.le (by positivity) hr
    hlocal hglobal y

/-- The uniform remainder hypothesis is automatic for a compactly supported
C² function, with no independent bound or continuity assumption on its Hessian. -/
theorem uniform_taylor_remainder_of_contDiff_compactSupport
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ x y : E,
      |f (x + y) - f x - fderiv ℝ f x y - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ f) x y y| ≤ ε * ‖y‖ ^ 2 + C * ‖y‖ ^ 4 := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hHcont : Continuous (fderiv ℝ (fderiv ℝ f)) := hDf.continuous_fderiv (by norm_num)
  have hHsupp : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) :=
    (hsupp.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have hbound : ∃ M : ℝ, ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M :=
    HasCompactSupport.exists_bound_of_continuous
      (f := fderiv ℝ (fderiv ℝ f)) hHsupp hHcont
  obtain ⟨M, hMbound⟩ := hbound
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ f) (0 : E))).trans (hMbound (0 : E))
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hDfdiff : Differentiable ℝ (fderiv ℝ f) := hDf.differentiable (by norm_num)
  have hHuc : UniformContinuous (fderiv ℝ (fderiv ℝ f)) :=
    hHsupp.uniformContinuous_of_continuous hHcont
  obtain ⟨r, hr, hR⟩ := uniform_taylor_remainder_of_uniformContinuous_hessian
    (f := f) (M := M) (ε := ε) hfdiff hDfdiff hHuc hM hMbound hε
  exact ⟨2 * M / r ^ 2, by positivity, hR⟩

end LatticeProb

/-! ### Nonvacuity: a concrete compactly supported C² function -/

namespace HessianTaylorRemainderExample

/-- The bump function on `EuclideanSpace ℝ (Fin 2)` centred at the origin, with
inner radius `1` and outer radius `2`. -/
def bump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump function is `C²`. -/
theorem bump_contDiff : ContDiff ℝ 2 (⇑bump) := bump.contDiff

/-- The bump function has compact support. -/
theorem bump_hasCompactSupport : HasCompactSupport (⇑bump) := bump.hasCompactSupport

/-- The uniform quadratic-plus-quartic Taylor remainder bound holds for the concrete
bump function, obtained from `LatticeProb.uniform_taylor_remainder_of_contDiff_compactSupport`. -/
theorem bump_uniform_taylor_remainder {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ x y : EuclideanSpace ℝ (Fin 2),
      |⇑bump (x + y) - ⇑bump x - fderiv ℝ (⇑bump) x y - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ (⇑bump)) x y y| ≤ ε * ‖y‖ ^ 2 + C * ‖y‖ ^ 4 :=
  LatticeProb.uniform_taylor_remainder_of_contDiff_compactSupport
    bump_contDiff bump_hasCompactSupport hε

end HessianTaylorRemainderExample
