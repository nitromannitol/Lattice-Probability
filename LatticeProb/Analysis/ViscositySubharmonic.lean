import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Viscosity subharmonic and superharmonic functions

A function `v` is viscosity subharmonic on a set `U` if every function `φ` that is twice
continuously differentiable at a point `x ∈ U` and touches `v` from above at `x` (that is,
`v - φ` has a local maximum at `x`) satisfies `0 ≤ Δ φ x`. Viscosity superharmonic functions are
defined dually with local minima and `Δ φ x ≤ 0`. Here `Δ` is `InnerProductSpace.laplacian` on a
finite-dimensional real inner product space `E` of dimension `d`.

The Laplacian of `‖x‖ ^ 2` is `2 d`. Hence, if every test function touching `u` from above at a
point of `U` has Laplacian at least `-K` there, then `u + K / (2 d) ‖x‖ ^ 2` is viscosity
subharmonic on `U`; dually, if every test function touching `u` from below has Laplacian at most
`K`, then `u - K / (2 d) ‖x‖ ^ 2` is viscosity superharmonic on `U`.

## Main results

* `LatticeProb.Ishii.IsViscSubharmonic`, `LatticeProb.Ishii.IsViscSuperharmonic`: the definitions.
* `LatticeProb.Ishii.IsViscSubharmonic.le_of_le_on_sphere`: comparison with a harmonic function.
* `LatticeProb.Ishii.laplacian_norm_sq`: `Δ ‖·‖ ^ 2 = 2 d`.
* `LatticeProb.Ishii.isViscSubharmonic_add_sq`, `LatticeProb.Ishii.isViscSuperharmonic_sub_sq`:
  the quadratic shifts.
-/

open InnerProductSpace
open Laplacian

namespace LatticeProb.Ishii

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `v` is viscosity subharmonic on `U`: whenever a function `φ`, twice continuously
differentiable at `x ∈ U`, touches `v` from above at `x`, its Laplacian at `x` is nonnegative. -/
def IsViscSubharmonic (U : Set E) (v : E → ℝ) : Prop :=
  ∀ x ∈ U, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun y => v y - φ y) x → 0 ≤ Δ φ x

/-- `v` is viscosity superharmonic on `U`: whenever a function `φ`, twice continuously
differentiable at `x ∈ U`, touches `v` from below at `x`, its Laplacian at `x` is nonpositive. -/
def IsViscSuperharmonic (U : Set E) (v : E → ℝ) : Prop :=
  ∀ x ∈ U, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => v y - φ y) x → Δ φ x ≤ 0

/-- The Laplacian of the squared norm is twice the dimension. -/
theorem laplacian_norm_sq (x : E) :
    Δ (fun y : E => ‖y‖ ^ 2) x = 2 * Module.finrank ℝ E := by
  have h2 : fderiv ℝ (fderiv ℝ fun y : E => ‖y‖ ^ 2) x = 2 • innerSL ℝ := by
    rw [fderiv_norm_sq]
    exact ContinuousLinearMap.fderiv (2 • innerSL ℝ (E := E))
  have hb : ∀ i, innerSL ℝ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) = 1 := by
    intro i
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq,
      (stdOrthonormalBasis ℝ E).orthonormal.1 i, one_pow]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, h2]
  simp [hb, mul_comm]

/-- In dimension zero every Laplacian vanishes. -/
theorem laplacian_eq_zero_of_finrank_eq_zero (hd : Module.finrank ℝ E = 0) (f : E → ℝ) (x : E) :
    Δ f x = 0 := by
  have : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hd]; infer_instance
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp

/-- The Laplacian at `x` of `c ‖·‖ ^ 2` is `c · 2 d`. -/
theorem laplacian_smul_norm_sq (c : ℝ) (x : E) :
    Δ (c • fun y : E => ‖y‖ ^ 2) x = c * (2 * Module.finrank ℝ E) := by
  rw [laplacian_smul c (contDiff_norm_sq ℝ (n := 2)).contDiffAt, laplacian_norm_sq, smul_eq_mul]

/-- A continuous viscosity subharmonic function is bounded above by a harmonic function
on a ball if the same inequality holds on the sphere. -/
theorem IsViscSubharmonic.le_of_le_on_sphere [Nontrivial E] {U : Set E} {v : E → ℝ}
    (hv : ContinuousOn v U) (hvisc : IsViscSubharmonic U v)
    {a : E} {r : ℝ} (hball : Metric.closedBall a r ⊆ U) {h : E → ℝ}
    (hhc : ContinuousOn h (Metric.closedBall a r))
    (hh : HarmonicOnNhd h (Metric.ball a r))
    (hboundary : ∀ x ∈ Metric.sphere a r, v x ≤ h x) :
    ∀ x ∈ Metric.ball a r, v x ≤ h x := by
  intro x hx
  by_contra hn
  have hm : 0 < v x - h x := sub_pos.mpr (lt_of_not_ge hn)
  have hx' : x ∈ Metric.closedBall a r := Metric.ball_subset_closedBall hx
  have hc : IsCompact (Metric.closedBall a r) := isCompact_closedBall a r
  obtain ⟨y, _, hymax⟩ := hc.exists_isMaxOn ⟨x, hx'⟩
    ((continuous_norm.pow 2).continuousOn : ContinuousOn (fun z : E => ‖z‖ ^ 2) _)
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt hm (‖y‖ ^ 2)
  let F : E → ℝ := fun z => v z - h z + ε * ‖z‖ ^ 2
  have hFc : ContinuousOn F (Metric.closedBall a r) :=
    ((hv.mono hball).sub hhc).add ((continuous_norm.pow 2).const_mul ε).continuousOn
  obtain ⟨z, hz, hzmax⟩ := hc.exists_isMaxOn ⟨x, hx'⟩ hFc
  have hFx : v x - h x ≤ F x := by
    dsimp [F]
    nlinarith [sq_nonneg ‖x‖]
  have hFz : v x - h x ≤ F z := hFx.trans (hzmax hx')
  have hzball : z ∈ Metric.ball a r := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    by_contra hznot
    have heq : dist z a = r := le_antisymm hz (le_of_not_gt hznot)
    have hzs : z ∈ Metric.sphere a r := Metric.mem_sphere.mpr heq
    have hq : ‖z‖ ^ 2 ≤ ‖y‖ ^ 2 := hymax hz
    have hb := hboundary z hzs
    dsimp [F] at hFz
    nlinarith [mul_le_mul_of_nonneg_left hq hε.le]
  have hlocal : IsLocalMax F z := hzmax.isLocalMax
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzball) Metric.ball_subset_closedBall)
  have hh' := hh z hzball
  have hq : ContDiffAt ℝ 2 (ε • fun w : E => ‖w‖ ^ 2) z :=
    ((contDiff_norm_sq ℝ (n := 2)).const_smul ε).contDiffAt
  have hmax : IsLocalMax (fun w => v w - (h - ε • fun w : E => ‖w‖ ^ 2) w) z := by
    have heq : (fun w => v w - (h - ε • fun w : E => ‖w‖ ^ 2) w) = F := by
      funext w
      simp only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact hlocal
  have hvineq := hvisc z (hball hz) (h - ε • fun w : E => ‖w‖ ^ 2)
    (hh'.1.sub hq) hmax
  rw [hh'.1.laplacian_sub hq, laplacian_smul_norm_sq] at hvineq
  have hhlap : Δ h z = 0 := hh'.2.self_of_nhds
  have hdim : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  rw [hhlap] at hvineq
  nlinarith

/-- **Quadratic shift, subharmonic case.** If every function touching `u` from above at a point
of `U` has Laplacian at least `-K` there, then `u + K / (2 d) ‖x‖ ^ 2` is viscosity subharmonic
on `U`. -/
theorem isViscSubharmonic_add_sq {U : Set E} {u : E → ℝ} {K : ℝ}
    (h : ∀ x ∈ U, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun y => u y - φ y) x → -K ≤ Δ φ x) :
    IsViscSubharmonic U fun x => u x + K / (2 * Module.finrank ℝ E) * ‖x‖ ^ 2 := by
  intro x hx φ hφ hmax
  rcases eq_or_ne (Module.finrank ℝ E) 0 with hd | hd
  · exact (laplacian_eq_zero_of_finrank_eq_zero hd φ x).ge
  set c : ℝ := K / (2 * Module.finrank ℝ E) with hc
  have hq : ContDiffAt ℝ 2 (c • fun y : E => ‖y‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ (n := 2)).const_smul c).contDiffAt
  have heq : (fun y => u y - (φ - c • fun y : E => ‖y‖ ^ 2) y)
      = fun y => (u y + c * ‖y‖ ^ 2) - φ y := by
    funext y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key := h x hx (φ - c • fun y : E => ‖y‖ ^ 2) (hφ.sub hq) (heq ▸ hmax)
  rw [hφ.laplacian_sub hq, laplacian_smul_norm_sq] at key
  have hcK : c * (2 * Module.finrank ℝ E) = K := by
    rw [hc]
    exact div_mul_cancel₀ K (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hd))
  linarith

/-- **Quadratic shift, superharmonic case.** If every function touching `u` from below at a point
of `U` has Laplacian at most `K` there, then `u - K / (2 d) ‖x‖ ^ 2` is viscosity superharmonic
on `U`. -/
theorem isViscSuperharmonic_sub_sq {U : Set E} {u : E → ℝ} {K : ℝ}
    (h : ∀ x ∈ U, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => u y - φ y) x → Δ φ x ≤ K) :
    IsViscSuperharmonic U fun x => u x - K / (2 * Module.finrank ℝ E) * ‖x‖ ^ 2 := by
  intro x hx φ hφ hmin
  rcases eq_or_ne (Module.finrank ℝ E) 0 with hd | hd
  · exact (laplacian_eq_zero_of_finrank_eq_zero hd φ x).le
  set c : ℝ := K / (2 * Module.finrank ℝ E) with hc
  have hq : ContDiffAt ℝ 2 (c • fun y : E => ‖y‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ (n := 2)).const_smul c).contDiffAt
  have heq : (fun y => u y - (φ + c • fun y : E => ‖y‖ ^ 2) y)
      = fun y => (u y - c * ‖y‖ ^ 2) - φ y := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key := h x hx (φ + c • fun y : E => ‖y‖ ^ 2) (hφ.add hq) (heq ▸ hmin)
  rw [hφ.laplacian_add hq, laplacian_smul_norm_sq] at key
  have hcK : c * (2 * Module.finrank ℝ E) = K := by
    rw [hc]
    exact div_mul_cancel₀ K (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hd))
  linarith

end LatticeProb.Ishii
