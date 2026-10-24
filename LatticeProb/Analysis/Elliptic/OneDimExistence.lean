import LatticeProb.Analysis.Elliptic.OneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.ProjIcc

/-!
# Existence for the one-dimensional Dirichlet problem

Continuous interval data admit a twice continuously differentiable solution of the
constant-coefficient elliptic equation with zero endpoint values.
-/

namespace LatticeProb.Elliptic

open Set Filter
open scoped Topology

noncomputable section

/-- The primitive of a continuous real function is continuously differentiable. -/
theorem contDiff_one_interval_primitive {g : ℝ → ℝ} (hg : Continuous g) (α : ℝ) :
    ContDiff ℝ 1 (fun x => ∫ t in α..x, g t) := by
  have hd (x : ℝ) : HasDerivAt (fun x => ∫ t in α..x, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  exact contDiff_one_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt, by
      convert hg using 1
      exact funext fun x => (hd x).deriv⟩

/-- Continuous data on the real line have a classical particular solution for positive mass. -/
theorem exists_particular_solution_pos {f : ℝ → ℝ} (hf : Continuous f)
    {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (α : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ v α = 0 ∧
      ∀ x, a * k ^ 2 * v x - a * deriv (deriv v) x = f x := by
  let S : ℝ → ℝ := fun x => Real.sinh (k * (x - α))
  let C : ℝ → ℝ := fun x => Real.cosh (k * (x - α))
  let A : ℝ → ℝ := fun x => ∫ t in α..x, S t * f t
  let B : ℝ → ℝ := fun x => ∫ t in α..x, C t * f t
  have hS (x : ℝ) : HasDerivAt S (k * C x) x := by
    simpa only [S, C, mul_one, one_mul, id_eq, mul_comm] using
      ((((hasDerivAt_id x).sub_const α).const_mul k).sinh)
  have hC (x : ℝ) : HasDerivAt C (k * S x) x := by
    simpa only [S, C, mul_one, one_mul, id_eq, mul_comm] using
      ((((hasDerivAt_id x).sub_const α).const_mul k).cosh)
  have hSc : ContDiff ℝ 1 S := by dsimp [S]; fun_prop
  have hCc : ContDiff ℝ 1 C := by dsimp [C]; fun_prop
  have hAc : ContDiff ℝ 1 A :=
    contDiff_one_interval_primitive (hSc.continuous.mul hf) α
  have hBc : ContDiff ℝ 1 B :=
    contDiff_one_interval_primitive (hCc.continuous.mul hf) α
  have hA (x : ℝ) : HasDerivAt A (S x * f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((hSc.continuous.mul hf).intervalIntegrable _ _)
      (hSc.continuous.mul hf).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hSc.continuous.mul hf).continuousAt
  have hB (x : ℝ) : HasDerivAt B (C x * f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((hCc.continuous.mul hf).intervalIntegrable _ _)
      (hCc.continuous.mul hf).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hCc.continuous.mul hf).continuousAt
  let v : ℝ → ℝ := fun x => (C x * A x - S x * B x) / (a * k)
  let w : ℝ → ℝ := fun x => (S x * A x - C x * B x) / a
  have hv (x : ℝ) : HasDerivAt v (w x) x := by
    apply ((((hC x).mul (hA x)).sub ((hS x).mul (hB x))).div_const (a * k)
      ).congr_deriv
    dsimp [w]
    field_simp [ha.ne', hk.ne']
    ring
  have hw (x : ℝ) : HasDerivAt w (k ^ 2 * v x - f x / a) x := by
    apply ((((hS x).mul (hA x)).sub ((hC x).mul (hB x))).div_const a
      ).congr_deriv
    have hidentity : C x ^ 2 - S x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    dsimp [v]
    field_simp [ha.ne', hk.ne']
    nlinarith [congrArg (fun t : ℝ => t * f x) hidentity]
  have hvderiv : deriv v = w := funext fun x => (hv x).deriv
  have hvc : ContDiff ℝ 2 v := by
    apply (contDiff_succ_iff_deriv (n := 1)).mpr
    refine ⟨fun x => (hv x).differentiableAt, ?_, ?_⟩
    · norm_num
    · rw [hvderiv]
      exact ((hSc.mul hAc).sub (hCc.mul hBc)).div_const a
  refine ⟨v, hvc, ?_, ?_⟩
  · simp [v, A, B]
  · intro x
    rw [hvderiv, (hw x).deriv]
    field_simp [ha.ne', hk.ne']
    ring

/-- Positive mass gives a classical scalar solution with zero endpoint values. -/
theorem exists_scalar_dirichlet_pos {α β μ a : ℝ} {f : ℝ → ℝ}
    (hαβ : α < β) (hμ : 0 < μ) (ha : 0 < a) (hf : ContinuousOn f (Icc α β)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ v α = 0 ∧ v β = 0 ∧
      ∀ x ∈ Ioo α β, μ * v x - a * deriv (deriv v) x = f x := by
  let g : ℝ → ℝ := fun x => f (projIcc α β hαβ.le x)
  have hg : Continuous g := hf.restrict.comp continuous_projIcc
  have hg_eq (x : ℝ) (hx : x ∈ Icc α β) : g x = f x := by
    dsimp [g]
    rw [projIcc_of_mem hαβ.le hx]
  let k := Real.sqrt (μ / a)
  have hk : 0 < k := Real.sqrt_pos.mpr (div_pos hμ ha)
  have hkμ : a * k ^ 2 = μ := by
    dsimp [k]
    rw [Real.sq_sqrt (div_nonneg hμ.le ha.le), mul_div_cancel₀ _ ha.ne']
  obtain ⟨p, hpc, hpα, hpe⟩ := exists_particular_solution_pos hg ha hk α
  let q : ℝ → ℝ := fun x => Real.sinh (k * (x - α))
  let q' : ℝ → ℝ := fun x => k * Real.cosh (k * (x - α))
  have hq (x : ℝ) : HasDerivAt q (q' x) x := by
    simpa only [q, q', mul_one, one_mul, id_eq, mul_comm] using
      ((((hasDerivAt_id x).sub_const α).const_mul k).sinh)
  have hq' (x : ℝ) : HasDerivAt q' (k ^ 2 * q x) x := by
    apply (((((hasDerivAt_id x).sub_const α).const_mul k).cosh).const_mul k
      ).congr_deriv
    dsimp [q]
    ring
  have hqβ : q β ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hk (sub_pos.mpr hαβ))).ne'
  let v : ℝ → ℝ := fun x => p x - (p β / q β) * q x
  have hqc : ContDiff ℝ 2 q := by dsimp [q]; fun_prop
  have hvc : ContDiff ℝ 2 v := hpc.sub (contDiff_const.mul hqc)
  have hvderiv : deriv v = fun x => deriv p x - (p β / q β) * q' x := by
    ext x
    exact ((hpc.differentiable (by norm_num) x).hasDerivAt.sub
      ((hq x).const_mul _)).deriv
  have hvsecond (x : ℝ) : deriv (deriv v) x =
      deriv (deriv p) x - (p β / q β) * (k ^ 2 * q x) := by
    rw [hvderiv]
    exact ((hpc.differentiable_deriv_two x).hasDerivAt.sub
      ((hq' x).const_mul _)).deriv
  refine ⟨v, hvc, ?_, ?_, ?_⟩
  · simp [v, q, hpα]
  · dsimp [v]
    rw [div_mul_cancel₀ _ hqβ, sub_self]
  · intro x hx
    rw [hvsecond]
    have he := hpe x
    rw [hkμ, hg_eq x (Ioo_subset_Icc_self hx)] at he
    dsimp [v]
    calc
      μ * (p x - p β / q β * q x) -
          a * (deriv (deriv p) x - p β / q β * (k ^ 2 * q x)) =
          μ * p x - a * deriv (deriv p) x +
            (a * k ^ 2 - μ) * (p β / q β * q x) := by ring
      _ = f x := by rw [hkμ, sub_self, zero_mul, add_zero, he]

/-- In one dimension an open coordinate interval is the Euclidean ball of the same radius. -/
theorem one_dim_interval_eq_abs (c R : ℝ) :
    {x : Fin 1 → ℝ | c - R < x 0 ∧ x 0 < c + R} =
      {x : Fin 1 → ℝ | |x 0 - c| < R} := by
  ext x
  simp only [mem_setOf_eq, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The interval carrier uses exactly the Euclidean radius in dimension one. -/
theorem one_dim_interval_eq_euclidean_ball (c R : ℝ) :
    {x : Fin 1 → ℝ | c - R < x 0 ∧ x 0 < c + R} =
      {x : Fin 1 → ℝ | LatticeProb.Euclidean.Lattice.radius (x - fun _ => c) < R} := by
  rw [one_dim_interval_eq_abs]
  ext x
  simp only [mem_setOf_eq, LatticeProb.Euclidean.Lattice.radius, Fin.sum_univ_one,
    Pi.sub_apply, Real.sqrt_sq_eq_abs]

/-- Every continuous datum on a closed interval has a classical one-dimensional
Dirichlet solution for positive mass and diffusivity. -/
theorem exists_classicalDirichletSolution_one {α β μ a₀ : ℝ}
    {f : (Fin 1 → ℝ) → ℝ} (hαβ : α < β) (hμ : 0 < μ) (ha : 0 < a₀)
    (hf : ContinuousOn f (closure {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β})) :
    ∃ u, IsClassicalDirichletSolution {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β}
      μ a₀ f u := by
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ => ℝ)
  let U : Set (Fin 1 → ℝ) := {x | α < x 0 ∧ x 0 < β}
  have hclosure : closure U = e ⁻¹' Icc α β := by
    change closure (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' Icc α β
    rw [← e.toHomeomorph.preimage_closure, closure_Ioo hαβ.ne]
  have hfrontier : frontier U = e ⁻¹' {α, β} := by
    change frontier (e.toHomeomorph ⁻¹' Ioo α β) = e.toHomeomorph ⁻¹' {α, β}
    rw [← e.toHomeomorph.preimage_frontier, frontier_Ioo hαβ]
  have hfc : ContinuousOn (fun t : ℝ => f (fun _ => t)) (Icc α β) := by
    apply hf.comp (show Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) by
      fun_prop).continuousOn
    intro t ht
    change (fun _ => t) ∈ closure U
    rw [hclosure]
    exact ht
  obtain ⟨v, hvc, hvα, hvβ, hve⟩ := exists_scalar_dirichlet_pos hαβ hμ ha hfc
  let u : (Fin 1 → ℝ) → ℝ := fun x => v (x 0)
  have huc : ContDiff ℝ 2 u := hvc.comp (by fun_prop)
  refine ⟨u, huc.contDiffOn, huc.continuous.continuousOn, ?_, ?_⟩
  · intro x hx
    change x ∈ frontier U at hx
    rw [hfrontier] at hx
    rcases hx with hx | hx
    · change x 0 = α at hx
      change v (x 0) = 0
      rw [hx, hvα]
    · change x 0 = β at hx
      change v (x 0) = 0
      rw [hx, hvβ]
  · intro x hx
    have hxconst : (fun _ : Fin 1 => x 0) = x := by
      ext i
      exact congrArg x (Subsingleton.elim 0 i)
    have hlap := laplacian_one_dim u (x 0)
    rw [hxconst] at hlap
    rw [hlap]
    change μ * v (x 0) - a₀ * deriv (deriv v) (x 0) = f x
    simpa only [hxconst] using hve (x 0) hx

/-- The centered one-dimensional Euclidean ball admits a classical Dirichlet solution. -/
theorem exists_classicalDirichletSolution_one_ball {c R μ a₀ : ℝ}
    {f : (Fin 1 → ℝ) → ℝ} (hR : 0 < R) (hμ : 0 < μ) (ha : 0 < a₀)
    (hf : ContinuousOn f (closure {x : Fin 1 → ℝ | |x 0 - c| < R})) :
    ∃ u, IsClassicalDirichletSolution {x : Fin 1 → ℝ | |x 0 - c| < R} μ a₀ f u := by
  rw [← one_dim_interval_eq_abs] at hf ⊢
  exact exists_classicalDirichletSolution_one (by linarith) hμ ha hf

/-- Constant unit forcing on the unit interval is an instance with nonzero data. -/
theorem exists_classicalDirichletSolution_one_unit :
    ∃ u, IsClassicalDirichletSolution {x : Fin 1 → ℝ | |x 0| < 1}
      1 1 (fun _ => 1) u := by
  simpa only [sub_zero] using exists_classicalDirichletSolution_one_ball
    (c := 0) (R := 1) (μ := 1) (a₀ := 1) (f := fun _ => 1)
    zero_lt_one zero_lt_one zero_lt_one continuousOn_const

end

end LatticeProb.Elliptic
