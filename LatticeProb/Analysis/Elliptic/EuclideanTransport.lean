import LatticeProb.Analysis.Elliptic.Dirichlet
import LatticeProb.Analysis.Elliptic.Examples
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Euclidean coordinate transport

The coordinate equivalence preserves the Euclidean quadratic domains and Hessian trace.
The norm on the coordinate target is used only for its topology and differentiation.
-/

namespace LatticeProb.Elliptic

open scoped BigOperators

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => Fin d → ℝ
local notation "q" => EuclideanSpace.equiv (Fin d) ℝ

/-- Squared Euclidean distance is the sum of squared coordinate differences. -/
theorem dist_sq_eq_sum (x c : E) :
    dist x c ^ 2 = ∑ i, (q x i - q c i) ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq (x - c)

/-- A positive-radius Euclidean ball has the quadratic coordinate description. -/
theorem image_ball_eq (c : E) {R : ℝ} (hR : 0 < R) :
    q '' Metric.ball c R = {y : V | ∑ i, (y i - q c i) ^ 2 < R ^ 2} := by
  ext z
  obtain ⟨x, rfl⟩ := (q).surjective z
  rw [(q).injective.mem_set_image, Metric.mem_ball, Set.mem_setOf_eq,
    ← dist_sq_eq_sum]
  exact (sq_lt_sq₀ dist_nonneg hR.le).symm

/-- Closure commutes with the coordinate homeomorphism. -/
theorem image_closure_equiv (S : Set E) : q '' closure S = closure (q '' S) :=
  (q).toHomeomorph.image_closure S

/-- Frontier commutes with the coordinate homeomorphism. -/
theorem image_frontier_equiv (S : Set E) : q '' frontier S = frontier (q '' S) :=
  (q).toHomeomorph.image_frontier S

/-- The closure of a positive-radius ball has the weak quadratic inequality. -/
theorem image_closure_ball_eq (c : E) {R : ℝ} (hR : 0 < R) :
    q '' closure (Metric.ball c R) =
      {y : V | ∑ i, (y i - q c i) ^ 2 ≤ R ^ 2} := by
  rw [closure_ball c hR.ne']
  ext z
  obtain ⟨x, rfl⟩ := (q).surjective z
  rw [(q).injective.mem_set_image, Metric.mem_closedBall, Set.mem_setOf_eq,
    ← dist_sq_eq_sum]
  exact (sq_le_sq₀ dist_nonneg hR.le).symm

/-- The Hessian trace is invariant under the Euclidean coordinate equivalence. -/
theorem laplacian_comp_equiv (u : V → ℝ) (y : E) :
    Laplacian.laplacian (u ∘ q) y = laplacian u (q y) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (u ∘ q) (EuclideanSpace.basisFun (Fin d) ℝ)]
  unfold laplacian secondPartial
  apply Finset.sum_congr rfl
  intro i _
  have h := (q).iteratedFDerivWithin_comp_right u uniqueDiffOn_univ
    (Set.mem_univ (q y)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single, Pi.single_apply]

/-- A classical coordinate solution transports to the Euclidean ball. -/
theorem isClassicalDirichletSolution_transport (c : E) {R : ℝ} (hR : 0 < R)
    {μ a₀ : ℝ} {h u : V → ℝ}
    (hu : IsClassicalDirichletSolution (q '' Metric.ball c R) μ a₀ h u) :
    ContDiffOn ℝ 2 (u ∘ q) (Metric.ball c R) ∧
      ContinuousOn (u ∘ q) (closure (Metric.ball c R)) ∧
      (∀ y ∈ Metric.sphere c R, (u ∘ q) y = 0) ∧
      ∀ y ∈ Metric.ball c R,
        μ * (u ∘ q) y - a₀ * Laplacian.laplacian (u ∘ q) y = (h ∘ q) y := by
  refine ⟨hu.1.comp (q).contDiff.contDiffOn (fun x hx => ⟨x, hx, rfl⟩),
    hu.2.1.comp (q).continuous.continuousOn ?_, ?_, ?_⟩
  · intro x hx
    rw [← image_closure_equiv]
    exact ⟨x, hx, rfl⟩
  · intro y hy
    apply hu.2.2.1
    rw [← image_frontier_equiv, frontier_ball c hR.ne']
    exact ⟨y, hy, rfl⟩
  · intro y hy
    rw [laplacian_comp_equiv]
    exact hu.2.2.2 (q y) ⟨y, hy, rfl⟩

/-- The Euclidean formulation characterizes the coordinate classical solution exactly. -/
theorem isClassicalDirichletSolution_transport_iff (c : E) {R : ℝ} (hR : 0 < R)
    {μ a₀ : ℝ} {h u : V → ℝ} :
    IsClassicalDirichletSolution (q '' Metric.ball c R) μ a₀ h u ↔
      ContDiffOn ℝ 2 (u ∘ q) (Metric.ball c R) ∧
      ContinuousOn (u ∘ q) (closure (Metric.ball c R)) ∧
      (∀ y ∈ Metric.sphere c R, (u ∘ q) y = 0) ∧
      ∀ y ∈ Metric.ball c R,
        μ * (u ∘ q) y - a₀ * Laplacian.laplacian (u ∘ q) y = (h ∘ q) y := by
  refine ⟨isClassicalDirichletSolution_transport c hR, ?_⟩
  rintro ⟨hd, hc, hb, he⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (q).contDiffOn_comp_iff.mp
    simpa only [(q).injective.preimage_image] using hd
  · have ht := hc.comp (q).symm.continuous.continuousOn
      (show Set.MapsTo (q).symm (closure (q '' Metric.ball c R))
        (closure (Metric.ball c R)) from fun z hz => by
          rw [← image_closure_equiv] at hz
          rcases hz with ⟨x, hx, rfl⟩
          simpa only [(q).symm_apply_apply] using hx)
    simpa only [Function.comp_def, (q).apply_symm_apply] using ht
  · intro z hz
    rw [← image_frontier_equiv, frontier_ball c hR.ne'] at hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hb y hy
  · rintro z ⟨y, hy, rfl⟩
    simpa only [Function.comp_apply, laplacian_comp_equiv] using he y hy

/-- The existing nonzero quadratic solution transports to the Euclidean unit ball. -/
theorem quadratic_euclidean_dirichlet (μ a₀ : ℝ) :
    ContDiffOn ℝ 2 (fun x : E => 1 - ∑ i, x i ^ 2) (Metric.ball 0 1) ∧
      ContinuousOn (fun x : E => 1 - ∑ i, x i ^ 2) (closure (Metric.ball 0 1)) ∧
      (∀ x ∈ Metric.sphere (0 : E) 1, 1 - ∑ i, x i ^ 2 = 0) ∧
      ∀ x ∈ Metric.ball (0 : E) 1,
        μ * (1 - ∑ i, x i ^ 2) -
          a₀ * Laplacian.laplacian (fun y : E => 1 - ∑ i, y i ^ 2) x =
            μ * (1 - ∑ i, x i ^ 2) + 2 * d * a₀ := by
  have hball : q '' Metric.ball (0 : E) 1 = unitBall d := by
    rw [image_ball_eq 0 (by norm_num)]
    ext x
    simp only [Set.mem_setOf_eq, map_zero, Pi.zero_apply, sub_zero, one_pow,
      mem_unitBall_iff]
  have hu := quadratic_isClassicalDirichletSolution (d := d) μ a₀
  rw [← hball] at hu
  exact isClassicalDirichletSolution_transport 0 (by norm_num) hu

/-- The transported quadratic equals one at the center of its domain. -/
theorem quadratic_euclidean_center :
    (0 : E) ∈ Metric.ball (0 : E) 1 ∧ (1 - ∑ i : Fin d, (0 : E) i ^ 2) = 1 := by
  simp

end

end LatticeProb.Elliptic
