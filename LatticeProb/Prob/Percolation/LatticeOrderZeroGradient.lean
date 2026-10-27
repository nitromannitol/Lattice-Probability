import LatticeProb.Prob.Percolation.LatticeOrderZeroTranslation
import LatticeProb.Prob.Percolation.LatticeLocalGradient

/-! A conditional local gradient estimate from the order-zero approximation. -/

open MeasureTheory
open scoped ProbabilityTheory

namespace LatticeProb.Percolation

/-- The order-zero input yields one all-centers event carrying a local gradient estimate. -/
theorem exists_all_centers_order_zero_gradient
    (input : LatticeProb.External.ArmstrongDarioOrderZero)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ K : ℝ), 0 < s ∧ 0 < θ ∧ 0 < K ∧
      ∃ X : Vertex d → Configuration d → ℝ,
        (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧
        (∀ z, Integrable (fun ω => Real.exp (Real.rpow (X z ω / θ) s))
          (latticeBondLaw d p)) ∧
        (∀ z, (∫ ω, Real.exp (Real.rpow (X z ω / θ) s) ∂latticeBondLaw d p) ≤ 2) ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              ∀ x : uniqueInfiniteComponent h', ∀ R : ℝ,
                8 * max 2 (X x.val ω) ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R,
                    (∀ w : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj z w →
                        w ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R) →
                    componentLaplacian (uniqueInfiniteComponent h') u z = 0) →
                  ∀ y : uniqueInfiniteComponent h',
                    (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                    (u x - u y) ^ 2 ≤
                      K * (max 2 (X x.val ω)) ^ d / R ^ 2 *
                        (componentBallL2 (uniqueInfiniteComponent h') x.val R u) ^ 2 := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hXn, hXi, hXb, hAE⟩ :=
    exists_all_centers_constant_approximation input d hd p hp hp1
  obtain ⟨K, hK, hgrad⟩ := component_local_gradient d hd
  refine ⟨s, θ, 16 * K * C ^ 2, hs, hθ, by positivity, X, hXm, hXn, hXi, hXb, ?_⟩
  filter_upwards [hAE] with ω hω
  obtain ⟨h, hall⟩ := hω
  refine ⟨h, ?_⟩
  intro h' x R hR u hu y hxy
  let m := max 2 (X x.val ω)
  have hm : 2 ≤ m := le_max_left _ _
  have hRm : 8 * m ≤ R := hR
  have hmpos : 0 < m := by linarith
  have hRpos : 0 < R := by linarith
  have hXR : 2 * X x.val ω ≤ R := by
    have := le_max_right 2 (X x.val ω)
    dsimp [m] at hR hm
    linarith
  obtain ⟨c, hc⟩ := hall h' x.val R hXR u hu
  have hcr := hc (4 * m) (by
    have := le_max_right 2 (X x.val ω)
    dsimp [m]
    linarith) (by linarith)
  have hh : ∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val (2 * m),
      componentLaplacian (uniqueInfiniteComponent h') (u - fun _ => c) z = 0 := by
    intro z hz
    have hz' := (mem_componentEuclideanBall (uniqueInfiniteComponent h') x.val _ z).mp hz
    have hzR : z ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R :=
      (mem_componentEuclideanBall (uniqueInfiniteComponent h') x.val R z).mpr (by linarith)
    have hn : ∀ w : uniqueInfiniteComponent h',
        (componentGraph (uniqueInfiniteComponent h')).Adj z w →
        w ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R := by
      intro w hzw
      apply (mem_componentEuclideanBall (uniqueInfiniteComponent h') x.val R w).mpr
      have he : dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z.val) = 1 :=
        dist_embedding_adj hzw.symm
      have ht := dist_triangle (latticeEuclideanEmbedding w.val)
        (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val)
      linarith
    have hzu := hu z hzR hn
    simp only [componentLaplacian, Pi.sub_apply] at hzu ⊢
    convert hzu using 1
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hg := hgrad ω (uniqueInfiniteComponent h') x y m hm (u - fun _ => c) hxy hh
  have hnon := componentBallL2_nonneg (uniqueInfiniteComponent h') x.val (4 * m) (u - fun _ => c)
  have hsq : (componentBallL2 (uniqueInfiniteComponent h') x.val (4 * m) (u - fun _ => c)) ^ 2 ≤
      (C * (4 * m / R) * componentBallL2 (uniqueInfiniteComponent h') x.val R u) ^ 2 :=
    (sq_le_sq₀ hnon (le_trans hnon hcr)).2 hcr
  have hpw : m ^ d = m ^ (d - 2) * m ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  calc
    _ = (u x - c - (u y - c)) ^ 2 := by ring
    _ ≤ K * m ^ (d - 2) *
        (componentBallL2 (uniqueInfiniteComponent h') x.val (4 * m) (u - fun _ => c)) ^ 2 := by
      simpa only [Pi.sub_apply] using hg
    _ ≤ K * m ^ (d - 2) *
        (C * (4 * m / R) * componentBallL2 (uniqueInfiniteComponent h') x.val R u) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by rw [hpw]; field_simp; ring

end LatticeProb.Percolation
