import LatticeProb.Prob.Percolation.LatticeClusterBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Euclidean localization geometry -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

namespace LatticeProb.Percolation

noncomputable section

/-- A forward unit step has Euclidean length one. -/
theorem dist_embedding_add_unit {d : ℕ} (x : Vertex d) (i : Fin d) :
    dist (latticeEuclideanEmbedding (x + unit i)) (latticeEuclideanEmbedding x) = 1 := by
  rw [dist_eq_norm]
  have heq : latticeEuclideanEmbedding (x + unit i) - latticeEuclideanEmbedding x =
      PiLp.single 2 i (1 : ℝ) := by
    ext j
    change ((x j + unit i j : ℤ) : ℝ) - (x j : ℝ) = (Pi.single i (1 : ℝ) : Fin d → ℝ) j
    by_cases h : j = i <;> simp [unit, h]
  rw [heq, PiLp.norm_single]
  norm_num

/-- The working-scale inequality implies the numerical localization bounds. -/
theorem localization_scale_bounds {D α m T : ℝ} (hD : 0 ≤ D) (hα : 0 < α)
    (hαhalf : α ≤ 1 / 2)
    (hwork : max (max 64 m) (2 * T) < D ^ α) :
    4096 < D ∧ m < D / 64 ∧ T < D / 128 ∧ 8 * m ≤ D / 4 := by
  have h64 : (64 : ℝ) < D ^ α :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hwork
  have hm' : m < D ^ α := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hwork
  have hT' : 2 * T < D ^ α := lt_of_le_of_lt (le_max_right _ _) hwork
  have hD1 : 1 ≤ D := by
    by_contra h
    have := Real.rpow_le_one hD (le_of_not_ge h) hα.le
    linarith
  have hs : D ^ α ≤ Real.sqrt D := by
    calc
      D ^ α ≤ D ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 hαhalf
      _ = Real.sqrt D := (Real.sqrt_eq_rpow D).symm
  have hs0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hs2 : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hlarge : 4096 < D := by nlinarith
  have hratio : Real.sqrt D < D / 64 := by nlinarith
  have hm'': m < D / 64 := lt_trans hm' (lt_of_le_of_lt hs hratio)
  have hT'': T < D / 128 := by nlinarith
  refine ⟨hlarge, hm'', hT'', ?_⟩
  linarith

/-- Points in the localization ball remain separated from a pole and its forward neighbor. -/
theorem localization_ball_separation {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (x y : Vertex d) (j : Fin d) (v : C)
    (hD : 4096 < dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y))
    (hv : v ∈ componentEuclideanBall C x
      (dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 4)) :
    3 * dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 4 <
      dist (latticeEuclideanEmbedding v.val) (latticeEuclideanEmbedding y) ∧
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 2 <
      dist (latticeEuclideanEmbedding v.val) (latticeEuclideanEmbedding (y + unit j)) := by
  have hv' := (mem_componentEuclideanBall C x _ v).mp hv
  have htri := dist_triangle (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding v.val)
    (latticeEuclideanEmbedding y)
  have htri' := dist_triangle (latticeEuclideanEmbedding v.val)
    (latticeEuclideanEmbedding (y + unit j)) (latticeEuclideanEmbedding y)
  have hunit := dist_embedding_add_unit y j
  rw [dist_comm (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding v.val)] at htri
  constructor <;> linarith

/-- Under the working-scale bounds both poles are outside the localization ball, and
    every point of the ball is beyond any threshold bounded by `T`. -/
theorem localization_poles_and_threshold {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (x y : Vertex d) (j : Fin d) (p q : C)
    (hp : p.val = y) (hq : q.val = y + unit j) (T : ℝ)
    (hD : 4096 < dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y))
    (hT : T < dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 128) :
    p ∉ componentEuclideanBall C x
        (dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 4) ∧
    q ∉ componentEuclideanBall C x
        (dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 4) ∧
    ∀ v ∈ componentEuclideanBall C x
        (dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 4),
      T < dist (latticeEuclideanEmbedding v.val) (latticeEuclideanEmbedding y) ∧
      T < dist (latticeEuclideanEmbedding v.val) (latticeEuclideanEmbedding (y + unit j)) := by
  constructor
  · intro hv
    have h := (localization_ball_separation C x y j p hD hv).1
    rw [hp, dist_self] at h
    linarith
  constructor
  · intro hv
    have h := (localization_ball_separation C x y j q hD hv).2
    rw [hq, dist_self] at h
    linarith
  · intro v hv
    obtain ⟨h₁, h₂⟩ := localization_ball_separation C x y j v hD hv
    constructor <;> linarith

end
end LatticeProb.Percolation
