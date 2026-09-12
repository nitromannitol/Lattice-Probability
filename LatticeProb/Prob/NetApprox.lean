/-
A partition of unity attached to a finite set of points of a metric space, and the
interpolation of a function by its values on that set.

For a finite set `F` and a scale `η > 0` the tent weight of `x ∈ F` at `y` is
`max 0 (η - dist x y)`, which vanishes as soon as `x` is at distance `η` from `y`.  Dividing by
the total weight gives, at every point `y` which is within `η` of some point of `F`, a finite
convex combination supported on the points of `F` near `y`, and `netApprox F η v` is the
corresponding interpolation of the values of `v` on `F`.

Two properties are what the interpolation is for.  It is close to `v` at every point where `v`
varies little at scale `η`, because `netApprox F η v y - v y` is a convex combination of the
increments `v x - v y` over points `x` within `η` of `y`; and it is a 1-Lipschitz function of
the values of `v` on `F` in the supremum norm, because the weights are nonnegative and sum to
one.  Together these turn a functional which is uniformly continuous for the supremum norm into
a function of finitely many values of `v`, up to an error controlled by the modulus of
continuity of `v`.
-/
import Mathlib

noncomputable section

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E]

/-- The tent weight of `x` at `y` at scale `η`. -/
def tentWeight (η : ℝ) (x y : E) : ℝ := max 0 (η - dist x y)

/-- The total tent weight of the points `x k` at `y`. -/
def tentSum {m : ℕ} (x : Fin m → E) (η : ℝ) (y : E) : ℝ := ∑ k, tentWeight η (x k) y

/-- The partition of unity attached to the points `x k` at scale `η`. -/
def tentPart {m : ℕ} (x : Fin m → E) (η : ℝ) (k : Fin m) (y : E) : ℝ :=
  tentWeight η (x k) y / tentSum x η y

/-- The interpolation of the values `u k` by the partition of unity. -/
def netApprox {m : ℕ} (x : Fin m → E) (η : ℝ) (u : Fin m → ℝ) (y : E) : ℝ :=
  ∑ k, tentPart x η k y * u k

theorem tentWeight_nonneg (η : ℝ) (x y : E) : 0 ≤ tentWeight η x y := le_max_left _ _

theorem tentSum_nonneg {m : ℕ} (x : Fin m → E) (η : ℝ) (y : E) : 0 ≤ tentSum x η y :=
  Finset.sum_nonneg fun k _ => tentWeight_nonneg η (x k) y

theorem tentPart_nonneg {m : ℕ} (x : Fin m → E) (η : ℝ) (k : Fin m) (y : E) :
    0 ≤ tentPart x η k y :=
  div_nonneg (tentWeight_nonneg η (x k) y) (tentSum_nonneg x η y)

theorem tentSum_pos {m : ℕ} {x : Fin m → E} {η : ℝ} {y : E} (h : ∃ k, dist (x k) y < η) :
    0 < tentSum x η y := by
  obtain ⟨k, hk⟩ := h
  unfold tentSum
  refine Finset.sum_pos' (fun j _ => tentWeight_nonneg η (x j) y) ⟨k, Finset.mem_univ k, ?_⟩
  have hpos : 0 < η - dist (x k) y := by linarith
  simpa [tentWeight] using hpos

theorem sum_tentPart {m : ℕ} {x : Fin m → E} {η : ℝ} {y : E} (h : 0 < tentSum x η y) :
    ∑ k, tentPart x η k y = 1 := by
  unfold tentPart
  rw [← Finset.sum_div]
  show tentSum x η y / tentSum x η y = 1
  exact div_self (ne_of_gt h)

theorem tentPart_eq_zero {m : ℕ} {x : Fin m → E} {η : ℝ} {k : Fin m} {y : E}
    (h : η ≤ dist (x k) y) : tentPart x η k y = 0 := by
  have hw : tentWeight η (x k) y = 0 := by
    simp [tentWeight, sub_nonpos.mpr h]
  simp [tentPart, hw]

/-- **The interpolation is close to the function it interpolates**, at every point where some
point of the net is within `η` and where the values of the function at those points are within
`δ` of the value `c`. -/
theorem abs_netApprox_sub_le {m : ℕ} {x : Fin m → E} {η δ c : ℝ} {y : E} {u : Fin m → ℝ}
    (hpos : 0 < tentSum x η y) (hmod : ∀ k, dist (x k) y < η → |u k - c| ≤ δ) :
    |netApprox x η u y - c| ≤ δ := by
  have h1 : ∑ k, tentPart x η k y = 1 := sum_tentPart hpos
  have h2 : netApprox x η u y - c = ∑ k, tentPart x η k y * (u k - c) := by
    simp only [netApprox, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  rw [h2]
  calc |∑ k, tentPart x η k y * (u k - c)| ≤ ∑ k, |tentPart x η k y * (u k - c)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, tentPart x η k y * δ := by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases hk : dist (x k) y < η
        · rw [abs_mul, abs_of_nonneg (tentPart_nonneg x η k y)]
          exact mul_le_mul_of_nonneg_left (hmod k hk) (tentPart_nonneg x η k y)
        · have hz : tentPart x η k y = 0 := tentPart_eq_zero (not_lt.mp hk)
          simp [hz]
    _ = δ := by rw [← Finset.sum_mul, h1, one_mul]

/-- **The interpolation is 1-Lipschitz in the interpolated values**, in the supremum norm. -/
theorem abs_netApprox_sub_netApprox_le {m : ℕ} {x : Fin m → E} {η c : ℝ} {y : E}
    {u w : Fin m → ℝ} (hpos : 0 < tentSum x η y) (h : ∀ k, |u k - w k| ≤ c) :
    |netApprox x η u y - netApprox x η w y| ≤ c := by
  have h1 : ∑ k, tentPart x η k y = 1 := sum_tentPart hpos
  have h2 : netApprox x η u y - netApprox x η w y
      = ∑ k, tentPart x η k y * (u k - w k) := by
    simp only [netApprox, mul_sub, Finset.sum_sub_distrib]
  rw [h2]
  calc |∑ k, tentPart x η k y * (u k - w k)| ≤ ∑ k, |tentPart x η k y * (u k - w k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, tentPart x η k y * c := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (tentPart_nonneg x η k y)]
        exact mul_le_mul_of_nonneg_left (h k) (tentPart_nonneg x η k y)
    _ = c := by rw [← Finset.sum_mul, h1, one_mul]

/-- **A compact set has a finite net at every scale**, with its points in the set. -/
theorem exists_net {K : Set E} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ (m : ℕ) (x : Fin m → E), (∀ k, x k ∈ K) ∧ ∀ y ∈ K, ∃ k, dist (x k) y < η := by
  classical
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact hK hη
  refine ⟨htf.toFinset.card, fun k => (htf.toFinset.equivFin.symm k : E), ?_, ?_⟩
  · intro k
    exact hts (htf.mem_toFinset.mp (htf.toFinset.equivFin.symm k).2)
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcov hy)
    refine ⟨htf.toFinset.equivFin ⟨z, htf.mem_toFinset.mpr hz⟩, ?_⟩
    simpa [Metric.mem_ball, dist_comm] using hyz

/-- The interpolation written as a single quotient, which is how its continuity is read off. -/
theorem netApprox_eq_div {m : ℕ} (x : Fin m → E) (η : ℝ) (u : Fin m → ℝ) (y : E) :
    netApprox x η u y = (∑ k, tentWeight η (x k) y * u k) / tentSum x η y := by
  simp [netApprox, tentPart, Finset.sum_div, div_mul_eq_mul_div]

/-- **The interpolation is continuous on a set the net covers.**  The numerator and the
denominator are continuous, and the denominator does not vanish there. -/
theorem continuousOn_netApprox {m : ℕ} {x : Fin m → E} {η : ℝ} (u : Fin m → ℝ) {K : Set E}
    (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η) : ContinuousOn (netApprox x η u) K := by
  have hw : ∀ k : Fin m, Continuous fun y : E => tentWeight η (x k) y := by
    intro k
    unfold tentWeight
    fun_prop
  have hnum : Continuous fun y : E => ∑ k, tentWeight η (x k) y * u k :=
    continuous_finsetSum _ fun k _ => (hw k).mul continuous_const
  have hden : Continuous fun y : E => tentSum x η y := by
    unfold tentSum
    exact continuous_finsetSum _ fun k _ => hw k
  have hfun : netApprox x η u
      = fun z : E => (∑ k, tentWeight η (x k) z * u k) / tentSum x η z := by
    funext z
    exact netApprox_eq_div x η u z
  intro y hy
  have hpos : 0 < tentSum x η y := tentSum_pos (hnet y hy)
  refine ContinuousAt.continuousWithinAt ?_
  rw [hfun]
  exact hnum.continuousAt.div hden.continuousAt (ne_of_gt hpos)

end LatticeProb

end
