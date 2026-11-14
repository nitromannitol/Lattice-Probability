import LatticeProb.Analysis.ConvexSubgradient

/-!
# A second-order Taylor expansion of a convex function from an expansion of its subgradients

Let `f` be a convex function on a finite-dimensional real inner product space `E`, `x₀ ∈ E`,
`p ∈ E` and `B : E →L[ℝ] E`. Suppose that every subgradient `g` of `f` at a point `x₀ + h` near `x₀`
satisfies `g = p + B h + o(‖h‖)`. Then `f` has the second-order expansion
`f y = f x₀ + ⟪p, y - x₀⟫ + 1/2 ⟪B (y - x₀), y - x₀⟫ + o(‖y - x₀‖ ^ 2)` at `x₀`.

The proof compares `f (x₀ + v) - f x₀` with Riemann sums of the subgradients along the segment from
`x₀` to `x₀ + v`: for any subgradients `g_k` at the points `x₀ + (k / N) • v`, convexity gives
`⟪g_k, v⟫ / N ≤ f (x₀ + ((k + 1) / N) • v) - f (x₀ + (k / N) • v) ≤ ⟪g_{k+1}, v⟫ / N`.
Summing over `k < N` and letting `N → ∞` gives the expansion. Only these two inequalities are used.

## Main results

* `LatticeProb.ConvexAnalysis.hasSecondOrderTaylor_of_subgradient_expansion`: the expansion.
* `LatticeProb.ConvexAnalysis.abs_taylor_le`: the quantitative form along a segment.
-/

open Set Filter Topology Asymptotics
open scoped InnerProductSpace

namespace LatticeProb.ConvexAnalysis

section Steps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ}

/-- A subgradient at `x` bounds the increment of `f` from below. -/
theorem IsSubgradientAt.inner_le_sub {x g : E} (hg : IsSubgradientAt f x g) (d : E) :
    ⟪g, d⟫_ℝ ≤ f (x + d) - f x := by
  have h := hg (x + d)
  rw [add_sub_cancel_left] at h
  linarith

/-- A subgradient at the end point `x + d` bounds the increment of `f` over `[x, x + d]` from above. -/
theorem IsSubgradientAt.sub_le_inner {x d g : E} (hg : IsSubgradientAt f (x + d) g) :
    f (x + d) - f x ≤ ⟪g, d⟫_ℝ := by
  have h := hg x
  have e : x - (x + d) = -d := by abel
  rw [e, inner_neg_right] at h
  linarith

/-- Pairing the expansion `‖g - p - B (t • v)‖ ≤ e * ‖t • v‖` with `v`. -/
theorem abs_inner_sub_le_of_expansion {B : E →L[ℝ] E} {p g v : E} {e t : ℝ} (ht : 0 ≤ t)
    (h : ‖g - p - B (t • v)‖ ≤ e * ‖t • v‖) :
    |⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ| ≤ e * t * ‖v‖ ^ 2 := by
  have h1 : ⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ = ⟪g - p - B (t • v), v⟫_ℝ := by
    rw [inner_sub_left, inner_sub_left, map_smul, real_inner_smul_left]
  rw [h1]
  calc |⟪g - p - B (t • v), v⟫_ℝ| ≤ ‖g - p - B (t • v)‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ e * ‖t • v‖ * ‖v‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = e * t * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      ring

end Steps

section Chain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ}

/-- Lower Riemann sum: the increments of `f` along `x₀ + (k * s) • v`, `k ≤ N`, are bounded below. -/
theorem lower_chain (hf : ConvexOn ℝ Set.univ f) {B : E →L[ℝ] E} {p x₀ v : E} {e s : ℝ}
    (hs : 0 < s) {N : ℕ} (hNs : (N : ℝ) * s = 1)
    (hsub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ g, IsSubgradientAt f (x₀ + t • v) g →
      |⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ| ≤ e * t * ‖v‖ ^ 2) :
    ∀ k : ℕ, k ≤ N →
      (k : ℝ) * s * ⟪p, v⟫_ℝ + k * (k - 1) / 2 * s ^ 2 * (⟪B v, v⟫_ℝ - e * ‖v‖ ^ 2) ≤
        f (x₀ + ((k : ℝ) * s) • v) - f x₀ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    have hk1 : (k : ℝ) * s ≤ 1 := by
      rw [← hNs]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) hs.le
    obtain ⟨g, hg⟩ := exists_isSubgradientAt hf (x₀ + ((k : ℝ) * s) • v)
    have hb := (abs_le.mp (hsub ((k : ℝ) * s) (by positivity) hk1 g hg)).1
    have hb' := mul_le_mul_of_nonneg_left hb hs.le
    have hstep := hg.inner_le_sub (s • v)
    have hx : x₀ + ((k : ℝ) * s) • v + s • v = x₀ + (((k : ℝ) + 1) * s) • v := by module
    rw [hx, real_inner_smul_right] at hstep
    have ih' := ih hkN
    push_cast
    nlinarith [hstep, hb', ih']

/-- Upper Riemann sum: the increments of `f` along `x₀ + (k * s) • v`, `k ≤ N`, are bounded above. -/
theorem upper_chain (hf : ConvexOn ℝ Set.univ f) {B : E →L[ℝ] E} {p x₀ v : E} {e s : ℝ}
    (hs : 0 < s) {N : ℕ} (hNs : (N : ℝ) * s = 1)
    (hsub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ g, IsSubgradientAt f (x₀ + t • v) g →
      |⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ| ≤ e * t * ‖v‖ ^ 2) :
    ∀ k : ℕ, k ≤ N →
      f (x₀ + ((k : ℝ) * s) • v) - f x₀ ≤
        (k : ℝ) * s * ⟪p, v⟫_ℝ + k * (k + 1) / 2 * s ^ 2 * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    have hk1 : ((k : ℝ) + 1) * s ≤ 1 :=
      calc ((k : ℝ) + 1) * s ≤ N * s :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hs.le
        _ = 1 := hNs
    obtain ⟨g, hg⟩ := exists_isSubgradientAt hf (x₀ + (((k : ℝ) + 1) * s) • v)
    have hb := (abs_le.mp (hsub (((k : ℝ) + 1) * s) (by positivity) hk1 g hg)).2
    have hb' := mul_le_mul_of_nonneg_left hb hs.le
    have hx : x₀ + (((k : ℝ) + 1) * s) • v = x₀ + ((k : ℝ) * s) • v + s • v := by module
    rw [hx] at hg
    have hstep := hg.sub_le_inner
    rw [real_inner_smul_right] at hstep
    have ih' := ih hkN
    rw [← hx] at hstep
    push_cast
    nlinarith [hstep, hb', ih']

/-- Lower bound at the end of the chain: `f (x₀ + v) - f x₀ ≥ ⟪p, v⟫ + (1 - s) / 2 * (Q - e ‖v‖²)`. -/
theorem lower_bound_of_chain (hf : ConvexOn ℝ Set.univ f) {B : E →L[ℝ] E} {p x₀ v : E} {e s : ℝ}
    (hs : 0 < s) {N : ℕ} (hNs : (N : ℝ) * s = 1)
    (hsub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ g, IsSubgradientAt f (x₀ + t • v) g →
      |⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ| ≤ e * t * ‖v‖ ^ 2) :
    ⟪p, v⟫_ℝ + (1 - s) / 2 * (⟪B v, v⟫_ℝ - e * ‖v‖ ^ 2) ≤ f (x₀ + v) - f x₀ := by
  have h := lower_chain hf hs hNs hsub N le_rfl
  have e2 : (N : ℝ) * ((N : ℝ) - 1) / 2 * s ^ 2 = (1 - s) / 2 := by
    calc (N : ℝ) * ((N : ℝ) - 1) / 2 * s ^ 2 = (((N : ℝ) * s) ^ 2 - ((N : ℝ) * s) * s) / 2 := by ring
      _ = (1 - s) / 2 := by rw [hNs]; ring
  rw [hNs, one_smul] at h
  have e3 : (N : ℝ) * ((N : ℝ) - 1) / 2 * s ^ 2 * (⟪B v, v⟫_ℝ - e * ‖v‖ ^ 2) =
      (1 - s) / 2 * (⟪B v, v⟫_ℝ - e * ‖v‖ ^ 2) := by rw [e2]
  rw [e3, one_mul] at h
  exact h

/-- Upper bound at the end of the chain: `f (x₀ + v) - f x₀ ≤ ⟪p, v⟫ + (1 + s) / 2 * (Q + e ‖v‖²)`. -/
theorem upper_bound_of_chain (hf : ConvexOn ℝ Set.univ f) {B : E →L[ℝ] E} {p x₀ v : E} {e s : ℝ}
    (hs : 0 < s) {N : ℕ} (hNs : (N : ℝ) * s = 1)
    (hsub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ g, IsSubgradientAt f (x₀ + t • v) g →
      |⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ| ≤ e * t * ‖v‖ ^ 2) :
    f (x₀ + v) - f x₀ ≤ ⟪p, v⟫_ℝ + (1 + s) / 2 * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) := by
  have h := upper_chain hf hs hNs hsub N le_rfl
  have e2 : (N : ℝ) * ((N : ℝ) + 1) / 2 * s ^ 2 = (1 + s) / 2 := by
    calc (N : ℝ) * ((N : ℝ) + 1) / 2 * s ^ 2 = (((N : ℝ) * s) ^ 2 + ((N : ℝ) * s) * s) / 2 := by ring
      _ = (1 + s) / 2 := by rw [hNs]; ring
  rw [hNs, one_smul] at h
  have e3 : (N : ℝ) * ((N : ℝ) + 1) / 2 * s ^ 2 * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) =
      (1 + s) / 2 * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) := by rw [e2]
  rw [e3, one_mul] at h
  exact h

/-- Along a segment: if the subgradients at `x₀ + t • v`, `0 ≤ t ≤ 1`, satisfy the expansion with
constant `e`, then `f (x₀ + v)` differs from its second-order Taylor polynomial by at most
`e / 2 * ‖v‖ ^ 2`. -/
theorem abs_taylor_le (hf : ConvexOn ℝ Set.univ f) {B : E →L[ℝ] E} {p x₀ v : E} {e : ℝ} (he : 0 ≤ e)
    (hsub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ g, IsSubgradientAt f (x₀ + t • v) g →
      |⟪g, v⟫_ℝ - ⟪p, v⟫_ℝ - t * ⟪B v, v⟫_ℝ| ≤ e * t * ‖v‖ ^ 2) :
    |f (x₀ + v) - f x₀ - ⟪p, v⟫_ℝ - 1 / 2 * ⟪B v, v⟫_ℝ| ≤ e * ‖v‖ ^ 2 / 2 := by
  have hP0 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hN : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * (1 / ((n : ℝ) + 1)) = 1 := by
    intro n
    push_cast
    field_simp
  have hlow : ∀ n : ℕ, -(e * ‖v‖ ^ 2 / 2) - 1 / ((n : ℝ) + 1) * ⟪B v, v⟫_ℝ / 2 ≤
      f (x₀ + v) - f x₀ - ⟪p, v⟫_ℝ - 1 / 2 * ⟪B v, v⟫_ℝ := by
    intro n
    have hs : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h := lower_bound_of_chain hf hs (hN n) hsub
    nlinarith [mul_nonneg hs.le (mul_nonneg he hP0)]
  have hupp : ∀ n : ℕ, f (x₀ + v) - f x₀ - ⟪p, v⟫_ℝ - 1 / 2 * ⟪B v, v⟫_ℝ ≤
      e * ‖v‖ ^ 2 / 2 + 1 / ((n : ℝ) + 1) * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) / 2 := by
    intro n
    have hs : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h := upper_bound_of_chain hf hs (hN n) hsub
    nlinarith
  have hL : -(e * ‖v‖ ^ 2 / 2) ≤ f (x₀ + v) - f x₀ - ⟪p, v⟫_ℝ - 1 / 2 * ⟪B v, v⟫_ℝ := by
    have ht : Tendsto (fun n : ℕ => -(e * ‖v‖ ^ 2 / 2) - 1 / ((n : ℝ) + 1) * ⟪B v, v⟫_ℝ / 2) atTop
        (𝓝 (-(e * ‖v‖ ^ 2 / 2) - 0 * ⟪B v, v⟫_ℝ / 2)) :=
      tendsto_const_nhds.sub ((hlim.mul_const _).div_const 2)
    simpa using le_of_tendsto' ht hlow
  have hU : f (x₀ + v) - f x₀ - ⟪p, v⟫_ℝ - 1 / 2 * ⟪B v, v⟫_ℝ ≤ e * ‖v‖ ^ 2 / 2 := by
    have ht : Tendsto
        (fun n : ℕ => e * ‖v‖ ^ 2 / 2 + 1 / ((n : ℝ) + 1) * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) / 2) atTop
        (𝓝 (e * ‖v‖ ^ 2 / 2 + 0 * (⟪B v, v⟫_ℝ + e * ‖v‖ ^ 2) / 2)) :=
      tendsto_const_nhds.add ((hlim.mul_const _).div_const 2)
    simpa using ge_of_tendsto' ht hupp
  exact abs_le.mpr ⟨hL, hU⟩

end Chain

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ}

/-- If the subgradients of a convex function `f` at `x₀ + h` are `p + B h + o(‖h‖)`, then `f` has the
second-order expansion `f y = f x₀ + ⟪p, y - x₀⟫ + 1/2 ⟪B (y - x₀), y - x₀⟫ + o(‖y - x₀‖ ^ 2)`. -/
theorem hasSecondOrderTaylor_of_subgradient_expansion (hf : ConvexOn ℝ Set.univ f) (B : E →L[ℝ] E)
    (p x₀ : E)
    (h : ∀ e > 0, ∃ r > 0, ∀ v : E, ‖v‖ < r → ∀ g, IsSubgradientAt f (x₀ + v) g →
      ‖g - p - B v‖ ≤ e * ‖v‖) :
    (fun y => f y - f x₀ - ⟪p, y - x₀⟫_ℝ - 1 / 2 * ⟪B (y - x₀), y - x₀⟫_ℝ) =o[𝓝 x₀]
      fun y => ‖y - x₀‖ ^ 2 := by
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨r, hr, hrh⟩ := h c hc
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with y hy
  have hv : ‖y - x₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hsub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ g, IsSubgradientAt f (x₀ + t • (y - x₀)) g →
      |⟪g, y - x₀⟫_ℝ - ⟪p, y - x₀⟫_ℝ - t * ⟪B (y - x₀), y - x₀⟫_ℝ| ≤ c * t * ‖y - x₀‖ ^ 2 := by
    intro t ht0 ht1 g hg
    refine abs_inner_sub_le_of_expansion ht0 (hrh (t • (y - x₀)) ?_ g hg)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖y - x₀‖ ≤ 1 * ‖y - x₀‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      _ < r := by rwa [one_mul]
  have key := abs_taylor_le hf hc.le hsub
  rw [add_sub_cancel] at key
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  calc _ ≤ c * ‖y - x₀‖ ^ 2 / 2 := key
    _ ≤ c * ‖y - x₀‖ ^ 2 := by
      have : 0 ≤ c * ‖y - x₀‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
      linarith

end Main

end LatticeProb.ConvexAnalysis
