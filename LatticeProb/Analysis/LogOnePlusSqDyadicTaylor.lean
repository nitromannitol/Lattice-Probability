import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic Taylor expansion of `log(1 + y²)` along a function of finite variation

Deterministic ingredients of the classical argument showing that a continuous process of finite variation with
centred increments vanishes (Revuz–Yor (1999), Chapter IV, Proposition 1.2; Fukushima–Oshima–Takeda (2011), proof of
Theorem 5.1.4): one expands `φ(N_T)`, `φ(y) = log(1 + y²)`, along the dyadic partitions `k T / 2ⁿ` of `[0, T]` and
shows that the sum of second-order remainders tends to `0`.

* `logOnePlusSq`, `logOnePlusSqDeriv`: `φ` and `φ'`; `φ ≥ 0`, `φ y = 0 → y = 0`, `|φ'| ≤ 1`, `φ' 0 = 0`, `φ'` is
  `2`-Lipschitz, and the second-order Taylor bound `|φ b - φ a - φ' a (b - a)| ≤ 2 |b - a| min(|b - a|, 1)`
  (`abs_logOnePlusSq_sub_sub_le`);
* `eventually_forall_abs_dyadic_increment_lt`: along the dyadic partitions of `[0, T]` the increments of a function
  continuous on `[0, T]` are eventually uniformly small;
* `dyadicTaylorRemainder`: the sum of the second-order remainders; `logOnePlusSq_eq_sum_add_dyadicTaylorRemainder` is
  the telescoped expansion for `N 0 = 0`, and `tendsto_dyadicTaylorRemainder` shows that the remainders tend to `0`
  when `N = α - β` with `α, β` continuous and nondecreasing on `[0, T]`.
-/

open Set Filter Topology

namespace LatticeProb

/-- The function `φ(y) = log(1 + y²)` of the Taylor argument. -/
noncomputable def logOnePlusSq (y : ℝ) : ℝ := Real.log (1 + y ^ 2)

/-- The derivative `φ'(y) = 2y / (1 + y²)` of `logOnePlusSq`. -/
noncomputable def logOnePlusSqDeriv (y : ℝ) : ℝ := 2 * y / (1 + y ^ 2)

theorem hasDerivAt_logOnePlusSq (y : ℝ) : HasDerivAt logOnePlusSq (logOnePlusSqDeriv y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add 1
  exact h1.log (by positivity)

theorem logOnePlusSq_zero : logOnePlusSq 0 = 0 := by simp [logOnePlusSq]

theorem logOnePlusSqDeriv_zero : logOnePlusSqDeriv 0 = 0 := by simp [logOnePlusSqDeriv]

theorem logOnePlusSq_nonneg (y : ℝ) : 0 ≤ logOnePlusSq y :=
  Real.log_nonneg (by nlinarith [sq_nonneg y])

theorem eq_zero_of_logOnePlusSq_eq_zero {y : ℝ} (h : logOnePlusSq y = 0) : y = 0 := by
  by_contra hy
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have : 0 < logOnePlusSq y := Real.log_pos (by linarith)
  linarith

theorem abs_logOnePlusSqDeriv_le_one (y : ℝ) : |logOnePlusSqDeriv y| ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rw [logOnePlusSqDeriv, abs_div, abs_of_pos hpos, div_le_one₀ hpos]
  exact abs_le.2 ⟨by nlinarith [sq_nonneg (y + 1)], by nlinarith [sq_nonneg (y - 1)]⟩

/-- The derivative `φ'` is `2`-Lipschitz. -/
theorem abs_logOnePlusSqDeriv_sub_le (u a : ℝ) :
    |logOnePlusSqDeriv u - logOnePlusSqDeriv a| ≤ 2 * |u - a| := by
  have hu : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have ha : (0 : ℝ) < 1 + a ^ 2 := by positivity
  have key : logOnePlusSqDeriv u - logOnePlusSqDeriv a =
      2 * (u - a) * (1 - u * a) / ((1 + u ^ 2) * (1 + a ^ 2)) := by
    rw [logOnePlusSqDeriv, logOnePlusSqDeriv, div_sub_div _ _ hu.ne' ha.ne']
    ring
  have hb : |1 - u * a| ≤ (1 + u ^ 2) * (1 + a ^ 2) :=
    abs_le.2 ⟨by nlinarith [sq_nonneg (u - a), sq_nonneg u, sq_nonneg a, sq_nonneg (u * a)],
      by nlinarith [sq_nonneg (u + a), sq_nonneg u, sq_nonneg a, sq_nonneg (u * a)]⟩
  rw [key, abs_div, abs_of_pos (mul_pos hu ha), div_le_iff₀ (mul_pos hu ha), abs_mul, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- The second-order Taylor bound for `φ(y) = log(1 + y²)`:
`|φ b - φ a - φ' a (b - a)| ≤ 2 |b - a| min(|b - a|, 1)`. -/
theorem abs_logOnePlusSq_sub_sub_le (a b : ℝ) :
    |logOnePlusSq b - logOnePlusSq a - logOnePlusSqDeriv a * (b - a)| ≤ 2 * |b - a| * min |b - a| 1 := by
  set g : ℝ → ℝ := fun u => logOnePlusSq u - logOnePlusSq a - logOnePlusSqDeriv a * (u - a) with hg
  have hgd : ∀ u, HasDerivAt g (logOnePlusSqDeriv u - logOnePlusSqDeriv a) u := by
    intro u
    exact (((hasDerivAt_logOnePlusSq u).sub_const (logOnePlusSq a)).sub
      (((hasDerivAt_id' u).sub_const a).const_mul (logOnePlusSqDeriv a))).congr_deriv (by ring)
  have hga : g a = 0 := by simp [hg]
  have h1 : |g b| ≤ 2 * |b - a| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (s := univ) (x := a) (y := b)
      (C := 2) (fun u _ => (hgd u).hasDerivWithinAt) (fun u _ => ?_) convex_univ (mem_univ _) (mem_univ _)
    · simpa [hga, Real.norm_eq_abs] using this
    · rw [Real.norm_eq_abs]
      have h1 := abs_le.1 (abs_logOnePlusSqDeriv_le_one u)
      have h2 := abs_le.1 (abs_logOnePlusSqDeriv_le_one a)
      exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have h2 : |g b| ≤ 2 * |b - a| * |b - a| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (s := uIcc a b) (x := a) (y := b)
      (C := 2 * |b - a|) (fun u _ => (hgd u).hasDerivWithinAt) (fun u hu => ?_) (convex_uIcc a b)
      left_mem_uIcc right_mem_uIcc
    · simpa [hga, Real.norm_eq_abs] using this
    · rw [Real.norm_eq_abs]
      exact (abs_logOnePlusSqDeriv_sub_le u a).trans
        (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hu) (by norm_num))
  rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
  exact le_min h2 h1

/-- Along the dyadic partitions `k T / 2ⁿ` of `[0, T]`, the increments of a function continuous on `[0, T]` are
eventually uniformly smaller than any `ε > 0`. -/
theorem eventually_forall_abs_dyadic_increment_lt {F : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hF : ContinuousOn F (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k < 2 ^ n,
      |F (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - F ((k : ℝ) * T / 2 ^ n)| < ε := by
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hF) ε hε
  have hlim : Tendsto (fun n : ℕ => T * (1 / 2 : ℝ) ^ n) atTop (𝓝 (T * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul T
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn k hk
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.succ_le_of_lt hk
  have hk0 : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk.le
  have hmem1 : ((k + 1 : ℕ) : ℝ) * T / 2 ^ n ∈ Icc 0 T :=
    ⟨by positivity, by rw [div_le_iff₀ h2]; nlinarith⟩
  have hmem0 : (k : ℝ) * T / 2 ^ n ∈ Icc 0 T :=
    ⟨by positivity, by rw [div_le_iff₀ h2]; nlinarith⟩
  have hdiff : ((k + 1 : ℕ) : ℝ) * T / 2 ^ n - (k : ℝ) * T / 2 ^ n = T * (1 / 2 : ℝ) ^ n := by
    rw [one_div_pow]
    push_cast
    field_simp
    ring
  have := hFδ _ hmem1 _ hmem0 (by rwa [Real.dist_eq, hdiff, abs_of_nonneg (by positivity)])
  rwa [Real.dist_eq] at this

/-! ### The dyadic Taylor expansion of `φ ∘ N` -/

theorem dyadic_mem_Icc {T : ℝ} (hT : 0 ≤ T) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    (k : ℝ) * T / 2 ^ n ∈ Icc 0 T := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk' : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
  exact ⟨by positivity, by rw [div_le_iff₀ h2]; nlinarith⟩

theorem dyadic_le_succ {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) :
    (k : ℝ) * T / 2 ^ n ≤ ((k + 1 : ℕ) : ℝ) * T / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
  rw [div_le_iff₀ h2, div_mul_cancel₀ _ h2.ne']
  exact mul_le_mul_of_nonneg_right hk hT

theorem dyadic_top (T : ℝ) (n : ℕ) : ((2 ^ n : ℕ) : ℝ) * T / 2 ^ n = T := by
  push_cast
  exact mul_div_cancel_left₀ T (by positivity)

/-- The sum of the second-order Taylor remainders of `φ = logOnePlusSq` along the dyadic partition
`k T / 2ⁿ`, `k < 2ⁿ`, of `[0, T]`, for a function `N`. -/
noncomputable def dyadicTaylorRemainder (N : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n),
    (logOnePlusSq (N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n)) - logOnePlusSq (N ((k : ℝ) * T / 2 ^ n)) -
      logOnePlusSqDeriv (N ((k : ℝ) * T / 2 ^ n)) *
        (N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)))

/-- The dyadic Taylor expansion `φ(N_T) = Σ_k φ'(N_{t_k}) (N_{t_{k+1}} - N_{t_k}) + Σ_k R_k` for `N_0 = 0`. -/
theorem logOnePlusSq_eq_sum_add_dyadicTaylorRemainder {N : ℝ → ℝ} (h0 : N 0 = 0) (T : ℝ) (n : ℕ) :
    logOnePlusSq (N T) = ∑ k ∈ Finset.range (2 ^ n), logOnePlusSqDeriv (N ((k : ℝ) * T / 2 ^ n)) *
        (N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)) + dyadicTaylorRemainder N T n := by
  have key := Finset.sum_range_sub (fun k : ℕ => logOnePlusSq (N ((k : ℝ) * T / 2 ^ n))) (2 ^ n)
  rw [dyadic_top, Nat.cast_zero, zero_mul, zero_div, h0, logOnePlusSq_zero, sub_zero] at key
  rw [dyadicTaylorRemainder, ← Finset.sum_add_distrib, ← key]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem abs_dyadicTaylorRemainder_le (N : ℝ → ℝ) (T : ℝ) (n : ℕ) :
    |dyadicTaylorRemainder N T n| ≤ ∑ k ∈ Finset.range (2 ^ n),
      2 * |N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)| *
        min |N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)| 1 :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun _ _ => abs_logOnePlusSq_sub_sub_le _ _)

/-- For a difference `N = α - β` of functions nondecreasing on `[0, T]`, the total variation of `N` along a dyadic
partition is at most `(α T - α 0) + (β T - β 0)`. -/
theorem sum_abs_dyadic_increment_le {N α β : ℝ → ℝ} (hN : ∀ r, N r = α r - β r) {T : ℝ} (hT : 0 ≤ T)
    (hα : MonotoneOn α (Icc 0 T)) (hβ : MonotoneOn β (Icc 0 T)) (n : ℕ) :
    ∑ k ∈ Finset.range (2 ^ n), |N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)| ≤
      (α T - α 0) + (β T - β 0) := by
  have tele : ∀ γ : ℝ → ℝ, ∑ k ∈ Finset.range (2 ^ n),
      (γ (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - γ ((k : ℝ) * T / 2 ^ n)) = γ T - γ 0 := by
    intro γ
    have key := Finset.sum_range_sub (fun k : ℕ => γ ((k : ℝ) * T / 2 ^ n)) (2 ^ n)
    rwa [dyadic_top, Nat.cast_zero, zero_mul, zero_div] at key
  have hinc : ∀ γ : ℝ → ℝ, MonotoneOn γ (Icc 0 T) → ∀ k ∈ Finset.range (2 ^ n),
      0 ≤ γ (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - γ ((k : ℝ) * T / 2 ^ n) := by
    intro γ hγ k hk
    have hk' := Finset.mem_range.1 hk
    exact sub_nonneg.2 (hγ (dyadic_mem_Icc hT hk'.le) (dyadic_mem_Icc (k := k + 1) hT hk')
      (dyadic_le_succ hT n k))
  rw [← tele α, ← tele β, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have h1 := hinc α hα k hk
  have h2 := hinc β hβ k hk
  rw [hN, hN, abs_le]
  constructor <;> linarith

theorem abs_dyadicTaylorRemainder_le_of_forall {N α β : ℝ → ℝ} (hN : ∀ r, N r = α r - β r) {T : ℝ}
    (hT : 0 ≤ T) (hα : MonotoneOn α (Icc 0 T)) (hβ : MonotoneOn β (Icc 0 T)) {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k < 2 ^ n, min |N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)| 1 ≤ c) :
    |dyadicTaylorRemainder N T n| ≤ 2 * c * ((α T - α 0) + (β T - β 0)) := by
  refine (abs_dyadicTaylorRemainder_le N T n).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range (2 ^ n),
        2 * c * |N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)| := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hm := h k (Finset.mem_range.1 hk)
        have h0 := abs_nonneg (N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n))
        nlinarith [mul_le_mul_of_nonneg_left hm h0]
    _ = 2 * c * ∑ k ∈ Finset.range (2 ^ n),
        |N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)| := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * c * ((α T - α 0) + (β T - β 0)) :=
        mul_le_mul_of_nonneg_left (sum_abs_dyadic_increment_le hN hT hα hβ n) (by positivity)

/-- For a difference `N = α - β` of functions continuous and nondecreasing on `[0, T]`, the dyadic Taylor
remainders of `φ ∘ N` tend to `0`. -/
theorem tendsto_dyadicTaylorRemainder {N α β : ℝ → ℝ} (hN : ∀ r, N r = α r - β r) {T : ℝ} (hT : 0 ≤ T)
    (hα : MonotoneOn α (Icc 0 T)) (hβ : MonotoneOn β (Icc 0 T)) (hαc : ContinuousOn α (Icc 0 T))
    (hβc : ContinuousOn β (Icc 0 T)) :
    Tendsto (dyadicTaylorRemainder N T) atTop (𝓝 0) := by
  set V := (α T - α 0) + (β T - β 0) with hV
  have hV0 : 0 ≤ V := by
    have h1 := hα (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
    have h2 := hβ (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
    linarith
  have hNc : ContinuousOn N (Icc 0 T) := by
    have : N = fun r => α r - β r := funext hN
    rw [this]
    exact hαc.sub hβc
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set η := min (ε / (4 * (V + 1))) 1 with hηdef
  have hη : 0 < η := lt_min (by positivity) one_pos
  have hη' : η * (4 * (V + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_left _ _)
  filter_upwards [eventually_forall_abs_dyadic_increment_lt hT hNc hη] with n hn
  rw [Real.dist_eq, sub_zero]
  have hb := abs_dyadicTaylorRemainder_le_of_forall hN hT hα hβ hη.le
    (fun k hk => (min_le_left _ _).trans (hn k hk).le)
  have e1 : η * (4 * (V + 1)) = 4 * (η * V) + 4 * η := by ring
  have e2 : 2 * η * V = 2 * (η * V) := by ring
  linarith [mul_nonneg hη.le hV0]

end LatticeProb
