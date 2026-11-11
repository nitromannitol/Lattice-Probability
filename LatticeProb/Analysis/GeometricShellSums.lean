import Mathlib

/-!
# Geometric shell sums

Elementary estimates for a nonnegative sequence `O` that contracts by a fixed factor `q < 1`
whenever it exceeds a positive threshold, and for radii `r k` dominated by such a sequence.
The indices `k` are called shells.

* Geometric decay of the sequence and of the partial sums of radii:
  `shell_maximum_le_geometric`, `shell_radii_sum_le`, `shell_radii_max_sum_le`,
  `shell_radius_le_geometric_above_floor`, `shell_radius_tail_sum_le`,
  `shell_radius_from_odometer_contraction`, `shell_radii_sum_from_odometer_contraction`.
* First crossing of a threshold, with a logarithmic bound on the crossing time:
  `exists_shell_maximum_le_threshold`, `shell_steps_lt_log_ratio`,
  `exists_first_shell_threshold_with_log_bound`, `log_initial_to_threshold`,
  `exists_first_shell_threshold_log_scale`.
* Budget estimates for the sum of radii plus a diameter error term:
  `shell_iteration_budget_le`, `exists_shell_threshold_with_iteration_budget`,
  `exists_shell_threshold_with_shifted_radius_budget`.
* Vanishing, as `ε → 0⁺`, of the logarithmic and power-law error terms:
  `tendsto_shell_floor_log_bound`, `tendsto_shell_iteration_budget`,
  `eventually_shell_iteration_budget_lt`, `eventually_first_crossing_budget_lt`,
  `eventually_exists_shell_threshold_with_budget`.
-/

namespace LatticeProb.GeometricShellSums

open Filter Topology

/-- A nonnegative sequence contracting by a fixed factor has geometric decay. -/
theorem shell_maximum_le_geometric (O : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ k, O (k + 1) ≤ q * O k) (n : ℕ) :
    O n ≤ O 0 * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      O (n + 1) ≤ q * O n := hstep n
      _ ≤ q * (O 0 * q ^ n) := mul_le_mul_of_nonneg_left ih hq
      _ = O 0 * q ^ (n + 1) := by rw [pow_succ]; ring

/-- The total radius is bounded when each shell has a geometric majorant. -/
theorem shell_radii_sum_le (r : ℕ → ℝ) (A q : ℝ) (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ)
    (hr : ∀ k < n, r k ≤ A * q ^ k) :
    ∑ k ∈ Finset.range n, r k ≤ A / (1 - q) := by
  calc
    ∑ k ∈ Finset.range n, r k ≤ ∑ k ∈ Finset.range n, A * q ^ k := by
      exact Finset.sum_le_sum fun k hk => hr k (Finset.mem_range.mp hk)
    _ = A * ∑ k ∈ Finset.range n, q ^ k := by rw [Finset.mul_sum]
    _ ≤ A * (1 - q)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact (summable_geometric_of_lt_one hq hq1).sum_le_tsum (Finset.range n)
        (fun k _ => pow_nonneg hq k) |>.trans_eq (tsum_geometric_of_lt_one hq hq1)
    _ = A / (1 - q) := by rw [div_eq_mul_inv]

/-- A maximum which contracts whenever it exceeds a positive threshold reaches
that threshold in finitely many steps. -/
theorem exists_shell_maximum_le_threshold (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hB : 0 < B)
    (hstep : ∀ k, B < O k → O (k + 1) ≤ q * O k) :
    ∃ n, O n ≤ B := by
  by_contra h
  have hall : ∀ n, B < O n := by simpa only [not_exists, not_le] using h
  have hgeom : ∀ n, O n ≤ O 0 * q ^ n :=
    shell_maximum_le_geometric O q hq (fun k => hstep k (hall k))
  have hlim : Tendsto (fun n : ℕ => O 0 * q ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 B hB)
  exact (not_lt_of_ge (hgeom N)) ((hN N le_rfl).trans (hall N))

/-- Before the first threshold crossing, the number of shell steps is bounded
by the logarithm of the initial-to-threshold odometer ratio. -/
theorem shell_steps_lt_log_ratio (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B) (n : ℕ)
    (hbefore : B < O n)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k) :
    (n : ℝ) < Real.log (O 0 / B) / (-Real.log q) := by
  have hgeom : ∀ k ≤ n, O k ≤ O 0 * q ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        O (k + 1) ≤ q * O k := hstep k (by omega)
        _ ≤ q * (O 0 * q ^ k) := mul_le_mul_of_nonneg_left (ih (by omega)) hq.le
        _ = O 0 * q ^ (k + 1) := by rw [pow_succ]; ring
  have hprod : B < O 0 * q ^ n := lt_of_lt_of_le hbefore (hgeom n le_rfl)
  have hO : 0 < O 0 := by
    have : 0 < O 0 * q ^ n := lt_trans hB hprod
    exact pos_of_mul_pos_left this (pow_nonneg hq.le n)
  have hlog := Real.log_lt_log hB hprod
  rw [Real.log_mul hO.ne' (pow_ne_zero _ hq.ne'), Real.log_pow] at hlog
  have hqlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  rw [lt_div_iff₀ hqlog, Real.log_div hO.ne' hB.ne']
  nlinarith

/-- The first crossing exists and is at most one more than the logarithmic bound
for the previous shell. The contraction is only required before crossing. -/
theorem exists_first_shell_threshold_with_log_bound (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B) (hinitial : B < O 0)
    (hstep : ∀ k, B < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (τ : ℝ) < Real.log (O 0 / B) / (-Real.log q) + 1 := by
  have hex := exists_shell_maximum_le_threshold O q B hq.le hq1 hB hstep
  let τ := Nat.find hex
  have hτ : O τ ≤ B := Nat.find_spec hex
  have hprev : ∀ k < τ, B < O k := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  have hτpos : 0 < τ := by
    by_contra hn
    have hτ0 : τ = 0 := Nat.eq_zero_of_not_pos hn
    rw [hτ0] at hτ
    exact (not_le_of_gt hinitial) hτ
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hτpos)
  have hbound := shell_steps_lt_log_ratio O q B hq hq1 hB n
    (hprev n (by omega)) (fun k hk => hstep k (hprev k (by omega)))
  refine ⟨τ, hτ, hprev, ?_⟩
  rw [hn, Nat.cast_succ]
  linarith

/-- The logarithm of the ratio `(C / ε) / ε ^ (-ω)`, expanded as
`log C + (1 - ω) * log ε⁻¹`. -/
theorem log_initial_to_threshold (C ε ω : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    Real.log ((C / ε) / ε ^ (-ω)) =
      Real.log C + (1 - ω) * Real.log ε⁻¹ := by
  rw [Real.log_div (div_ne_zero hC.ne' hε.ne') (Real.rpow_pos_of_pos hε _).ne',
    Real.log_div hC.ne' hε.ne', Real.log_rpow hε, Real.log_inv]
  ring

/-- For an initial maximum at most `C / ε` and threshold `ε ^ (-ω)`, the first
threshold crossing occurs at a time bounded by
`(log C + (1 - ω) * log ε⁻¹) / (-log q) + 1`. -/
theorem exists_first_shell_threshold_log_scale (O : ℕ → ℝ) (q C ε ω : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 < C) (hε : 0 < ε)
    (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, O τ ≤ ε ^ (-ω) ∧ (∀ k < τ, ε ^ (-ω) < O k) ∧
      (τ : ℝ) < (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1 := by
  have hB : 0 < ε ^ (-ω) := Real.rpow_pos_of_pos hε _
  obtain ⟨τ, hτ, hbefore, hbound⟩ :=
    exists_first_shell_threshold_with_log_bound O q (ε ^ (-ω)) hq hq1 hB hinitial hstep
  refine ⟨τ, hτ, hbefore, ?_⟩
  have hlog : Real.log (O 0 / ε ^ (-ω)) ≤ Real.log ((C / ε) / ε ^ (-ω)) :=
    Real.log_le_log (div_pos (lt_trans hB hinitial) hB) (div_le_div_of_nonneg_right hupper hB.le)
  rw [log_initial_to_threshold C ε ω hC hε] at hlog
  have hden : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hdiv := div_le_div_of_nonneg_right hlog hden.le
  linarith

/-- A maximum-based radius reduces to its geometric branch while it is strictly
above the floor. This uses an inequality, not equality for the maximum. -/
theorem shell_radius_le_geometric_above_floor {r A q R : ℝ} {k : ℕ}
    (hr : r ≤ max (A * q ^ k) R) (hfloor : R < r) : r ≤ A * q ^ k := by
  rcases le_total (A * q ^ k) R with h | h
  · rw [max_eq_right h] at hr
    linarith
  · rwa [max_eq_left h] at hr

/-- A uniformly bounded tail contributes at most its length times the floor. -/
theorem shell_radius_tail_sum_le (r : ℕ → ℝ) (R : ℝ) (n : ℕ)
    (hr : ∀ k < n, r k ≤ R) : ∑ k ∈ Finset.range n, r k ≤ (n : ℝ) * R := by
  calc
    ∑ k ∈ Finset.range n, r k ≤ ∑ _k ∈ Finset.range n, R :=
      Finset.sum_le_sum fun k hk => hr k (Finset.mem_range.mp hk)
    _ = (n : ℝ) * R := by simp

/-- The shifted radius `r (k + 1)` is bounded, up to the floor `R`, by the geometric
term `((O 0 * K) ^ α) * (q ^ α) ^ k` when the odometer `O` contracts by the factor `q`. -/
theorem shell_radius_from_odometer_contraction
    (O r : ℕ → ℝ) (q K α R : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hO : ∀ k ≤ n, 0 ≤ O k)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R) :
    ∀ k < n, r (k + 1) ≤ max (((O 0 * K) ^ α) * (q ^ α) ^ k) R := by
  have hgeom : ∀ k ≤ n, O k ≤ O 0 * q ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        O (k + 1) ≤ q * O k := hstep k (by omega)
        _ ≤ q * (O 0 * q ^ k) := mul_le_mul_of_nonneg_left (ih (by omega)) hq
        _ = O 0 * q ^ (k + 1) := by rw [pow_succ]; ring
  intro k hk
  apply (hr k hk).trans
  apply max_le_max_right
  calc
    (O k * K) ^ α ≤ ((O 0 * q ^ k) * K) ^ α :=
      Real.rpow_le_rpow (mul_nonneg (hO k (by omega)) hK)
        (mul_le_mul_of_nonneg_right (hgeom k (by omega)) hK) hα
    _ = ((O 0 * K) ^ α) * (q ^ α) ^ k := by
      rw [show O 0 * q ^ k * K = (O 0 * K) * q ^ k by ring,
        Real.mul_rpow (mul_nonneg (hO 0 (by omega)) hK) (pow_nonneg hq k),
        ← Real.rpow_natCast_mul hq k α, mul_comm (k : ℝ) α,
        Real.rpow_mul_natCast hq α k]

/-- A maximum of a geometric radius and a nonnegative floor is bounded in
total by the geometric series plus the accumulated floor. -/
theorem shell_radii_max_sum_le (r : ℕ → ℝ) (A q R : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1) (hR : 0 ≤ R) (n : ℕ)
    (hr : ∀ k < n, r k ≤ max (A * q ^ k) R) :
    ∑ k ∈ Finset.range n, r k ≤ A / (1 - q) + (n : ℝ) * R := by
  have hgeom : ∀ k, 0 ≤ A * q ^ k := fun k => mul_nonneg hA (pow_nonneg hq k)
  have hsum := shell_radii_sum_le (fun k => r k - R) A q hA hq hq1 n
    (fun k hk => by
      have hmax : max (A * q ^ k) R ≤ A * q ^ k + R := max_le (by linarith) (by linarith [hgeom k])
      linarith [hr k hk])
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

/-- For a shifted radius sequence `r (k + 1)` dominated, up to the floor `R`, by the
maxima of a contracting odometer, the sum of the radii is bounded by the initial radius,
a geometric series with ratio `q ^ α`, and the floor `R` times the number of shells. -/
theorem shell_radii_sum_from_odometer_contraction
    (O r : ℕ → ℝ) (q K α R : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K) (hα : 0 < α) (hR : 0 ≤ R)
    (hO : ∀ k ≤ n, 0 ≤ O k)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R) :
    ∑ k ∈ Finset.range (n + 1), r k ≤
      r 0 + (O 0 * K) ^ α / (1 - q ^ α) + (n : ℝ) * R := by
  have hdecay := shell_radius_from_odometer_contraction O r q K α R n hq hK hα.le hO hstep hr
  have hsum := shell_radii_max_sum_le (fun k => r (k + 1)) ((O 0 * K) ^ α) (q ^ α) R
    (Real.rpow_nonneg (mul_nonneg (hO 0 (Nat.zero_le n)) hK) α)
    (Real.rpow_nonneg hq α) (Real.rpow_lt_one hq hq1 hα) hR n hdecay
  rw [Finset.sum_range_succ']
  linarith

/-- First threshold crossing with the radius indexed by the previous maximum.
This combines the stopping-time estimate with the radius formula, including the
initial radius and the diameter error term `2 * D` on each shell. -/
theorem exists_shell_threshold_with_shifted_radius_budget
    (O r : ℕ → ℝ) (q K α R D C ε ω δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hK : 0 ≤ K) (hα : 0 < α)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hC : 0 < C) (hε : 0 < ε)
    (hO : ∀ k, 0 ≤ O k) (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k)
    (hr : ∀ k, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hbudget : let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      r 0 + (O 0 * K) ^ α / (1 - q ^ α) + L * R + (L + 1) * (2 * D) ≤ δ) :
    ∃ n : ℕ, O n ≤ ε ^ (-ω) ∧
      (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤ δ := by
  obtain ⟨n, hn, hbefore, hlog⟩ :=
    exists_first_shell_threshold_log_scale O q C ε ω hq hq1 hC hε hinitial hupper hstep
  have hnpos : 0 < n := by
    by_contra hn'
    have : n = 0 := Nat.eq_zero_of_not_pos hn'
    subst n
    exact (not_le_of_gt hinitial) hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  refine ⟨m + 1, hn, ?_⟩
  have hsum := shell_radii_sum_from_odometer_contraction O r q K α R m
    hq.le hq1 hK hα hR (fun k _ => hO k)
    (fun k hk => hstep k (hbefore k (by omega))) (fun k _ => hr k)
  have hm : (m : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.le_succ m
  have hfloor := mul_le_mul_of_nonneg_right (hm.trans hlog.le) hR
  have hdiam := mul_le_mul_of_nonneg_right (add_le_add_right hlog.le 1) (by linarith : 0 ≤ 2 * D)
  dsimp only at hbudget
  linarith

/-- The geometric, floor, and diameter contributions fit a common iteration budget
when the stopping index has a deterministic upper bound. -/
theorem shell_iteration_budget_le (r : ℕ → ℝ) (A q R D L : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (n : ℕ) (hn : (n : ℝ) ≤ L)
    (hr : ∀ k < n, r k ≤ max (A * q ^ k) R) :
    (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤
      A / (1 - q) + L * R + (L + 1) * (2 * D) := by
  have hsum := shell_radii_max_sum_le r A q R hA hq hq1 hR n hr
  have hfloor := mul_le_mul_of_nonneg_right hn hR
  have hdiam := mul_le_mul_of_nonneg_right (add_le_add_right hn 1) (by linarith : 0 ≤ 2 * D)
  linarith

/-- Fixed-factor odometer contraction and a logarithmic radius budget give a
stopping shell with both a small boundary maximum and controlled total growth. -/
theorem exists_shell_threshold_with_iteration_budget
    (O r : ℕ → ℝ) (q p C ε ω A R D δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hp : 0 ≤ p) (hp1 : p < 1)
    (hC : 0 < C) (hε : 0 < ε) (hA : 0 ≤ A) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k)
    (hr : ∀ k, (∀ j < k, ε ^ (-ω) < O j) → r k ≤ max (A * p ^ k) R)
    (hbudget : let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      A / (1 - p) + L * R + (L + 1) * (2 * D) ≤ δ) :
    ∃ n : ℕ, O n ≤ ε ^ (-ω) ∧
      (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤ δ := by
  obtain ⟨n, hn, hbefore, hbound⟩ :=
    exists_first_shell_threshold_log_scale O q C ε ω hq hq1 hC hε hinitial hupper hstep
  refine ⟨n, hn, ?_⟩
  apply (shell_iteration_budget_le r A p R D _ hA hp hp1 hR hD n hbound.le ?_).trans hbudget
  intro k hk
  apply hr k
  intro j hj
  exact hbefore j (lt_trans hj hk)

/-- The floor-scale contribution to the total radius vanishes, even with a
logarithmic number of shell steps. -/
theorem tendsto_shell_floor_log_bound (A B ω : ℝ) (hω : 0 < ω) :
    Tendsto (fun ε : ℝ => (A + B * Real.log ε⁻¹) * ε ^ ω) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun ε : ℝ => ε ^ ω) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hω.ne'] using hi.rpow_const (Or.inr hω.le)
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hω
  have hlim := (hp.const_mul A).add (hlog.neg.const_mul B)
  simp only [mul_zero, neg_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [] with ε
  rw [Real.log_inv]
  ring

/-- With logarithmically many shells, power-law radius floors and diameter terms
do not contribute to the limiting spatial budget. -/
theorem tendsto_shell_iteration_budget
    (A p a b R D ω ζ : ℝ) (hω : 0 < ω) (hζ : 0 < ζ) :
    Tendsto (fun ε : ℝ => A / (1 - p) +
      (a + b * Real.log ε⁻¹) * (R * ε ^ ω) +
      (a + b * Real.log ε⁻¹ + 1) * (2 * (D * ε ^ ζ)))
      (𝓝[>] 0) (𝓝 (A / (1 - p))) := by
  have hf := (tendsto_shell_floor_log_bound a b ω hω).const_mul R
  have hd := (tendsto_shell_floor_log_bound (a + 1) b ζ hζ).const_mul (2 * D)
  simp only [mul_zero] at hf hd
  have hsum := ((tendsto_const_nhds (x := A / (1 - p))).add hf).add hd
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with ε
  ring

/-- Any strict margin above the geometric contribution eventually covers the
floor and diameter terms in the shell budget. -/
theorem eventually_shell_iteration_budget_lt
    (A p a b R D ω ζ δ : ℝ) (hω : 0 < ω) (hζ : 0 < ζ)
    (hδ : A / (1 - p) < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      A / (1 - p) + (a + b * Real.log ε⁻¹) * (R * ε ^ ω) +
        (a + b * Real.log ε⁻¹ + 1) * (2 * (D * ε ^ ζ)) < δ :=
  (tendsto_order.1 (tendsto_shell_iteration_budget A p a b R D ω ζ hω hζ)).2 δ hδ

/-- The logarithmic first-crossing bound yields an admissible shell budget at
all sufficiently small scales whenever the geometric contribution has a strict
margin below the target. -/
theorem eventually_first_crossing_budget_lt
    (A p q C ω R D α β δ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hδ : A / (1 - p) < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      A / (1 - p) + L * (R * ε ^ α) + (L + 1) * (2 * (D * ε ^ β)) < δ := by
  have h := eventually_shell_iteration_budget_lt A p
    (Real.log C / (-Real.log q) + 1) ((1 - ω) / (-Real.log q)) R D α β δ hα hβ hδ
  filter_upwards [h] with ε hε
  convert hε using 1
  simp only [div_eq_mul_inv]
  ring

/-- At sufficiently small scales, every fixed-factor shell iteration satisfying
the stated odometer and radius bounds reaches its threshold within the target
spatial budget. -/
theorem eventually_exists_shell_threshold_with_budget
    (q p C ω A R D α β δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hp : 0 ≤ p) (hp1 : p < 1)
    (hC : 0 < C) (hA : 0 ≤ A) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hα : 0 < α) (hβ : 0 < β) (hδ : A / (1 - p) < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ O r : ℕ → ℝ,
      ε ^ (-ω) < O 0 → O 0 ≤ C / ε →
      (∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k) →
      (∀ k, (∀ j < k, ε ^ (-ω) < O j) →
        r k ≤ max (A * p ^ k) (R * ε ^ α)) →
      ∃ n : ℕ, O n ≤ ε ^ (-ω) ∧
        (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * (D * ε ^ β)) ≤ δ := by
  filter_upwards [eventually_first_crossing_budget_lt A p q C ω R D α β δ hα hβ hδ,
    self_mem_nhdsWithin] with ε hbudget hε O r hinitial hupper hstep hr
  exact exists_shell_threshold_with_iteration_budget O r q p C ε ω A (R * ε ^ α)
    (D * ε ^ β) δ hq hq1 hp hp1 hC hε hA
    (mul_nonneg hR (Real.rpow_pos_of_pos hε α).le)
    (mul_nonneg hD (Real.rpow_pos_of_pos hε β).le)
    hinitial hupper hstep hr hbudget.le

end LatticeProb.GeometricShellSums
