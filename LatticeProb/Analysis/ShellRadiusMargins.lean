import Mathlib

/-!
# Shell radius margins

Elementary estimates for a radius `r` lying between a lower and an upper envelope, and for
power-law floors `ε ^ q` as `ε → 0⁺`:

* strict slack of a local mass bound under a power-law radius:
  `shell_odometer_factor_le_radius_rpow`, `shell_strict_local_mass_slack`,
  `exists_shell_radius_coefficient`, `shell_strict_local_mass_slack_of_radius`,
  `shell_mass_test_above_scale`;
* margins for radius floors and cutoffs:
  `eventually_mul_rpow_lt_mul_rpow`, `eventually_shell_survival_floor`,
  `exists_shell_radius_floor_exponent`, `shell_margins_of_radius_bounds`,
  `shell_test_radius_le_cutoff`.
-/

namespace LatticeProb.ShellRadiusMargins

open Filter Topology

/-- A positive power of the variable tends to zero along the right-hand neighbourhood
filter of zero. -/
theorem tendsto_rpow_nhdsGT_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa [Real.zero_rpow hb.ne'] using hi.rpow_const (Or.inr hb.le)

/-- Raising the lower bound on a radius to a positive power recovers the product
bound, including when the product is zero. -/
theorem shell_odometer_factor_le_radius_rpow
    {O ε K r β : ℝ} (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K)
    (hβ : 0 < β) (hr : (O * ε * K) ^ (1 / β) ≤ r) :
    O * ε * K ≤ r ^ β := by
  have hbase : 0 ≤ O * ε * K := mul_nonneg (mul_nonneg hO hε.le) hK
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hr hβ.le
  simpa only [one_div, Real.rpow_inv_rpow hbase hβ.ne'] using h

/-- A strict coefficient margin makes the local mass bound strictly smaller than the
threshold `s₁ * (a * r) ^ β / ε`. The factor `a` is the ratio between the test radius
and the radius `r`. -/
theorem shell_strict_local_mass_slack
    {O ε K r β a s₁ C : ℝ}
    (hO : 0 ≤ O) (hε : 0 < ε) (hr : 0 < r)
    (ha : 0 < a) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * a ^ β * K) (hpower : O * ε * K ≤ r ^ β) :
    C * O < s₁ * (a * r) ^ β / ε := by
  have hapos : 0 < s₁ * a ^ β := mul_pos hs₁ (Real.rpow_pos_of_pos ha β)
  rw [Real.mul_rpow ha.le hr.le, lt_div_iff₀ hε]
  by_cases hOz : O = 0
  · subst O
    simp only [mul_zero, zero_mul]
    positivity
  · have hOpos : 0 < O := lt_of_le_of_ne hO (Ne.symm hOz)
    have h1 := mul_lt_mul_of_pos_right hcoeff (mul_pos hOpos hε)
    have h2 := mul_le_mul_of_nonneg_left hpower hapos.le
    nlinarith

/-- For every constant there is a positive coefficient whose scaled product with
`s₁ * a ^ β` strictly exceeds that constant. -/
theorem exists_shell_radius_coefficient
    {a β s₁ C : ℝ} (ha : 0 < a) (hs₁ : 0 < s₁) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ C < s₁ * a ^ β * K := by
  have hd : 0 < s₁ * a ^ β := mul_pos hs₁ (Real.rpow_pos_of_pos ha β)
  refine ⟨(C + 1) / (s₁ * a ^ β), div_pos (by linarith) hd, ?_⟩
  rw [mul_div_cancel₀ _ hd.ne']
  linarith

/-- The radius formula and a strict coefficient choice together imply the strict
local mass slack, for any nonnegative radius floor. -/
theorem shell_strict_local_mass_slack_of_radius
    {O ε K r β a s₁ C : ℝ}
    (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K) (hr : 0 < r) (hβ : 0 < β)
    (ha : 0 < a) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * a ^ β * K)
    (hradius : (O * ε * K) ^ (1 / β) ≤ r) :
    C * O < s₁ * (a * r) ^ β / ε :=
  shell_strict_local_mass_slack hO hε hr ha hs₁ hcoeff
    (shell_odometer_factor_le_radius_rpow hO hε hK hβ hradius)

/-- If a fixed multiple of a power `ε ^ ω` lies below `r / 4` after the factor `c / 8`
and `c ≤ 1`, then the smaller power `ε ^ βₘ` with `ω ≤ βₘ` lies below `r / 4` too. -/
theorem shell_mass_test_above_scale
    {ε ω βₘ c r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : ω ≤ βₘ)
    (hc : c ≤ 1) (hr : 0 ≤ r) (hmin : 10 * ε ^ ω ≤ (c / 8) * r) :
    ε ^ βₘ ≤ r / 4 := by
  have hpow := Real.rpow_le_rpow_of_exponent_ge hε hε1 hω
  have hpow_nonneg : 0 ≤ ε ^ ω := Real.rpow_nonneg hε.le ω
  have hcr : c * r ≤ r := by simpa using mul_le_mul_of_nonneg_right hc hr
  nlinarith

/-- A larger exponent beats any fixed coefficient times a smaller exponent near zero. -/
theorem eventually_mul_rpow_lt_mul_rpow
    {a b A B : ℝ} (hab : b < a) (hB : 0 < B) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, A * ε ^ a < B * ε ^ b := by
  have hpow := tendsto_rpow_nhdsGT_zero (sub_pos.mpr hab)
  have hlim : Tendsto (fun ε : ℝ => A * ε ^ (a - b)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hpow.const_mul A
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.1 hlim).2 B hB] with ε hε hsmall
  have hmul := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hε b)
  have hpow' : ε ^ (a - b) * ε ^ b = ε ^ a := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  calc
    A * ε ^ a = (A * ε ^ (a - b)) * ε ^ b := by rw [← hpow']; ring
    _ < B * ε ^ b := hmul

/-- A power `ε ^ ω` with `q < ω` is eventually below `c / 8` times `ε ^ q`, after
the factor `10`. -/
theorem eventually_shell_survival_floor
    {ω q c : ℝ} (hqω : q < ω) (hc : 0 < c) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 10 * ε ^ ω < (c / 8) * ε ^ q :=
  eventually_mul_rpow_lt_mul_rpow hqω (by positivity)

/-- One power floor with an exponent below both `ω` and `d` simultaneously dominates
the power `ε ^ d` and the lower bound `10 * ε ^ ω` from the survival estimate. -/
theorem exists_shell_radius_floor_exponent
    {ω d c : ℝ} (hω : 0 < ω) (hd : 0 < d) (hc : 0 < c) :
    ∃ q : ℝ, 0 < q ∧ q < ω ∧ q < d ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ε ^ d ≤ ε ^ q / 2 ∧ 10 * ε ^ ω ≤ (c / 8) * ε ^ q := by
  let q := min ω d / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqω : q < ω := by dsimp [q]; linarith [min_le_left ω d]
  have hqd : q < d := by dsimp [q]; linarith [min_le_right ω d]
  refine ⟨q, hq, hqω, hqd, ?_⟩
  filter_upwards [eventually_mul_rpow_lt_mul_rpow (A := 2) (B := 1) hqd (by norm_num),
    eventually_shell_survival_floor hqω hc] with ε hdiam hsurv
  constructor
  · linarith
  · exact hsurv.le

/-- Two-sided bounds `L ≤ r ≤ U` on a radius, together with the stated upper envelope
conditions, yield the geometric margin inequalities at `r`. -/
theorem shell_margins_of_radius_bounds
    (ε ω r L U D R ρ c dd : ℝ)
    (hc : 0 ≤ c) (hr : L ≤ r) (hrU : r ≤ U)
    (hD : D ≤ L / 2) (hambient : U + R ≤ ρ)
    (hclosure : R + U / 4 + D < ρ / 2)
    (hmargin : R + (((c / 8) * U + D) + U / 4) + D + U / 4 ≤ ρ)
    (hmin : 10 * ε ^ ω ≤ (c / 8) * L) (hmax : (c / 8) * U ≤ dd) :
    D ≤ r / 2 ∧ r + R ≤ ρ ∧ R + r / 4 + D < ρ / 2 ∧
      R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ ∧
      10 * ε ^ ω ≤ (c / 8) * r ∧ (c / 8) * r ≤ dd := by
  have hc' : 0 ≤ c / 8 := by positivity
  have hcr := mul_le_mul_of_nonneg_left hr hc'
  have hcrU := mul_le_mul_of_nonneg_left hrU hc'
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  exact ⟨hmin.trans hcr, hcrU.trans hmax⟩

/-- A cutoff `c ≤ 1` and a radius `r ≤ dd` bound the scaled radius `(c / 8) * r`
by `dd`. -/
theorem shell_test_radius_le_cutoff
    (c r dd : ℝ) (hc : c ≤ 1) (hr : 0 ≤ r) (hdd : r ≤ dd) :
    (c / 8) * r ≤ dd := by
  have h := mul_le_mul_of_nonneg_right (show c / 8 ≤ 1 by linarith) hr
  linarith

end LatticeProb.ShellRadiusMargins
