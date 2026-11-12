/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Bridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatScale
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Eta
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel

/-!
# The bridge shell bound (DZZ L2.5, `η` half; decision D62 route (1); task P2-DZZPRE2)

`bridgeShellBound_256 : BridgeShellBound 256`: the radial maximum `M_t = max_{s ≤ t} |X_s|` of the
planar Brownian bridge of length `t` satisfies `P(r − d ≤ M_t < r) ≤ 256 d/√t`.

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 459–461) only say "similar
argument"; no published proof of this bounded-density statement was found (see D62). Own
argument (D62 route (1)), all analytic:

1. the shell probability is `q_{B(0,r)}(t; 0, 0) − q_{B(0,r−d)}(t; 0, 0)`, and by Brownian scaling
   (`bridgeStay_ball_scale`) `q_{B(0,ρ)}(t; 0, 0) = G(t/ρ²)`, `G(τ) = q_{B(0,1)}(τ; 0, 0)`;
2. `G(τ) = 2πτ K(τ)` with `K(τ) = p_{B(0,1)}(τ; 0, 0)`, which is log-convex in `τ`
   (`killedHeat_sq_le_real`: Chapman–Kolmogorov + Cauchy–Schwarz);
3. a discrete log-convexity estimate (`logConvex_sub_le`: if `ψ_{j+1}² ≤ ψ_j ψ_{j+2}` then
   `ψ_n − ψ_{n+1} ≤ ψ_0/n`) along the progression `τ/2 ≤ x₀ < x₀ + s < … < τ + s` gives
   `K(τ) − K(τ + s) ≤ (4s/τ) sup_{x ≥ τ/2} K(x)`;
4. `K(x) ≤ min((2πx)⁻¹, 1/(πx²))` (`killedHeat_le_heatKernel`, `killedHeat_le_rpow`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat

/-! ### Discrete log-convexity -/

lemma logConvex_pow_le (ψ : ℕ → ℝ) (h0 : ∀ j, 0 ≤ ψ j)
    (h : ∀ j, ψ (j + 1) ^ 2 ≤ ψ j * ψ (j + 2)) (n : ℕ) :
    ψ n ^ (n + 1) ≤ ψ 0 * ψ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases (h0 (n + 1)).eq_or_lt with h1 | h1
    · rw [← h1, zero_pow (by omega)]
      exact mul_nonneg (h0 0) (pow_nonneg (h0 _) _)
    · have key : ψ (n + 1) ^ n * ψ (n + 1) ^ (n + 2) ≤
          ψ (n + 1) ^ n * (ψ 0 * ψ (n + 2) ^ (n + 1)) := by
        calc ψ (n + 1) ^ n * ψ (n + 1) ^ (n + 2) = (ψ (n + 1) ^ 2) ^ (n + 1) := by ring
          _ ≤ (ψ n * ψ (n + 2)) ^ (n + 1) := pow_le_pow_left₀ (sq_nonneg _) (h n) _
          _ = ψ n ^ (n + 1) * ψ (n + 2) ^ (n + 1) := mul_pow _ _ _
          _ ≤ (ψ 0 * ψ (n + 1) ^ n) * ψ (n + 2) ^ (n + 1) :=
              mul_le_mul_of_nonneg_right ih (pow_nonneg (h0 _) _)
          _ = _ := by ring
      exact le_of_mul_le_mul_left key (pow_pos h1 n)

/-- If `ψ ≥ 0` is log-convex (`ψ_{j+1}² ≤ ψ_j ψ_{j+2}`), then `ψ_n − ψ_{n+1} ≤ ψ_0 / n`. -/
lemma logConvex_sub_le (ψ : ℕ → ℝ) (h0 : ∀ j, 0 ≤ ψ j)
    (h : ∀ j, ψ (j + 1) ^ 2 ≤ ψ j * ψ (j + 2)) {n : ℕ} (hn : 1 ≤ n) :
    ψ n - ψ (n + 1) ≤ ψ 0 / n := by
  have hP := logConvex_pow_le ψ h0 h n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a := ψ n with ha_def
  set b := ψ (n + 1) with hb_def
  set c := ψ 0 with hc_def
  have ha0 : 0 ≤ a := h0 n
  rcases le_or_gt a b with hab | hab
  · have : 0 ≤ c / n := div_nonneg (h0 0) hn'.le
    linarith
  have hb : 0 < b := by
    rcases (h0 (n + 1)).eq_or_lt with hb | hb
    · exfalso
      have ha : 0 < a := lt_of_le_of_lt (h0 _) (hb_def ▸ hab)
      rw [show b = 0 from hb.symm, zero_pow (by omega), mul_zero] at hP
      exact absurd hP (not_le.mpr (pow_pos ha _))
    · exact hb
  have hab' : 1 ≤ a / b := (one_le_div hb).mpr hab.le
  have hB := one_add_mul_le_pow (a := a / b - 1) (by linarith) n
  rw [add_sub_cancel, div_pow] at hB
  have hbn : 0 < b ^ n := pow_pos hb n
  rw [le_div_iff₀ hbn] at hB
  have hd : 0 ≤ (n : ℝ) * (a - b) * b ^ n :=
    mul_nonneg (mul_nonneg hn'.le (by linarith)) hbn.le
  have h3 : (n : ℝ) * (a - b) * b ^ n ≤ a ^ (n + 1) := by
    have e : (1 + (n : ℝ) * (a / b - 1)) * b ^ n = b ^ n + (n * (a - b) * b ^ n) / b := by
      field_simp
    rw [e] at hB
    have h4 : (n * (a - b) * b ^ n) / b ≥ (n : ℝ) * (a - b) * b ^ n / a := by
      exact div_le_div_of_nonneg_left hd hb hab.le
    rw [pow_succ']
    have ha1 : a ≠ 0 := (hb.trans hab).ne'
    have h5 : a * ((n : ℝ) * (a - b) * b ^ n / a) = (n : ℝ) * (a - b) * b ^ n := by
      field_simp
    have h6 : a * (b ^ n + (n * (a - b) * b ^ n) / b) ≤ a * a ^ n :=
      mul_le_mul_of_nonneg_left hB ha0
    nlinarith [mul_le_mul_of_nonneg_left h4 ha0, mul_nonneg ha0 hbn.le]
  have hkey : (n : ℝ) * (a - b) * b ^ n ≤ c * b ^ n := h3.trans hP
  rw [le_div_iff₀ hn']
  have := le_of_mul_le_mul_right hkey hbn
  linarith

/-! ### The killed heat kernel of the unit disc at its centre -/

/-- `K(x) = p_{B(0,1)}(x; 0, 0)`. -/
def unitDiscK (x : ℝ) : ℝ := killedHeat (Metric.ball 0 1) x.toNNReal 0 0

/-- `G(x) = q_{B(0,1)}(x; 0, 0)`. -/
def unitDiscG (x : ℝ) : ℝ := bridgeStay (Metric.ball 0 1) x.toNNReal 0 0

lemma unitDiscK_nonneg (x : ℝ) : 0 ≤ unitDiscK x := killedHeat_nonneg _ _ _ _

lemma unitDiscG_eq {x : ℝ} (hx : 0 < x) : unitDiscG x = 2 * Real.pi * x * unitDiscK x := by
  unfold unitDiscG unitDiscK killedHeat heatKernel
  rw [Real.coe_toNNReal _ hx.le]
  simp only [sub_self, norm_zero]
  have := Real.pi_pos
  field_simp
  simp

lemma unitDiscK_le_inv {x : ℝ} (hx : 0 < x) : unitDiscK x ≤ (2 * Real.pi * x)⁻¹ := by
  have h := (killedHeat_le_heatKernel (Metric.ball (0 : ℂ) 1) x.toNNReal 0 0).trans
    (heatKernel_le_inv _ (NNReal.coe_nonneg _) 0 0)
  rwa [Real.coe_toNNReal _ hx.le] at h

lemma unitDiscK_le_inv_sq {x : ℝ} (hx : 0 < x) : unitDiscK x ≤ 1 / (Real.pi * x ^ 2) := by
  have h := killedHeat_le_rpow (A := Metric.ball (0 : ℂ) 1) (c := 0) zero_le_one subset_rfl hx 0 0
  rw [Real.rpow_neg hx.le, Real.rpow_two] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-- Log-convexity of `K` along an arithmetic progression. -/
lemma unitDiscK_sub_le_div {x₀ s : ℝ} (hx₀ : 0 < x₀) (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) :
    unitDiscK (x₀ + n * s) - unitDiscK (x₀ + (n + 1) * s) ≤ unitDiscK x₀ / n := by
  have h := logConvex_sub_le (fun j : ℕ => unitDiscK (x₀ + j * s)) (fun j => unitDiscK_nonneg _)
    (fun j => ?_) hn
  · simpa using h
  have hp : 0 < x₀ + (j : ℝ) * s := by positivity
  have hq : 0 < x₀ + ((j + 2 : ℕ) : ℝ) * s := by positivity
  have := killedHeat_sq_le_real (A := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball hp hq 0
  simp only [unitDiscK]
  convert this using 4
  push_cast
  ring

/-- `K(τ) − K(τ + s) ≤ (4s/τ) M` whenever `K ≤ M` on `[τ/2, ∞)`. -/
lemma unitDiscK_sub_le {τ s M : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s)
    (hM : ∀ x, τ / 2 ≤ x → unitDiscK x ≤ M) :
    unitDiscK τ - unitDiscK (τ + s) ≤ 4 * s / τ * M := by
  have hM0 : 0 ≤ M := (unitDiscK_nonneg τ).trans (hM τ (by linarith))
  have hK1 := unitDiscK_nonneg (τ + s)
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0; simp
  set n := ⌊τ / (2 * s)⌋₊ with hn_def
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hlt : τ / (2 * s) < 1 := Nat.floor_eq_zero.mp hn
    rw [div_lt_one (by positivity)] at hlt
    have h1 : 1 ≤ 4 * s / τ := by rw [le_div_iff₀ hτ]; linarith
    have := hM τ (by linarith)
    nlinarith
  · have hnle : (n : ℝ) ≤ τ / (2 * s) := Nat.floor_le (by positivity)
    have hlt : τ / (2 * s) < n + 1 := Nat.lt_floor_add_one _
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hns : (n : ℝ) * s ≤ τ / 2 := by
      rw [le_div_iff₀ (by positivity)] at hnle
      linarith
    set x₀ := τ - n * s
    have hx₀ : τ / 2 ≤ x₀ := by simp only [x₀]; linarith
    have h := unitDiscK_sub_le_div (x₀ := x₀) (by linarith) hs0 hn
    rw [show x₀ + n * s = τ by simp only [x₀]; ring,
      show x₀ + (n + 1) * s = τ + s by simp only [x₀]; ring] at h
    have hK0 := hM x₀ hx₀
    have hτn : τ ≤ 4 * s * n := by
      rw [div_lt_iff₀ (by positivity)] at hlt
      nlinarith
    have hn' : (0 : ℝ) < n := by linarith
    calc unitDiscK τ - unitDiscK (τ + s) ≤ unitDiscK x₀ / n := h
      _ ≤ M / n := div_le_div_of_nonneg_right hK0 hn'.le
      _ ≤ 4 * s / τ * M := by
          rw [div_le_iff₀ hn', div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hτ]
          nlinarith

/-- The two increments bounds for `G`: `G(τ) − G(τ + s) ≤ 8s/τ` and `≤ 32 s/τ²`. -/
lemma unitDiscG_sub_le {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) :
    unitDiscG τ - unitDiscG (τ + s) ≤ 8 * s / τ ∧
      unitDiscG τ - unitDiscG (τ + s) ≤ 32 * s / τ ^ 2 := by
  have hpi := Real.pi_pos
  have hG : unitDiscG τ - unitDiscG (τ + s) ≤
      2 * Real.pi * τ * (unitDiscK τ - unitDiscK (τ + s)) := by
    rw [unitDiscG_eq hτ, unitDiscG_eq (by linarith)]
    have := unitDiscK_nonneg (τ + s)
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt (mul_pos two_pos hpi)) hs) this]
  have hK1 := unitDiscK_sub_le (M := (Real.pi * τ)⁻¹) hτ hs fun x hx => by
    have hx0 : 0 < x := by linarith
    refine (unitDiscK_le_inv hx0).trans ?_
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  have hK2 := unitDiscK_sub_le (M := 4 / (Real.pi * τ ^ 2)) hτ hs fun x hx => by
    have hx0 : 0 < x := by linarith
    refine (unitDiscK_le_inv_sq hx0).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left
      (mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ τ / 2) hx) hpi.le]
  have h2 : 0 ≤ 2 * Real.pi * τ := by positivity
  constructor
  · refine hG.trans ((mul_le_mul_of_nonneg_left hK1 h2).trans (le_of_eq ?_))
    field_simp
    ring
  · refine hG.trans ((mul_le_mul_of_nonneg_left hK2 h2).trans (le_of_eq ?_))
    field_simp
    ring

/-- Scaling: `q_{B(0,ρ)}(t; 0, 0) = G(t/ρ²)`. -/
lemma bridgeStay_ball_eq_unitDiscG {t : ℝ≥0} (ht : t ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    bridgeStay (Metric.ball 0 ρ) t 0 0 = unitDiscG ((t : ℝ) / ρ ^ 2) := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hτ : ((t : ℝ) / ρ ^ 2).toNNReal ≠ 0 := by
    simpa using (by positivity : (0 : ℝ) < (t : ℝ) / ρ ^ 2)
  rw [bridgeStay_ball_scale ht, unitDiscG, bridgeStay_ball_scale hτ,
    Real.coe_toNNReal _ (by positivity), Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hρ.le, one_div_div]

/-! ### The shell bound -/

/-- **The bridge shell bound** (D62 route (1)): `P(r − d ≤ max_{s≤t} |X_s| < r) ≤ 256 d/√t`. -/
theorem bridgeShellBound_256 : BridgeShellBound 256 := by
  intro t ht r d hd
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have := (isPlanarBridge_stdBridge ht).gauss.isProbabilityMeasure
  set q := Real.sqrt t with hq_def
  have hq : 0 < q := Real.sqrt_pos.mpr ht'
  have hqq : (t : ℝ) = q ^ 2 := (Real.sq_sqrt ht'.le).symm
  have hR : 0 ≤ 256 * d / q := by positivity
  set X := stdBridge t
  set S := {ω | ∃ s : ℝ≥0, s ≤ t ∧ r - d ≤ ‖X s ω‖} ∩ {ω | ∀ s : ℝ≥0, s ≤ t → ‖X s ω‖ < r}
  change P2.real S ≤ 256 * d / q
  -- `r ≤ 0`: empty event
  rcases le_or_gt r 0 with hr | hr
  · have : S = ∅ := by
      ext ω
      simp only [S, mem_inter_iff, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, h⟩
      exact absurd (h 0 zero_le) (not_lt.mpr (hr.trans (norm_nonneg _)))
    rw [this, measureReal_empty]
    exact hR
  set Stay : ℝ → Set Ω2 := fun ρ => bridgeEvent (Metric.ball 0 ρ) t 0 0 X with hStay
  have hS : S = Stay r \ Stay (r - d) := by
    ext ω
    simp only [S, Stay, mem_inter_iff, mem_sdiff, bridgeEvent, Set.mem_ofPred_eq, bridgePath,
      Metric.mem_ball, dist_zero_right, sub_self, mul_zero, zero_add, not_forall, not_lt,
      exists_prop]
    tauto
  have hreal : ∀ ρ, P2.real (Stay ρ) = bridgeStay (Metric.ball 0 ρ) t 0 0 := fun ρ => rfl
  -- crude bound `P(S) ≤ min(1, 2r²/t)`
  have hcrude : P2.real S ≤ 2 * r ^ 2 / t := by
    have h1 : P2.real S ≤ P2.real (Stay r) := by
      rw [hS]; exact measureReal_mono sdiff_subset
    rw [hreal] at h1
    have hh : (t / 2 + t / 2 : ℝ≥0) = t := add_halves t
    have h2 := bridgeStay_le_of_subset_ball (A := Metric.ball (0 : ℂ) r) (c := 0) hr.le subset_rfl
      (a := t / 2) (by simpa using ht) 0 0
    rw [hh] at h2
    refine h1.trans (h2.trans (le_of_eq ?_))
    push_cast
    field_simp
  have hone : P2.real S ≤ 1 := measureReal_le_one
  rcases le_or_gt d (r / 2) with hdr | hdr
  · -- main case: `d ≤ r/2`
    have hrd : 0 < r - d := by linarith
    have hsub : Stay (r - d) ⊆ Stay r := fun ω hω s hs =>
      Metric.ball_subset_ball (by linarith) (hω s hs)
    have hdiff : P2.real S = bridgeStay (Metric.ball 0 r) t 0 0 -
        bridgeStay (Metric.ball 0 (r - d)) t 0 0 := by
      rw [hS, measureReal_def, measure_sdiff hsub
        (nullMeasurableSet_bridgeEvent (isPlanarBridge_stdBridge ht) Metric.isOpen_ball 0 0)
        (measure_ne_top _ _), ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]
      rfl
    rw [hdiff, bridgeStay_ball_eq_unitDiscG ht hr, bridgeStay_ball_eq_unitDiscG ht hrd]
    set τ : ℝ := (t : ℝ) / r ^ 2 with hτ_def
    set s : ℝ := (t : ℝ) / (r - d) ^ 2 - τ with hs_def
    have hτ : 0 < τ := by positivity
    have hs8 : s ≤ 8 * t * d / r ^ 3 := by
      calc s = t * (d * (2 * r - d)) / (r ^ 2 * (r - d) ^ 2) := by
              simp only [hs_def, hτ_def]; field_simp; ring
        _ ≤ t * (d * (2 * r)) / (r ^ 2 * (r ^ 2 / 4)) := by
              gcongr
              · linarith
              · nlinarith [mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ r / 2)
                  (by linarith : r / 2 ≤ r - d)]
        _ = 8 * t * d / r ^ 3 := by field_simp; ring
    have hs0 : 0 ≤ s := by
      simp only [hs_def, hτ_def]
      exact sub_nonneg.mpr (div_le_div_of_nonneg_left ht'.le (by positivity) (by nlinarith))
    have hts : (t : ℝ) / (r - d) ^ 2 = τ + s := by simp only [hs_def]; ring
    rw [hts]
    obtain ⟨hG1, hG2⟩ := unitDiscG_sub_le hτ hs0
    have hs8' : s * r ^ 3 ≤ 8 * q ^ 2 * d := by
      rw [← hqq]; rwa [le_div_iff₀ (by positivity)] at hs8
    rcases le_or_gt q r with hqr | hqr
    · refine hG1.trans ?_
      rw [hτ_def, hqq, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hq]
      have : s * r ^ 2 * q ≤ s * r ^ 2 * r := mul_le_mul_of_nonneg_left hqr (by positivity)
      have h3 : s * r ^ 2 ≤ 8 * q * d := by
        have : s * r ^ 2 * q ≤ 8 * q ^ 2 * d := by nlinarith
        nlinarith
      nlinarith
    · refine hG2.trans ?_
      rw [hτ_def, hqq, div_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hq]
      have h3 : s * r ^ 4 ≤ 8 * q ^ 3 * d := by
        have : s * r ^ 3 * r ≤ 8 * q ^ 2 * d * q :=
          mul_le_mul hs8' hqr.le hr.le (by positivity)
        nlinarith
      nlinarith
  · -- `d > r/2`: crude bounds
    rcases le_or_gt r q with hrq | hrq
    · refine hcrude.trans ?_
      rw [hqq, div_le_div_iff₀ (by positivity) hq]
      have := mul_le_mul_of_nonneg_left hrq (by positivity : (0 : ℝ) ≤ 2 * r * q)
      nlinarith
    · refine hone.trans ?_
      rw [le_div_iff₀ hq]
      linarith

end DZZ
end LQGMetric
