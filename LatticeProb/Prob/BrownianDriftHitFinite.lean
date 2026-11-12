import Mathlib
import LatticeProb.Prob.UpcrossIntervals

/-!
# A Brownian motion with positive drift reaches every nonnegative level

For a Brownian motion `B` and a drift `mu > 0`, almost surely `B n / n → 0` along the integers
(strong law of large numbers for the i.i.d. standard Gaussian increments `B (n+1) - B n`), so
`B s + mu * s` is eventually above any level `c`; by continuity of the paths and `B 0 = 0` the
level `c ≥ 0` is hit.

* `LatticeProb.ae_tendsto_inv_mul_brownian`: `n⁻¹ * B n → 0` almost surely.
* `LatticeProb.ae_hitFrom_ne_top_brownian_drift`: for `0 ≤ c` the first time
  `B s + mu * s = c` is almost surely finite.  (For `c < 0` the statement is false: the level is
  hit with probability `exp (2 * mu * c) < 1`.)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Strong law along the integers for Brownian motion: `n⁻¹ * B n → 0` almost surely. -/
theorem ae_tendsto_inv_mul_brownian (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * B (n : ℝ≥0) ω) atTop (𝓝 0) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let X : ℕ → Ω → ℝ := fun i ω => B ((i + 1 : ℕ) : ℝ≥0) ω - B (i : ℝ≥0) ω
  have hind : iIndepFun X P :=
    hB.hasIndepIncrements.nat (t := fun i : ℕ => (i : ℝ≥0)) (fun a b hab => Nat.mono_cast hab)
  have hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P := by
    intro i
    have h := hB.hasLaw_sub ((i + 1 : ℕ) : ℝ≥0) (i : ℝ≥0)
    have hd : nndist ((i + 1 : ℕ) : ℝ≥0).1 (i : ℝ≥0).1 = 1 := by
      rw [← NNReal.coe_inj, coe_nndist]
      simp
    rw [hd] at h
    exact h
  have hint : Integrable (X 0) P :=
    (hB.integrable_eval ((0 + 1 : ℕ) : ℝ≥0)).sub (hB.integrable_eval ((0 : ℕ) : ℝ≥0))
  have hmean : ∫ ω, X 0 ω ∂P = 0 := by
    simp only [X]
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
      hB.integral_eval, sub_zero]
  have hlln := strong_law_ae X hint (fun i j hij => hind.indepFun hij)
    (fun i => (hlaw i).identDistrib (hlaw 0))
  filter_upwards [hlln, hB.eval_zero_ae_eq_zero] with ω h h0
  rw [hmean] at h
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, X i ω = B (n : ℝ≥0) ω := by
    intro n
    have := Finset.sum_range_sub (fun i : ℕ => B (i : ℝ≥0) ω) n
    simpa [X, h0] using this
  simpa [hsum] using h

/-- A Brownian motion with positive drift `mu` hits every level `c ≥ 0` in finite time, almost
surely. -/
theorem ae_hitFrom_ne_top_brownian_drift (hB : IsBrownianReal B P) {mu c : ℝ} (hmu : 0 < mu)
    (hc : 0 ≤ c) :
    ∀ᵐ ω ∂P, hitFrom c 0 (fun s : ℝ≥0 => B s ω + mu * s) ≠ ⊤ := by
  filter_upwards [ae_tendsto_inv_mul_brownian hB, hB.cont, hB.eval_zero_ae_eq_zero] with
    ω h hcont h0
  have h1 : ∀ᶠ n : ℕ in atTop, -(mu / 2) < (n : ℝ)⁻¹ * B (n : ℝ≥0) ω :=
    h.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ n : ℕ in atTop, 2 * c / mu ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and (eventually_gt_atTop 0))).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn3
  have hB' : -(mu / 2) * n < B (n : ℝ≥0) ω := by
    have := mul_lt_mul_of_pos_right hn1 hnpos
    have e : (n : ℝ)⁻¹ * B (n : ℝ≥0) ω * n = B (n : ℝ≥0) ω := by field_simp
    rwa [e] at this
  have hmn : 2 * c ≤ n * mu := (div_le_iff₀ hmu).1 hn2
  have hcw : c ≤ B (n : ℝ≥0) ω + mu * ((n : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_natCast]
    nlinarith
  have hcts : Continuous fun s : ℝ≥0 => B s ω + mu * (s : ℝ) := by fun_prop
  have hc0 : (fun s : ℝ≥0 => B s ω + mu * (s : ℝ)) 0 ≤ c := by simpa [h0] using hc
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ (n : ℝ≥0))
    hcts.continuousOn (show c ∈ Set.Icc _ _ from ⟨hc0, hcw⟩)
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hitFrom_le (zero_le) hs)

end LatticeProb
