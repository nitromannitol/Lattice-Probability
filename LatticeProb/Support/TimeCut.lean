/-
The continuous time weights that replace the indicator of a time interval in the
local central limit step.

the local central limit step reads a CONTINUOUS weight
in each of the two time variables, and the weight has to vanish below the time
`δ` at which the local central limit theorem starts being uniform.  The double
time sum of `prop:dlt4-heat-potential-invariance` carries no weight at all: it is
the indicator of `[0, k)`.  The weights below interpolate between the two.  At
resolution `n` the weight is the trapezoid that is zero below `1/n` and above
`ρ`, one on `[2/n, ρ - 2/n]`, and affine in between.

Two properties do the work.  The weight INCREASES with `n`, and it converges
pointwise to the indicator of the open interval `(0, ρ)`, so that the continuum
double time integrals it produces increase to the double time integral of
`prop:dlt4-heat-potential-invariance` by monotone convergence.  The second weight,
`lowerCut`, shortens the interval by `3/n` as well, which is what makes its support
fit strictly inside the lattice time range for every large scale.
-/
import Mathlib

open Filter Topology

namespace LatticeProb.TimeCut

/-- The continuous trapezoidal weight of the time interval `(0, ρ)` at resolution `n`. -/
noncomputable def timeCut (n : ℕ) (ρ : ℝ) : ℝ → ℝ :=
  fun t => min 1 (max 0 ((n : ℝ) * t - 1)) * min 1 (max 0 ((n : ℝ) * (ρ - t) - 1))

theorem continuous_timeCut (n : ℕ) (ρ : ℝ) : Continuous (timeCut n ρ) := by
  unfold timeCut
  fun_prop

theorem timeCut_nonneg (n : ℕ) (ρ t : ℝ) : 0 ≤ timeCut n ρ t := by
  have h1 : (0:ℝ) ≤ min 1 (max 0 ((n : ℝ) * t - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  have h2 : (0:ℝ) ≤ min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  exact mul_nonneg h1 h2

theorem timeCut_le_one (n : ℕ) (ρ t : ℝ) : timeCut n ρ t ≤ 1 := by
  have h1 : min 1 (max 0 ((n : ℝ) * t - 1)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) ≤ 1 := min_le_left _ _
  have h2' : (0:ℝ) ≤ min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  calc timeCut n ρ t ≤ 1 * min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) :=
        mul_le_mul_of_nonneg_right h1 h2'
    _ ≤ 1 := by rw [one_mul]; exact h2

theorem timeCut_eq_zero_of_small {n : ℕ} {ρ t : ℝ} (h : (n : ℝ) * t ≤ 1) :
    timeCut n ρ t = 0 := by
  have h0 : max 0 ((n : ℝ) * t - 1) = 0 := max_eq_left (by linarith)
  show min 1 (max 0 ((n : ℝ) * t - 1)) * _ = 0
  rw [h0, min_eq_right (by norm_num : (0:ℝ) ≤ 1), zero_mul]

theorem timeCut_eq_zero_of_ge {n : ℕ} {ρ t : ℝ} (h : ρ ≤ t) : timeCut n ρ t = 0 := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : (n : ℝ) * (ρ - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn (by linarith)
  have h0 : max 0 ((n : ℝ) * (ρ - t) - 1) = 0 := max_eq_left (by linarith)
  show _ * min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) = 0
  rw [h0, min_eq_right (by norm_num : (0:ℝ) ≤ 1), mul_zero]

theorem timeCut_eq_one {n : ℕ} {ρ t : ℝ} (h1 : 2 ≤ (n : ℝ) * t)
    (h2 : 2 ≤ (n : ℝ) * (ρ - t)) : timeCut n ρ t = 1 := by
  have e1 : min 1 (max 0 ((n : ℝ) * t - 1)) = 1 := by
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  have e2 : min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) = 1 := by
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  show min 1 (max 0 ((n : ℝ) * t - 1)) * min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) = 1
  rw [e1, e2, one_mul]

theorem timeCut_mono (ρ t : ℝ) : Monotone (fun n : ℕ => timeCut n ρ t) := by
  intro m n hmn
  have hm : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hfac : ∀ c : ℝ, min 1 (max 0 ((m : ℝ) * c - 1)) ≤ min 1 (max 0 ((n : ℝ) * c - 1)) := by
    intro c
    rcases le_total 0 c with hc | hc
    · have : (m : ℝ) * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right hm hc
      exact min_le_min le_rfl (max_le_max le_rfl (by linarith))
    · have hzm : max 0 ((m : ℝ) * c - 1) = 0 := by
        refine max_eq_left ?_
        have : (m : ℝ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hc
        linarith
      rw [hzm, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      exact le_min (by norm_num) (le_max_left _ _)
  have h1 := hfac t
  have h2 := hfac (ρ - t)
  have hnn : (0:ℝ) ≤ min 1 (max 0 ((m : ℝ) * (ρ - t) - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  have hle1 : (0:ℝ) ≤ min 1 (max 0 ((n : ℝ) * t - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  show min 1 (max 0 ((m : ℝ) * t - 1)) * min 1 (max 0 ((m : ℝ) * (ρ - t) - 1))
      ≤ min 1 (max 0 ((n : ℝ) * t - 1)) * min 1 (max 0 ((n : ℝ) * (ρ - t) - 1))
  exact mul_le_mul h1 h2 hnn hle1

theorem tendsto_timeCut (ρ t : ℝ) :
    Tendsto (fun n : ℕ => timeCut n ρ t) atTop (𝓝 (Set.indicator (Set.Ioo 0 ρ) (fun _ => (1:ℝ)) t)) := by
  by_cases h : t ∈ Set.Ioo (0:ℝ) ρ
  · rw [Set.indicator_of_mem h]
    obtain ⟨ht0, htρ⟩ := h
    have hev : ∀ᶠ n : ℕ in atTop, timeCut n ρ t = 1 := by
      obtain ⟨N1, hN1⟩ := exists_nat_gt (2 / t)
      obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / (ρ - t))
      filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop N2] with n hn1 hn2
      refine timeCut_eq_one ?_ ?_
      · have : (2:ℝ) / t < (n : ℝ) := lt_of_lt_of_le hN1 (by exact_mod_cast hn1)
        rw [div_lt_iff₀ ht0] at this
        nlinarith
      · have hpos : (0:ℝ) < ρ - t := by linarith
        have : (2:ℝ) / (ρ - t) < (n : ℝ) := lt_of_lt_of_le hN2 (by exact_mod_cast hn2)
        rw [div_lt_iff₀ hpos] at this
        nlinarith
    exact Tendsto.congr' (by filter_upwards [hev] with n hn using hn.symm) tendsto_const_nhds
  · rw [Set.indicator_of_notMem h]
    have hz : ∀ n : ℕ, timeCut n ρ t = 0 := by
      intro n
      rcases le_or_gt t 0 with ht | ht
      · refine timeCut_eq_zero_of_small ?_
        have : (n : ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ht
        linarith
      · have hρt : ρ ≤ t := le_of_not_gt (fun hc => h ⟨ht, hc⟩)
        exact timeCut_eq_zero_of_ge hρt
    exact Tendsto.congr' (by filter_upwards with n using (hz n).symm) tendsto_const_nhds

theorem timeCut_mono_rho {ρ ρ' : ℝ} (h : ρ ≤ ρ') (n : ℕ) (t : ℝ) :
    timeCut n ρ t ≤ timeCut n ρ' t := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) ≤ min 1 (max 0 ((n : ℝ) * (ρ' - t) - 1)) := by
    refine min_le_min le_rfl (max_le_max le_rfl ?_)
    have : (n : ℝ) * (ρ - t) ≤ (n : ℝ) * (ρ' - t) :=
      mul_le_mul_of_nonneg_left (by linarith) hn
    linarith
  have hnn : (0:ℝ) ≤ min 1 (max 0 ((n : ℝ) * (ρ - t) - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  have hfirst : (0:ℝ) ≤ min 1 (max 0 ((n : ℝ) * t - 1)) :=
    le_min (by norm_num) (le_max_left _ _)
  show min 1 (max 0 ((n : ℝ) * t - 1)) * min 1 (max 0 ((n : ℝ) * (ρ - t) - 1))
      ≤ min 1 (max 0 ((n : ℝ) * t - 1)) * min 1 (max 0 ((n : ℝ) * (ρ' - t) - 1))
  exact mul_le_mul_of_nonneg_left h2 hfirst

/-- The weight of the time interval `(0, ρ)` at resolution `n`, with the interval
also shortened by `3/(n+1)` so that its support sits strictly inside the lattice
time range at every large scale. -/
noncomputable def lowerCut (n : ℕ) (ρ : ℝ) : ℝ → ℝ :=
  timeCut (n + 1) (ρ - 3 / ((n : ℝ) + 1))

theorem continuous_lowerCut (n : ℕ) (ρ : ℝ) : Continuous (lowerCut n ρ) :=
  continuous_timeCut _ _

theorem lowerCut_nonneg (n : ℕ) (ρ t : ℝ) : 0 ≤ lowerCut n ρ t := timeCut_nonneg _ _ _

theorem lowerCut_le_one (n : ℕ) (ρ t : ℝ) : lowerCut n ρ t ≤ 1 := timeCut_le_one _ _ _

theorem abs_lowerCut_le_one (n : ℕ) (ρ t : ℝ) : |lowerCut n ρ t| ≤ 1 := by
  rw [abs_of_nonneg (lowerCut_nonneg n ρ t)]
  exact lowerCut_le_one n ρ t

theorem lowerCut_eq_zero_of_lt {n : ℕ} {ρ t : ℝ} (h : t < 1 / ((n : ℝ) + 1)) :
    lowerCut n ρ t = 0 := by
  refine timeCut_eq_zero_of_small ?_
  have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have : ((n : ℕ) + 1 : ℕ) = ((n : ℝ) + 1) := by push_cast; ring
  rw [this]
  rw [lt_div_iff₀ hn] at h
  linarith

theorem lowerCut_eq_zero_of_ge {n : ℕ} {ρ t : ℝ} (h : ρ - 3 / ((n : ℝ) + 1) ≤ t) :
    lowerCut n ρ t = 0 := timeCut_eq_zero_of_ge h

theorem lowerCut_eq_one {n : ℕ} {ρ t : ℝ} (h1 : 2 / ((n : ℝ) + 1) ≤ t)
    (h2 : t ≤ ρ - 5 / ((n : ℝ) + 1)) : lowerCut n ρ t = 1 := by
  have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : (((n : ℕ) + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := by push_cast; ring
  refine timeCut_eq_one ?_ ?_
  · rw [hcast]
    rw [div_le_iff₀ hn] at h1
    linarith
  · rw [hcast]
    have h3 : 5 / ((n : ℝ) + 1) ≤ ρ - t := by linarith
    rw [div_le_iff₀ hn] at h3
    have h4 : 3 / ((n : ℝ) + 1) * ((n : ℝ) + 1) = 3 := by field_simp
    nlinarith [h3, h4]

theorem lowerCut_mono (ρ t : ℝ) : Monotone (fun n : ℕ => lowerCut n ρ t) := by
  intro m n hmn
  have hm : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hρ : ρ - 3 / ((m : ℝ) + 1) ≤ ρ - 3 / ((n : ℝ) + 1) := by
    have h1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have : 3 / ((n : ℝ) + 1) ≤ 3 / ((m : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) h1 (by linarith)
    linarith
  calc timeCut (m + 1) (ρ - 3 / ((m : ℝ) + 1)) t
      ≤ timeCut (m + 1) (ρ - 3 / ((n : ℝ) + 1)) t := timeCut_mono_rho hρ _ _
    _ ≤ timeCut (n + 1) (ρ - 3 / ((n : ℝ) + 1)) t :=
        timeCut_mono _ t (by omega)

theorem tendsto_lowerCut (ρ t : ℝ) :
    Tendsto (fun n : ℕ => lowerCut n ρ t) atTop
      (𝓝 (Set.indicator (Set.Ioo 0 ρ) (fun _ => (1:ℝ)) t)) := by
  by_cases h : t ∈ Set.Ioo (0:ℝ) ρ
  · rw [Set.indicator_of_mem h]
    obtain ⟨ht0, htρ⟩ := h
    have hev : ∀ᶠ n : ℕ in atTop, lowerCut n ρ t = 1 := by
      obtain ⟨N1, hN1⟩ := exists_nat_gt (2 / t)
      obtain ⟨N2, hN2⟩ := exists_nat_gt (5 / (ρ - t))
      filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop N2] with n hn1 hn2
      have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
      refine lowerCut_eq_one ?_ ?_
      · have hlt : (2:ℝ) / t < (n : ℝ) + 1 := by
          have : ((N1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          linarith
        rw [div_lt_iff₀ ht0] at hlt
        rw [div_le_iff₀ hn]
        linarith
      · have hpos : (0:ℝ) < ρ - t := by linarith
        have hlt : (5:ℝ) / (ρ - t) < (n : ℝ) + 1 := by
          have : ((N2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
          linarith
        rw [div_lt_iff₀ hpos] at hlt
        have : 5 / ((n : ℝ) + 1) ≤ ρ - t := by
          rw [div_le_iff₀ hn]
          linarith
        linarith
    exact Tendsto.congr' (by filter_upwards [hev] with n hn using hn.symm) tendsto_const_nhds
  · rw [Set.indicator_of_notMem h]
    have hz : ∀ n : ℕ, lowerCut n ρ t = 0 := by
      intro n
      have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
      rcases le_or_gt t 0 with ht | ht
      · refine lowerCut_eq_zero_of_lt ?_
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · have hρt : ρ ≤ t := le_of_not_gt (fun hc => h ⟨ht, hc⟩)
        refine lowerCut_eq_zero_of_ge ?_
        have : (0:ℝ) < 3 / ((n : ℝ) + 1) := by positivity
        linarith
    exact Tendsto.congr' (by filter_upwards with n using (hz n).symm) tendsto_const_nhds

end LatticeProb.TimeCut
