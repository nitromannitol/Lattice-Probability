import LatticeProb.Gauss.CircleAverageShellSum

/-!
# Summable one-point tails of circle averages along geometric radii

For a whole-plane Gaussian free field `h`, a scale `s > 0`, a rate `ρ > 0`, centres `c k` with
`‖c k‖ ≤ M s e^{-ρ k}` and the circle averages `h_{s e^{-ρ k}}(c k)`, the probabilities
`P{-η k < ξ (h_{s e^{-ρ k}}(c k) + A log (s e^{-ρ k}))}` are summable in `k` as soon as `ξ > 0` and
`η < ξ A ρ`.  Indeed the event forces `h_{s e^{-ρ k}}(c k) ≥ b k - A log s` with `b = A ρ - η / ξ > 0`,
while `Var (h_{s e^{-ρ k}}(c k) - h_1(0)) ≤ ρ k + const`, so the Gaussian tail gives
`≲ exp (-(b² / (2 ρ)) k)`.  The dyadic radii `s / 2ᵏ` are the case `ρ = log 2`
(`LatticeProb.Gauss.IsWholePlaneGFF.tsum_measure_shell_circle_exp_ne_top`); the case `ρ = 1` gives the
radii `s e^{-k}` of the exponential shells `{e^{-(k+1)} ≤ |x| ≤ e^{-k}}`.

* `LatticeProb.Gauss.IsWholePlaneGFF.tsum_measure_geometric_circle_exp_ne_top`: the summable tail.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Summable one-point tails along geometrically shrinking circles.** Let `h` be a whole-plane
Gaussian free field, `s > 0`, `ρ > 0`, `ξ > 0`, `A, η, M ∈ ℝ` with `η < ξ A ρ`, and `c k ∈ ℂ` with
`‖c k‖ ≤ M s e^{-ρ k}`.  Then `∑ₖ P{-η k < ξ (h_{s e^{-ρ k}}(c k) + A log (s e^{-ρ k}))} < ∞`. -/
theorem tsum_measure_geometric_circle_exp_ne_top (hh : IsWholePlaneGFF P hC hcirc)
    {s ρ ξ A η M : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hξ : 0 < ξ) (hη : η < ξ * A * ρ) {c : ℕ → ℂ}
    (hc : ∀ k : ℕ, ‖c k‖ ≤ M * (s * Real.exp (-(ρ * k)))) :
    ∑' k : ℕ, P {ω | -η * k < ξ * (hcirc ω (s * Real.exp (-(ρ * k))) (c k) +
      A * Real.log (s * Real.exp (-(ρ * k))))} ≠ ⊤ := by
  have hP := hh.isProbabilityMeasure
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = A * ρ - η / ξ := ⟨_, rfl⟩
  have hbpos : 0 < b := by
    have : η / ξ < A * ρ := by rw [div_lt_iff₀ hξ]; linarith
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |M| * s := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * Real.log (1 + R) - Real.log s := ⟨_, rfl⟩
  obtain ⟨κ, hκ, n₀, hn₀⟩ :=
    exists_pos_eventually_quadratic_of_pos (K := A * Real.log s) (L := L) hρ hbpos
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₀ ≤ n₁ ∧ s ≤ ρ * n₁ := by
    refine ⟨max n₀ ⌈s / ρ⌉₊, le_max_left _ _, ?_⟩
    have h1 : s / ρ ≤ ((max n₀ ⌈s / ρ⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))
    rw [div_le_iff₀ hρ] at h1
    linarith
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = 2 + Real.exp (κ * n₁) := ⟨_, rfl⟩
  have hM2 : 2 ≤ M' := by rw [hM']; linarith [Real.exp_pos (κ * n₁)]
  have hbound : ∀ k : ℕ, P {ω | -η * k < ξ * (hcirc ω (s * Real.exp (-(ρ * k))) (c k) +
      A * Real.log (s * Real.exp (-(ρ * k))))} ≤ ENNReal.ofReal (M' * Real.exp (-(κ * k))) := by
    intro k
    by_cases hk : k < n₁
    · -- small levels: the probability is at most one
      refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hkr : (k : ℝ) ≤ n₁ := Nat.cast_le.2 hk.le
      have hexp : Real.exp (κ * k) ≤ Real.exp (κ * n₁) :=
        Real.exp_le_exp.2 (by nlinarith)
      have hmul : Real.exp (κ * k) * Real.exp (-(κ * k)) = 1 := by
        rw [← Real.exp_add]; simp
      have hle : Real.exp (κ * k) ≤ M' := by rw [hM']; linarith
      calc (1 : ℝ) = Real.exp (κ * k) * Real.exp (-(κ * k)) := hmul.symm
        _ ≤ M' * Real.exp (-(κ * k)) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    · -- large levels: Gaussian tail
      have hk' : n₁ ≤ k := not_lt.1 hk
      obtain ⟨hV, hapos, hq⟩ := hn₀ k (hn₁.1.trans hk')
      set r := s * Real.exp (-(ρ * k)) with hr
      have hr0 : 0 < r := mul_pos hs (Real.exp_pos _)
      have hsk : s ≤ ρ * k := hn₁.2.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hk') hρ.le)
      have hr1 : r ≤ 1 := by
        rw [hr, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        linarith [Real.add_one_le_exp (ρ * k)]
      have hexp1 : Real.exp (-(ρ * k)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
      have hzn : ‖c k‖ ≤ R * 1 := by
        refine (hc k).trans ?_
        rw [mul_one, hR]
        calc M * r ≤ |M| * r := mul_le_mul_of_nonneg_right (le_abs_self M) hr0.le
          _ ≤ |M| * s :=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hs.le hexp1) (abs_nonneg M)
      have hvar := hh.variance_circle_sub_start_le hr0 hr1 one_pos hR0 hzn
      rw [mul_one] at hvar
      have hlog : Real.log r = Real.log s - ρ * k := by
        rw [hr, Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
      have hlogr : -Real.log r + 2 * Real.log (1 + R) = ρ * k + L := by
        rw [hlog, hL]; ring
      rw [hlogr] at hvar
      have htail := hh.measure_circle_sub_ge_le hr0 one_pos (c k) 0 hV hvar hapos
      have hone := hh.ae_circleAverage_one_zero
      have hincl : {ω | -η * k < ξ * (hcirc ω r (c k) + A * Real.log r)} ⊆
          {ω | b * k - A * Real.log s ≤ hcirc ω r (c k)} := by
        intro ω hω
        simp only [mem_ofPred_eq] at hω ⊢
        rw [hlog] at hω
        have e : ξ * (b * k - A * Real.log s) =
            ξ * A * ρ * k - η * k - ξ * A * Real.log s := by
          have hξη : ξ * (η / ξ) = η := by field_simp
          rw [hb]
          linear_combination (-(k : ℝ)) * hξη
        refine le_of_lt (lt_of_mul_lt_mul_left ?_ hξ.le)
        rw [e]
        linarith
      have hsub : {ω | b * k - A * Real.log s ≤ hcirc ω r (c k)} ≤ᵐ[P]
          {ω | b * k - A * Real.log s ≤ |hcirc ω r (c k) - hcirc ω 1 0|} :=
        hone.mono fun ω h0 hω => by
          simp only [mem_ofPred_eq] at hω ⊢
          rw [h0, sub_zero]
          exact hω.trans (le_abs_self _)
      refine (measure_mono hincl).trans ((measure_mono_ae hsub).trans (htail.trans ?_))
      refine ENNReal.ofReal_le_ofReal ?_
      have hq' : κ * k ≤ (b * k - A * Real.log s) ^ 2 / (2 * (ρ * k + L)) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [hq]
      exact mul_le_mul hM2 (Real.exp_le_exp.2 (neg_le_neg hq')) (Real.exp_pos _).le (by linarith)
  -- summability
  have hterm : ∀ k : ℕ, ENNReal.ofReal (M' * Real.exp (-(κ * k))) =
      ENNReal.ofReal (M' * (Real.exp (-κ)) ^ k) := fun k => by
    congr 1
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hsum : Summable fun k : ℕ => M' * (Real.exp (-κ)) ^ k :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left M'
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end IsWholePlaneGFF

end LatticeProb.Gauss
