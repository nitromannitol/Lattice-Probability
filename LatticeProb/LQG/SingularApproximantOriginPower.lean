import LatticeProb.LQG.SingularApproximantCommonEvent

/-!
# Power bounds at the origin for singular approximants

The almost-sure bound `ae_exists_singular_approximant_uniform_dyadic_bound` controls
the approximants `lqgApprox γ (fieldCircleAverage α h) (2^{-k})` of the measure with a
logarithmic singularity `-α log |·|` on dyadic balls `ball 0 (2^{-J})`, uniformly in the
approximation level `k`, by the maximum of `A₀ 2^{-J}` and `A₁ q^{⌊J/n⌋}` with `q < 1`.

This file turns such dyadic geometric bounds into a power bound `A s^a` for every
radius `0 < s ≤ s₀`, uniformly over a family of measures, and records the resulting
almost-sure positive origin exponent of the singular approximants, with constants that
do not depend on the approximation level. A total-mass bound on a larger ball extends
any such power bound to all radii up to that ball.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- Every radius `0 < s ≤ 2^{-J₁}` lies in a dyadic bracket `2^{-(J+1)} < s ≤ 2^{-J}`
with `J₁ ≤ J`. -/
theorem exists_dyadicScale_bracket {J₁ : ℕ} {s : ℝ} (hs : 0 < s)
    (hsJ : s ≤ dyadicScale J₁) :
    ∃ J : ℕ, J₁ ≤ J ∧ dyadicScale (J + 1) < s ∧ s ≤ dyadicScale J := by
  have key : ∀ j : ℕ, dyadicScale (J₁ + j) * 2 ^ j = dyadicScale J₁ := by
    intro j
    unfold dyadicScale
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (x := dyadicScale J₁ / s) (y := (2 : ℝ))
    ((one_le_div hs).2 hsJ) (by norm_num)
  rw [le_div_iff₀ hs] at hm1
  rw [div_lt_iff₀ hs] at hm2
  refine ⟨J₁ + m, Nat.le_add_right _ _, ?_, ?_⟩
  · have h := key (m + 1)
    rw [← add_assoc] at h
    exact lt_of_mul_lt_mul_right (by rw [h, mul_comm s]; exact hm2) (by positivity)
  · have h := key m
    exact le_of_mul_le_mul_right (by rw [h, mul_comm s]; exact hm1) (by positivity)

/-- `exp (-(log 2) J) = 2^{-J}`. -/
theorem exp_neg_log_two_mul_eq_dyadicScale (J : ℕ) :
    Real.exp (-(Real.log 2) * J) = dyadicScale J := by
  unfold dyadicScale
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2⁻¹), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  ring

/-- **Dyadic geometric bounds give a power bound.** If, for every `J ≥ J₁`, each
measure of a family gives the ball `ball x (2^{-J})` mass at most
`max (A₀ 2^{-J}) (A₁ q^{⌊J/n⌋})` with `0 ≤ q < 1`, then there are `0 < a ≤ 1` and
`A ≥ 0`, not depending on the member of the family, such that every ball `ball x s`
with `0 < s ≤ 2^{-J₁}` has mass at most `A s^a`. -/
theorem exists_rpow_bound_of_dyadic_geometric_bound
    {ι E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E]
    (ν : ι → Measure E) (x : E) {A₀ A₁ q : ℝ} {n J₁ : ℕ}
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n)
    (h : ∀ i, ∀ J : ℕ, J₁ ≤ J → ν i (ball x (dyadicScale J)) ≤
      max (ENNReal.ofReal (A₀ * dyadicScale J)) (ENNReal.ofReal (A₁ * q ^ (J / n)))) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 ≤ A ∧ ∀ i, ∀ s : ℝ, 0 < s → s ≤ dyadicScale J₁ →
      ν i (ball x s) ≤ ENNReal.ofReal (A * s ^ a) := by
  set q' := max q (1 / 2) with hq'
  have hq'half : 1 / 2 ≤ q' := le_max_right _ _
  have hq'0 : 0 < q' := lt_of_lt_of_le (by norm_num) hq'half
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnL : 0 < (n : ℝ) * Real.log 2 := mul_pos (Nat.cast_pos.2 hn) hL
  have hlogq : Real.log q' < 0 := Real.log_neg hq'0 hq'1
  set a := min 1 (-Real.log q' / ((n : ℝ) * Real.log 2)) with ha
  have ha0 : 0 < a := lt_min one_pos (div_pos (neg_pos.2 hlogq) hnL)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haq : a * ((n : ℝ) * Real.log 2) ≤ -Real.log q' :=
    (le_div_iff₀ hnL).1 (min_le_right _ _)
  have hdpos : ∀ J : ℕ, 0 < dyadicScale J := fun J => pow_pos (by norm_num) J
  have hdy : ∀ J : ℕ, dyadicScale J ^ a = Real.exp (-(a * Real.log 2 * J)) := by
    intro J
    rw [Real.rpow_def_of_pos (hdpos J)]
    congr 1
    unfold dyadicScale
    rw [Real.log_pow, Real.log_inv]
    ring
  set B := max A₀ (2 * A₁) with hB
  have hB0 : 0 ≤ B := le_trans hA₀ (le_max_left _ _)
  have hfirst : ∀ J : ℕ, A₀ * dyadicScale J ≤ B * dyadicScale J ^ a := by
    intro J
    have hle1 : dyadicScale J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h1 : dyadicScale J ≤ dyadicScale J ^ a := by
      have := Real.rpow_le_rpow_of_exponent_ge (hdpos J) hle1 ha1
      rwa [Real.rpow_one] at this
    exact mul_le_mul (le_max_left _ _) h1 (hdpos J).le hB0
  have hsecond : ∀ J : ℕ, A₁ * q ^ (J / n) ≤ B * dyadicScale J ^ a := by
    intro J
    have hmJ : (J : ℝ) ≤ (n : ℝ) * (((J / n : ℕ) : ℝ) + 1) := by
      have := (Nat.lt_mul_div_succ J hn).le
      exact_mod_cast this
    have e1 : (((J / n : ℕ) : ℝ) + 1) * Real.log q' ≤
        (((J / n : ℕ) : ℝ) + 1) * (-(a * ((n : ℝ) * Real.log 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : a * Real.log 2 * (J : ℝ) ≤
        a * Real.log 2 * ((n : ℝ) * (((J / n : ℕ) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hmJ (by positivity)
    have hpow : q' ^ (J / n + 1) ≤ dyadicScale J ^ a := by
      rw [hdy J]
      calc q' ^ (J / n + 1) = Real.exp (Real.log q') ^ (J / n + 1) := by
            rw [Real.exp_log hq'0]
        _ = Real.exp (((J / n + 1 : ℕ) : ℝ) * Real.log q') := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (-(a * Real.log 2 * J)) :=
            Real.exp_le_exp.2 (by push_cast; linarith)
    have hqq : q ^ (J / n) ≤ q' ^ (J / n) := pow_le_pow_left₀ hq0 (le_max_left _ _) _
    have hstep : q' ^ (J / n) ≤ 2 * q' ^ (J / n + 1) := by
      have hnn := pow_nonneg hq'0.le (J / n)
      rw [pow_succ]
      nlinarith
    calc A₁ * q ^ (J / n) ≤ A₁ * (2 * dyadicScale J ^ a) :=
          mul_le_mul_of_nonneg_left (hqq.trans (hstep.trans (by linarith))) hA₁
      _ = 2 * A₁ * dyadicScale J ^ a := by ring
      _ ≤ B * dyadicScale J ^ a :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (hdpos J).le _)
  refine ⟨a, 2 * B, ha0, ha1, by positivity, ?_⟩
  intro i s hs hsJ
  obtain ⟨J, hJ₁, hlt, hle⟩ := exists_dyadicScale_bracket hs hsJ
  have hdouble : dyadicScale J = 2 * dyadicScale (J + 1) := by
    unfold dyadicScale
    ring
  have h2s : dyadicScale J ^ a ≤ 2 * s ^ a := by
    calc dyadicScale J ^ a ≤ (2 * s) ^ a :=
          Real.rpow_le_rpow (hdpos J).le (by linarith) ha0.le
      _ = 2 ^ a * s ^ a := Real.mul_rpow (by norm_num) hs.le
      _ ≤ 2 * s ^ a := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
          rwa [Real.rpow_one] at this
  calc ν i (ball x s) ≤ ν i (ball x (dyadicScale J)) := measure_mono (ball_subset_ball hle)
    _ ≤ max (ENNReal.ofReal (A₀ * dyadicScale J)) (ENNReal.ofReal (A₁ * q ^ (J / n))) :=
        h i J hJ₁
    _ ≤ ENNReal.ofReal (B * dyadicScale J ^ a) :=
        max_le (ENNReal.ofReal_le_ofReal (hfirst J)) (ENNReal.ofReal_le_ofReal (hsecond J))
    _ ≤ ENNReal.ofReal (2 * B * s ^ a) := by
        apply ENNReal.ofReal_le_ofReal
        calc B * dyadicScale J ^ a ≤ B * (2 * s ^ a) := mul_le_mul_of_nonneg_left h2s hB0
          _ = 2 * B * s ^ a := by ring

/-- A power bound for small radii and a bound on the mass of a larger ball give a power
bound, with the same exponent, up to the radius of the larger ball. -/
theorem rpow_bound_extend_of_ball_mass_le
    {ι E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E]
    (ν : ι → Measure E) (x : E) {a A M s₀ L : ℝ} (ha : 0 ≤ a)
    (hM : 0 ≤ M) (hs₀ : 0 < s₀)
    (hsmall : ∀ i, ∀ s : ℝ, 0 < s → s ≤ s₀ → ν i (ball x s) ≤ ENNReal.ofReal (A * s ^ a))
    (hmass : ∀ i, ν i (ball x L) ≤ ENNReal.ofReal M) :
    ∀ i, ∀ s : ℝ, 0 < s → s ≤ L →
      ν i (ball x s) ≤ ENNReal.ofReal (max A (M / s₀ ^ a) * s ^ a) := by
  intro i s hs hsL
  have hspow : 0 ≤ s ^ a := Real.rpow_nonneg hs.le _
  by_cases hss : s ≤ s₀
  · exact (hsmall i s hs hss).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hspow))
  · have hlt : s₀ < s := lt_of_not_ge hss
    have hs₀a : 0 < s₀ ^ a := Real.rpow_pos_of_pos hs₀ _
    calc ν i (ball x s) ≤ ν i (ball x L) := measure_mono (ball_subset_ball hsL)
      _ ≤ ENNReal.ofReal M := hmass i
      _ ≤ ENNReal.ofReal (max A (M / s₀ ^ a) * s ^ a) := by
          apply ENNReal.ofReal_le_ofReal
          calc M = M / s₀ ^ a * s₀ ^ a := by field_simp
            _ ≤ M / s₀ ^ a * s ^ a :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs₀.le hlt.le ha)
                  (div_nonneg hM hs₀a.le)
            _ ≤ max A (M / s₀ ^ a) * s ^ a :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hspow

/-- **Positive origin exponent of the singular approximants.** On a common event, the
approximants of the measure with logarithmic singularity `-α log |·|`, `α < Q`, give the
balls `ball 0 s`, `0 < s ≤ s₀`, mass at most `A s^a`, with `a > 0`, `A` and `s₀`
depending on the sample but not on the approximation level. -/
theorem ae_exists_singular_approximant_origin_rpow_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ a A s₀ : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 ≤ A ∧ 0 < s₀ ∧
      ∀ k : ℕ, ∀ s : ℝ, 0 < s → s ≤ s₀ →
        lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k) (ball 0 s) ≤
          ENNReal.ofReal (A * s ^ a) := by
  filter_upwards [ae_exists_singular_approximant_uniform_dyadic_bound hX hG hc heq hγ hγ2
    hαQ hδ hρ hrρ] with ω hω
  obtain ⟨C, _hC, n, hn, J₀, hbound⟩ := hω
  set q := Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) with hq
  have hpos : 0 < γ * (lqgQ γ - α) * Real.log 2 / 2 :=
    div_pos (mul_pos (mul_pos hγ (sub_pos.2 hαQ)) (Real.log_pos one_lt_two)) two_pos
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos hpos)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  obtain ⟨Jr, hJr⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
  set J₁ := max (J₀ * n) Jr with hJ₁
  have hgeom : ∀ k : ℕ, ∀ J : ℕ, J₁ ≤ J →
      lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        max (ENNReal.ofReal (Real.pi * Real.exp (γ * C) * dyadicScale J))
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) / (1 - q) * q ^ (J / n))) := by
    intro k J hJ
    have hJr' : dyadicScale J ≤ r := by
      have hmono : dyadicScale J ≤ dyadicScale Jr :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_trans (le_max_right _ _) hJ)
      exact hmono.trans (le_of_lt (by simpa [dyadicScale] using hJr))
    have hJ₀ : J₀ ≤ J / n := (Nat.le_div_iff_mul_le hn).2 (le_trans (le_max_left _ _) hJ)
    have := hbound J k hJr' hJ₀
    rw [exp_neg_log_two_mul_eq_dyadicScale] at this
    convert this using 3
    ring
  obtain ⟨a, A, ha0, ha1, hA, hpow⟩ :=
    exists_rpow_bound_of_dyadic_geometric_bound
      (fun k : ℕ => lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k)) (0 : ℂ)
      (A₀ := Real.pi * Real.exp (γ * C))
      (A₁ := Real.exp (γ * (|α| * Real.log 2)) / (1 - q)) (by positivity)
      (div_nonneg (Real.exp_pos _).le (by linarith)) hq0 hq1 hn hgeom
  exact ⟨a, A, dyadicScale J₁, ha0, ha1, hA, pow_pos (by norm_num) _,
    fun k s hs hsJ => hpow k s hs hsJ⟩

end LatticeProb.LQG
