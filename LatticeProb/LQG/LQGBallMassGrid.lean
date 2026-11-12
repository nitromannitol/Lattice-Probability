import Mathlib
import LatticeProb.LQG.LQGMeasureInputs

/-!
# Uniform bounds on the LQG mass of small balls from single-ball tail estimates

The uniform estimate of Ding and Gwynne (arXiv:1807.01072, Lemma 3.8): with polynomially high probability as
`ε → 0`, every ball of radius `ε^{β_lower}` centred in the unit square has mass at least `ε` and every ball of
radius `ε^{β_upper}` centred there has mass at most `ε`, whenever `β_lower < 2/(2+γ)²` and `β_upper > 2/(2-γ)²`.
This file proves the deterministic part of the argument: a covering of the unit square by `O(r⁻²)` balls of
comparable radius and a union bound reduce the uniform estimate to single-ball tail estimates whose failure
probability decays faster than `r²`.

Write `a_± = (2 ± γ)²/2`. The single-ball estimates are:

* upper tail: for every `b < a_-` there is `θ > 2` with `P[μ(B_r(z)) > r^b] ≤ C r^θ` for `z` in the unit square and
  small `r`;
* lower tail: for every `c > a_+` there is `θ > 2` with `P[μ(B_r(z)) < r^c] ≤ C r^θ`.

They follow from the positive moments of order `2/γ` and the negative moments of the mass of a unit ball and the
exact scaling of the whole-plane Gaussian free field; they are not proved here. Probabilities of events that need
not be measurable are outer measures, as in `PolyHighProb`.

## Main results

* `exists_unitSquare_grid`: a finite set of `(1/δ + 1)²` points of the unit square at distance `< 2δ` from every
  point of the square.
* `polyHighProb_ballMass_upper`, `polyHighProb_ballMass_lower`: the two halves of the uniform estimate.
* `polyHighProb_ballMass_of_single`: the uniform estimate in the form of `WholePlaneLQGBallMassBoundsLP`.
* `wholePlaneLQGBallMassBoundsLP_of_single`: the literature statement `WholePlaneLQGBallMassBoundsLP` from the
  single-ball estimates for every γ-LQG measure of the whole-plane Gaussian free field.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

/-- Single-ball upper tail of a random measure on `ℂ` at the exponents of the γ-LQG measure: for every
`b < (2 - γ)²/2` the probability that a ball of radius `r` centred in the unit square has mass larger than `r^b`
is at most `C r^θ` for some `θ > 2`, uniformly in the centre, for small `r`. -/
def BallMassUpperTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (μ : Ω → Measure ℂ) : Prop :=
  ∀ b : ℝ, b < (2 - γ) ^ 2 / 2 → ∃ θ : ℝ, 2 < θ ∧ ∃ C r₀ : ℝ, 0 < r₀ ∧
    ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ r : ℝ, 0 < r → r < r₀ →
      P {ω | ENNReal.ofReal (r ^ b) < μ ω (ball z r)} ≤ ENNReal.ofReal (C * r ^ θ)

/-- Single-ball lower tail of a random measure on `ℂ` at the exponents of the γ-LQG measure: for every
`c > (2 + γ)²/2` the probability that a ball of radius `r` centred in the unit square has mass smaller than `r^c`
is at most `C r^θ` for some `θ > 2`, uniformly in the centre, for small `r`. -/
def BallMassLowerTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (μ : Ω → Measure ℂ) : Prop :=
  ∀ c : ℝ, (2 + γ) ^ 2 / 2 < c → ∃ θ : ℝ, 2 < θ ∧ ∃ C r₀ : ℝ, 0 < r₀ ∧
    ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ r : ℝ, 0 < r → r < r₀ →
      P {ω | μ ω (ball z r) < ENNReal.ofReal (r ^ c)} ≤ ENNReal.ofReal (C * r ^ θ)

/-- A grid of mesh `δ` in the unit square: at most `(1/δ + 1)²` points of the square, every point of the square
at distance less than `2δ` from one of them. -/
theorem exists_unitSquare_grid {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : Finset ℂ, (G.card : ℝ) ≤ (1 / δ + 1) ^ 2 ∧ (∀ w ∈ G, w ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) ∧
      ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∃ w ∈ G, dist z w < 2 * δ := by
  set n : ℕ := ⌊1 / δ⌋₊ with hn
  let g : ℕ × ℕ → ℂ := fun p => ⟨p.1 * δ, p.2 * δ⟩
  refine ⟨(Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image g, ?_, ?_, ?_⟩
  · have hcard := Finset.card_image_le (s := Finset.range (n + 1) ×ˢ Finset.range (n + 1)) (f := g)
    rw [Finset.card_product, Finset.card_range] at hcard
    have hn1 : ((n : ℝ) + 1) ≤ 1 / δ + 1 := by
      have := Nat.floor_le (a := 1 / δ) (by positivity)
      linarith
    calc ((Finset.image g _).card : ℝ) ≤ ((n + 1) * (n + 1) : ℕ) := by exact_mod_cast hcard
      _ = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ (1 / δ + 1) ^ 2 := by gcongr
  · intro w hw
    obtain ⟨⟨i, k⟩, hik, rfl⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hik
    have hle : ∀ j : ℕ, j < n + 1 → (j : ℝ) * δ ≤ 1 := by
      intro j hj
      have hj' : (j : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hj
      have := Nat.floor_le (a := 1 / δ) (by positivity)
      calc (j : ℝ) * δ ≤ (1 / δ) * δ := by gcongr; linarith
        _ = 1 := by field_simp
    rw [Complex.mem_reProdIm]
    exact ⟨⟨by positivity, hle i hik.1⟩, ⟨by positivity, hle k hik.2⟩⟩
  · intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
    have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ⌊x / δ⌋₊ < n + 1 ∧ 0 ≤ x - ⌊x / δ⌋₊ * δ ∧
        x - ⌊x / δ⌋₊ * δ < δ := by
      intro x hx0 hx1
      refine ⟨Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right hx1 hδ.le)), ?_, ?_⟩
      · have := Nat.floor_le (div_nonneg hx0 hδ.le)
        have h2 : (⌊x / δ⌋₊ : ℝ) * δ ≤ x / δ * δ := by gcongr
        rw [div_mul_cancel₀ x hδ.ne'] at h2
        linarith
      · have := Nat.lt_floor_add_one (x / δ)
        have h2 : x / δ * δ < ((⌊x / δ⌋₊ : ℝ) + 1) * δ := by gcongr
        rw [div_mul_cancel₀ x hδ.ne'] at h2
        linarith
    obtain ⟨hi, hi0, hi1⟩ := key z.re hx0 hx1
    obtain ⟨hk, hk0, hk1⟩ := key z.im hy0 hy1
    refine ⟨g (⌊z.re / δ⌋₊, ⌊z.im / δ⌋₊), Finset.mem_image_of_mem _ ?_, ?_⟩
    · exact Finset.mem_product.2 ⟨Finset.mem_range.2 hi, Finset.mem_range.2 hk⟩
    · rw [dist_eq_norm]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [g, Complex.sub_re, Complex.sub_im]
      rw [abs_of_nonneg hi0, abs_of_nonneg hk0]
      linarith

/-- A property that holds eventually as `ε → 0+` holds on an interval `(0, r₀)`. -/
theorem exists_pos_forall_of_eventually_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), p ε) :
    ∃ r₀ > 0, ∀ ε : ℝ, 0 < ε → ε < r₀ → p ε := by
  rcases Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h) with ⟨r₀, hr₀, H⟩
  refine ⟨r₀, hr₀, fun ε hε hεr => H ?_ hε⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hε]
  exact hεr

/-- `ε^a → 0` as `ε → 0+` for `a > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_rpow_const ha.le).tendsto (0 : ℝ)
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The upper half of the uniform estimate: if the single-ball upper tail holds, then with polynomially high
probability every ball of radius `ε^{β_upper}` centred in the unit square has mass at most `ε`, for
`β_upper > 2/(2-γ)²`. Cover the square by `O(r⁻²)` balls of radius `2r`, `r = ε^{β_upper}`. -/
theorem polyHighProb_ballMass_upper {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {μ : Ω → Measure ℂ} (hup : BallMassUpperTail P γ μ) (hγ2 : γ < 2) {βu : ℝ}
    (hβu : 2 / (2 - γ) ^ 2 < βu) :
    PolyHighProb P fun ε => {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      μ ω (ball z (ε ^ βu)) ≤ ENNReal.ofReal ε} := by
  have hs : 0 < (2 - γ) ^ 2 := pow_pos (sub_pos.2 hγ2) 2
  have hβu0 : 0 < βu := lt_of_le_of_lt (by positivity) hβu
  have hinv : 1 / βu < (2 - γ) ^ 2 / 2 := by
    rw [div_lt_iff₀ hs] at hβu
    rw [div_lt_div_iff₀ hβu0 two_pos]
    nlinarith
  set b : ℝ := (1 / βu + (2 - γ) ^ 2 / 2) / 2 with hb
  have hb1 : 1 / βu < b := by rw [hb]; linarith
  have hb2 : b < (2 - γ) ^ 2 / 2 := by rw [hb]; linarith
  have hbβ : 1 < βu * b := by
    rw [div_lt_iff₀ hβu0] at hb1
    linarith [mul_comm b βu]
  obtain ⟨θ, hθ, C, r₀, hr₀, hC⟩ := hup b hb2
  obtain ⟨C', hC'0, hCC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  have ev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    (gt_mem_nhds one_pos).filter_mono nhdsWithin_le_nhds
  have ev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ^ βu < r₀ := by
    have h := (tendsto_rpow_nhdsGT_zero hβu0).const_mul 2
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds hr₀)
  have ev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 ^ b * ε ^ (βu * b - 1) ≤ 1 := by
    have h := (tendsto_rpow_nhdsGT_zero (sub_pos.2 hbβ)).const_mul ((2 : ℝ) ^ b)
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds one_pos)).mono fun _ h => h.le
  obtain ⟨ε₀, hε₀, hev⟩ := exists_pos_forall_of_eventually_nhdsGT ((ev1.and ev2).and ev3)
  refine ⟨βu * (θ - 2), mul_pos hβu0 (by linarith), 9 * 2 ^ θ * C', ε₀, hε₀, ?_⟩
  intro ε hε hεε₀
  obtain ⟨⟨hε1, hr0'⟩, hcond⟩ := hev ε hε hεε₀
  have hrpos : 0 < ε ^ βu := Real.rpow_pos_of_pos hε _
  have hr1 : ε ^ βu ≤ 1 := Real.rpow_le_one hε.le hε1.le hβu0.le
  set r := ε ^ βu with hr
  obtain ⟨G, hGcard, hGsq, hGcov⟩ := exists_unitSquare_grid (half_pos hrpos)
  have hrb : (2 * r) ^ b ≤ ε := by
    have hsplit : ε ^ (βu * b) = ε ^ (βu * b - 1) * ε := by
      rw [← Real.rpow_add_one hε.ne', sub_add_cancel]
    rw [Real.mul_rpow two_pos.le hrpos.le, hr, ← Real.rpow_mul hε.le, hsplit, ← mul_assoc]
    calc 2 ^ b * ε ^ (βu * b - 1) * ε ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
  have hsub : {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ ω (ball z r) ≤ ENNReal.ofReal ε}ᶜ ⊆
      ⋃ w ∈ G, {ω | ENNReal.ofReal ((2 * r) ^ b) < μ ω (ball w (2 * r))} := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le, exists_prop] at hω
    obtain ⟨z, hz, hlt⟩ := hω
    obtain ⟨w, hwG, hzw⟩ := hGcov z hz
    refine mem_iUnion₂.2 ⟨w, hwG, ?_⟩
    have hball : ball z r ⊆ ball w (2 * r) := by
      intro y hy
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle y z w]
    calc ENNReal.ofReal ((2 * r) ^ b) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hrb
      _ < μ ω (ball z r) := hlt
      _ ≤ μ ω (ball w (2 * r)) := measure_mono hball
  have hterm : ∀ w ∈ G, P {ω | ENNReal.ofReal ((2 * r) ^ b) < μ ω (ball w (2 * r))} ≤
      ENNReal.ofReal (C' * (2 * r) ^ θ) := by
    intro w hw
    refine (hC w (hGsq w hw) (2 * r) (by positivity) hr0').trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hCC' (by positivity)
  have hcard : (G.card : ℝ) ≤ 9 / r ^ 2 := by
    refine hGcard.trans ?_
    have h1 : 1 ≤ 1 / r := by rw [le_div_iff₀ hrpos]; linarith
    have h3 : 1 / (r / 2) + 1 ≤ 3 / r := by
      rw [one_div_div]
      calc 2 / r + 1 ≤ 2 / r + 1 / r := by linarith
        _ = 3 / r := by ring
    calc (1 / (r / 2) + 1) ^ 2 ≤ (3 / r) ^ 2 := by gcongr
      _ = 9 / r ^ 2 := by ring
  have hpow : ε ^ (βu * (θ - 2)) = r ^ θ / r ^ 2 := by
    rw [Real.rpow_mul hε.le, ← hr, Real.rpow_sub hrpos, Real.rpow_two]
  refine le_trans (measure_mono hsub) ?_
  refine (measure_biUnion_finset_le G _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hpow, Real.mul_rpow two_pos.le hrpos.le]
  calc (G.card : ℝ) * (C' * (2 ^ θ * r ^ θ)) ≤ 9 / r ^ 2 * (C' * (2 ^ θ * r ^ θ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 9 * 2 ^ θ * C' * (r ^ θ / r ^ 2) := by ring

/-- The lower half of the uniform estimate: if the single-ball lower tail holds, then with polynomially high
probability every ball of radius `ε^{β_lower}` centred in the unit square has mass at least `ε`, for
`0 < β_lower < 2/(2+γ)²`. Each such ball contains a ball of radius `r/2` about a grid point, `r = ε^{β_lower}`. -/
theorem polyHighProb_ballMass_lower {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {μ : Ω → Measure ℂ} (hlow : BallMassLowerTail P γ μ) (hγ0 : 0 ≤ γ) {βl : ℝ} (hβl0 : 0 < βl)
    (hβl : βl < 2 / (2 + γ) ^ 2) :
    PolyHighProb P fun ε => {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ βl))} := by
  have hs : 0 < (2 + γ) ^ 2 := by positivity
  have hinv : (2 + γ) ^ 2 / 2 < 1 / βl := by
    rw [lt_div_iff₀ hs] at hβl
    rw [div_lt_div_iff₀ two_pos hβl0]
    nlinarith
  set c : ℝ := (1 / βl + (2 + γ) ^ 2 / 2) / 2 with hc
  have hc1 : (2 + γ) ^ 2 / 2 < c := by rw [hc]; linarith
  have hc2 : c < 1 / βl := by rw [hc]; linarith
  have hc0 : 0 < c := lt_trans (by positivity) hc1
  have hcβ : βl * c < 1 := by
    rw [lt_div_iff₀ hβl0] at hc2
    linarith [mul_comm c βl]
  obtain ⟨θ, hθ, C, r₀, hr₀, hC⟩ := hlow c hc1
  obtain ⟨C', hC'0, hCC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  have ev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    (gt_mem_nhds one_pos).filter_mono nhdsWithin_le_nhds
  have ev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ βl < r₀ :=
    (tendsto_rpow_nhdsGT_zero hβl0).eventually (gt_mem_nhds hr₀)
  have ev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 ^ c * ε ^ (1 - βl * c) ≤ 1 := by
    have h := (tendsto_rpow_nhdsGT_zero (sub_pos.2 hcβ)).const_mul ((2 : ℝ) ^ c)
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds one_pos)).mono fun _ h => h.le
  obtain ⟨ε₀, hε₀, hev⟩ := exists_pos_forall_of_eventually_nhdsGT ((ev1.and ev2).and ev3)
  refine ⟨βl * (θ - 2), mul_pos hβl0 (by linarith), 25 * C', ε₀, hε₀, ?_⟩
  intro ε hε hεε₀
  obtain ⟨⟨hε1, hr0'⟩, hcond⟩ := hev ε hε hεε₀
  have hrpos : 0 < ε ^ βl := Real.rpow_pos_of_pos hε _
  have hr1 : ε ^ βl ≤ 1 := Real.rpow_le_one hε.le hε1.le hβl0.le
  set r := ε ^ βl with hr
  have hr4 : 0 < r / 4 := by positivity
  obtain ⟨G, hGcard, hGsq, hGcov⟩ := exists_unitSquare_grid hr4
  have hrc : ε ≤ (r / 2) ^ c := by
    have hsplit : ε = ε ^ (1 - βl * c) * ε ^ (βl * c) := by
      rw [← Real.rpow_add hε, sub_add_cancel, Real.rpow_one]
    have h2c : (0 : ℝ) < 2 ^ c := by positivity
    rw [Real.div_rpow hrpos.le two_pos.le, le_div_iff₀ h2c, hr, ← Real.rpow_mul hε.le]
    calc ε * 2 ^ c = 2 ^ c * ε ^ (1 - βl * c) * ε ^ (βl * c) := by
          conv_lhs => rw [hsplit]
          ring
      _ ≤ 1 * ε ^ (βl * c) := by gcongr
      _ = ε ^ (βl * c) := one_mul _
  have hsub : {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ENNReal.ofReal ε ≤ μ ω (ball z r)}ᶜ ⊆
      ⋃ w ∈ G, {ω | μ ω (ball w (r / 2)) < ENNReal.ofReal ((r / 2) ^ c)} := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le, exists_prop] at hω
    obtain ⟨z, hz, hlt⟩ := hω
    obtain ⟨w, hwG, hzw⟩ := hGcov z hz
    refine mem_iUnion₂.2 ⟨w, hwG, ?_⟩
    have hball : ball w (r / 2) ⊆ ball z r := by
      intro y hy
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle y w z, dist_comm z w]
    calc μ ω (ball w (r / 2)) ≤ μ ω (ball z r) := measure_mono hball
      _ < ENNReal.ofReal ε := hlt
      _ ≤ ENNReal.ofReal ((r / 2) ^ c) := ENNReal.ofReal_le_ofReal hrc
  have hterm : ∀ w ∈ G, P {ω | μ ω (ball w (r / 2)) < ENNReal.ofReal ((r / 2) ^ c)} ≤
      ENNReal.ofReal (C' * r ^ θ) := by
    intro w hw
    refine (hC w (hGsq w hw) (r / 2) (by positivity) (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
    calc C * (r / 2) ^ θ ≤ C' * (r / 2) ^ θ := mul_le_mul_of_nonneg_right hCC' (by positivity)
      _ ≤ C' * r ^ θ := by
        gcongr
        linarith
  have hcard : (G.card : ℝ) ≤ 25 / r ^ 2 := by
    refine hGcard.trans ?_
    have h1 : 1 ≤ 1 / r := by rw [le_div_iff₀ hrpos]; linarith
    have h3 : 1 / (r / 4) + 1 ≤ 5 / r := by
      rw [one_div_div]
      calc 4 / r + 1 ≤ 4 / r + 1 / r := by linarith
        _ = 5 / r := by ring
    calc (1 / (r / 4) + 1) ^ 2 ≤ (5 / r) ^ 2 := by gcongr
      _ = 25 / r ^ 2 := by ring
  have hpow : ε ^ (βl * (θ - 2)) = r ^ θ / r ^ 2 := by
    rw [Real.rpow_mul hε.le, ← hr, Real.rpow_sub hrpos, Real.rpow_two]
  refine le_trans (measure_mono hsub) ?_
  refine (measure_biUnion_finset_le G _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hpow]
  calc (G.card : ℝ) * (C' * r ^ θ) ≤ 25 / r ^ 2 * (C' * r ^ θ) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 25 * C' * (r ^ θ / r ^ 2) := by ring

/-- The uniform estimate of Ding and Gwynne (Lemma 3.8, whole-plane case) for a random measure satisfying the
single-ball upper and lower tail estimates. -/
theorem polyHighProb_ballMass_of_single {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {μ : Ω → Measure ℂ} (hup : BallMassUpperTail P γ μ) (hlow : BallMassLowerTail P γ μ) (hγ0 : 0 ≤ γ)
    (hγ2 : γ < 2) {βl βu : ℝ} (hβl0 : 0 < βl) (hβl : βl < 2 / (2 + γ) ^ 2) (hβu : 2 / (2 - γ) ^ 2 < βu) :
    PolyHighProb P fun ε => {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ βl))) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ ω (ball z (ε ^ βu)) ≤ ENNReal.ofReal ε} := by
  obtain ⟨p₁, hp₁, C₁, r₁, hr₁, h₁⟩ := polyHighProb_ballMass_lower hlow hγ0 hβl0 hβl
  obtain ⟨p₂, hp₂, C₂, r₂, hr₂, h₂⟩ := polyHighProb_ballMass_upper hup hγ2 hβu
  refine ⟨min p₁ p₂, lt_min hp₁ hp₂, max C₁ 0 + max C₂ 0, min (min r₁ r₂) 1,
    lt_min (lt_min hr₁ hr₂) one_pos, ?_⟩
  intro ε hε hεr
  have hεr₁ : ε < r₁ := hεr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεr₂ : ε < r₂ := hεr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := (hεr.trans_le (min_le_right _ _)).le
  have hmono : ∀ {p : ℝ} {C : ℝ}, min p₁ p₂ ≤ p → ENNReal.ofReal (C * ε ^ p) ≤
      ENNReal.ofReal (max C 0 * ε ^ min p₁ p₂) := by
    intro p C hp
    refine ENNReal.ofReal_le_ofReal ?_
    calc C * ε ^ p ≤ max C 0 * ε ^ p := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ε ^ min p₁ p₂ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε hε1 hp) (le_max_right _ _)
  refine le_trans (measure_mono fun ω hω => ?_) ((measure_union_le
      {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ βl))}ᶜ
      {ω | ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ ω (ball z (ε ^ βu)) ≤ ENNReal.ofReal ε}ᶜ).trans ?_)
  · by_contra hc
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hc
    exact hω ⟨hc.1, hc.2⟩
  calc _ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ min p₁ p₂) + ENNReal.ofReal (max C₂ 0 * ε ^ min p₁ p₂) :=
        add_le_add ((h₁ ε hε hεr₁).trans (hmono (min_le_left _ _)))
          ((h₂ ε hε hεr₂).trans (hmono (min_le_right _ _)))
    _ = ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * ε ^ min p₁ p₂) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

/-- The literature statement `WholePlaneLQGBallMassBoundsLP` (Ding and Gwynne 2020, Lemma 3.8, whole-plane case)
from the single-ball upper and lower tail estimates for every γ-LQG measure of the whole-plane Gaussian free
field. -/
theorem wholePlaneLQGBallMassBoundsLP_of_single {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ μ : Ω → Measure ℂ,
      IsLQGMeasureOfField P γ 0 hcirc μ → BallMassUpperTail P γ μ ∧ BallMassLowerTail P γ μ) :
    WholePlaneLQGBallMassBoundsLP P γ hC hcirc := by
  intro hh hγ0 hγ2 μ hμ βl βu hβl0 hβl hβu
  obtain ⟨hup, hlow⟩ := h hh hγ0 hγ2 μ hμ
  exact polyHighProb_ballMass_of_single hup hlow hγ0.le hγ2 hβl0 hβl hβu

end LatticeProb.LQG
