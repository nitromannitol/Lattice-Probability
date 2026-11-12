import LatticeProb.Gauss.CircleAverageModulusRate
import LatticeProb.LQG.LQGMeasure

/-!
# A uniform modulus of the circle averages in the radius at dyadic scales

Let `h` be a whole-plane Gaussian free field with circle averages `h_s(z)`, and let
`ε_k = 2^{-k}` (`LatticeProb.LQG.dyadicScale`). For every `a > 0` and every radius `R₀` there is an
exponent `β > 0` such that almost surely, for all large `k`, all `z` with `|z| ≤ R₀` and all radii
`s, s' ∈ [ε_k / 2, ε_k]` with `|s - s'| < ε_k ε_k^a`,

`|h_s(z) - h_{s'}(z)| ≤ ε_k^β`.

The proof covers `{(s, z) : s ∈ [ε/2, ε], |z| ≤ R₀}` by the rescaled boxes
`(s, z) = (ε x₀, ε (m + i n) + ε (x₁ + i x₂))`, `x ∈ [1/2, 1] × [0, 1]²`, with lattice centres
`|m|, |n| ≤ ⌈R₀ 2^k⌉`, applies the per-box modulus rate
`IsWholePlaneGFF.measure_circleRescaled_modulus_gt_le` at the dyadic level `⌊a k⌋` with
`p = 12 + 12 / a` and `c = 2^{-1/4}` to each of the `O(4^k)` boxes, and concludes by the
Borel–Cantelli lemma.

## Main results

* `LatticeProb.Gauss.circleBoxPoint`, `LatticeProb.Gauss.circleBoxCentre`: the covering by boxes,
  with `circleRescaled_circleBoxPoint`.
* `LatticeProb.Gauss.IsWholePlaneGFF.measure_circleBadEvent_le`: union bound over the boxes.
* `LatticeProb.Gauss.IsWholePlaneGFF.ae_eventually_abs_circle_sub_le`: the uniform modulus.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.LQG (dyadicScale)

namespace LatticeProb.Gauss

/-- For a scale `ε`, a radius `s` and a point `z`, the point `(s / ε, {Re z / ε}, {Im z / ε})`
(fractional parts) of the box `[1/2, 1] × [0, 1]²`. -/
noncomputable def circleBoxPoint (ε s : ℝ) (z : ℂ) : Fin 3 → ℝ :=
  ![s / ε, Int.fract (z.re / ε), Int.fract (z.im / ε)]

/-- The lattice centre `ε (m + i n)`. -/
def circleBoxCentre (ε : ℝ) (m n : ℤ) : ℂ := ⟨ε * m, ε * n⟩

theorem circleBoxPoint_mem {ε s : ℝ} (hε : 0 < ε) (hs : ε / 2 ≤ s) (hs' : s ≤ ε) (z : ℂ) :
    circleBoxPoint ε s z ∈ Set.Icc circleBoxLower circleBoxUpper := by
  have h1 : (1 : ℝ) / 2 ≤ s / ε := by rw [le_div_iff₀ hε]; linarith
  have h2 : s / ε ≤ 1 := (div_le_one hε).2 hs'
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    first
    | exact h1
    | exact h2
    | exact Int.fract_nonneg _
    | exact (Int.fract_lt_one _).le

/-- The rescaled circle-average process at the box point of `(s, z)`, with the lattice centre of
`z`, is the circle average `h_s(z)`. -/
theorem circleRescaled_circleBoxPoint {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) {ε : ℝ} (hε : ε ≠ 0)
    (s : ℝ) (z : ℂ) (ω : Ω) :
    circleRescaled hcirc ε (circleBoxCentre ε ⌊z.re / ε⌋ ⌊z.im / ε⌋) (circleBoxPoint ε s z) ω
      = hcirc ω s z := by
  have h1 : ε * (s / ε) = s := by field_simp
  have h2 : circleBoxCentre ε ⌊z.re / ε⌋ ⌊z.im / ε⌋
      + (ε : ℂ) * ⟨Int.fract (z.re / ε), Int.fract (z.im / ε)⟩ = z := by
    apply Complex.ext
    · simp only [circleBoxCentre, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [← mul_add, Int.floor_add_fract]
      field_simp
    · simp only [circleBoxCentre, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rw [← mul_add, Int.floor_add_fract]
      field_simp
  show hcirc ω (ε * (s / ε)) (circleBoxCentre ε ⌊z.re / ε⌋ ⌊z.im / ε⌋
      + (ε : ℂ) * ⟨Int.fract (z.re / ε), Int.fract (z.im / ε)⟩) = hcirc ω s z
  rw [h1, h2]

/-- Two radii `s, s'` at the same point `z` give box points at sup-distance `|s - s'| / ε`. -/
theorem dist_circleBoxPoint_lt {ε r s s' : ℝ} (hε : 0 < ε) (hr : 0 < r) (z : ℂ)
    (h : |s - s'| < ε * r) : dist (circleBoxPoint ε s z) (circleBoxPoint ε s' z) < r := by
  rw [dist_pi_lt_iff hr]
  intro i
  fin_cases i
  · show dist (s / ε) (s' / ε) < r
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε, div_lt_iff₀ hε]
    linarith [mul_comm ε r]
  · show dist (Int.fract (z.re / ε)) (Int.fract (z.re / ε)) < r
    simpa using hr
  · show dist (Int.fract (z.im / ε)) (Int.fract (z.im / ε)) < r
    simpa using hr

theorem floor_mem_Icc_of_abs_le {t R : ℝ} {L : ℕ} (h : |t| ≤ R) (hL : R ≤ L) :
    ⌊t⌋ ∈ Finset.Icc (-(L : ℤ)) L := by
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [neg_abs_le t]
  · have h' : ((⌊t⌋ : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := by
      push_cast
      linarith [Int.floor_le t, le_abs_self t]
    exact_mod_cast h'

/-- The per-box bound of `IsWholePlaneGFF.measure_circleRescaled_modulus_gt_le`. -/
noncomputable def circleModulusBound (p c : ℝ) (N : ℕ) : ℝ :=
  (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2) * 3 * 3 ^ 3 *
    (∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p) ^ j) *
    ((N : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p) ^ N

/-- The event that one of the rescaled boxes with lattice centres `ε (m + i n)`, `|m|, |n| ≤ L`,
carries an increment larger than `7 c^M / (1 - c)` at sup-distance less than `2^{-M}`. -/
def circleBadEvent {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (c ε : ℝ) (L M : ℕ) : Set Ω :=
  ⋃ mn ∈ Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L,
    {ω | ∃ x ∈ Set.Icc circleBoxLower circleBoxUpper,
      ∃ y ∈ Set.Icc circleBoxLower circleBoxUpper, dist x y < 1 / 2 ^ M ∧
        7 * c ^ M / (1 - c) < |circleRescaled hcirc ε (circleBoxCentre ε mn.1 mn.2) x ω -
          circleRescaled hcirc ε (circleBoxCentre ε mn.1 mn.2) y ω|}

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Union bound over the `(2L + 1)²` boxes. -/
theorem measure_circleBadEvent_le (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (hc1 : c < 1)
    (hθ : (2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p < 1) (L : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    P (circleBadEvent hcirc c ε L M)
      ≤ ENNReal.ofReal ((2 * (L : ℝ) + 1) ^ 2 * circleModulusBound p c M) := by
  unfold circleBadEvent
  calc _ ≤ ∑ mn ∈ Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L,
        ENNReal.ofReal (circleModulusBound p c M) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun mn _ => ?_)
        exact measure_circleRescaled_modulus_gt_le hh hε _ hp hc hc1 hθ hM
    _ = ENNReal.ofReal ((2 * (L : ℝ) + 1) ^ 2 * circleModulusBound p c M) := by
        rw [Finset.sum_const, Finset.card_product, Int.card_Icc, nsmul_eq_mul]
        have hcard : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
        rw [hcard, ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
        congr 2
        push_cast
        ring

/-- **Uniform modulus of the circle averages in the radius at dyadic scales.** For every `a > 0`
and `R₀` there is `β > 0` such that almost surely, for all large `k`, all `z` with `|z| ≤ R₀`, and
all radii `s, s' ∈ [ε_k / 2, ε_k]` with `|s - s'| < ε_k ε_k^a` (`ε_k = 2^{-k}`),
`|h_s(z) - h_{s'}(z)| ≤ ε_k^β`. -/
theorem ae_eventually_abs_circle_sub_le (hh : IsWholePlaneGFF P hC hcirc) {a : ℝ} (ha : 0 < a)
    (R₀ : ℝ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ z : ℂ, ‖z‖ ≤ R₀ → ∀ s s' : ℝ,
      dyadicScale k / 2 ≤ s → s ≤ dyadicScale k → dyadicScale k / 2 ≤ s' → s' ≤ dyadicScale k →
      |s - s'| < dyadicScale k * dyadicScale k ^ a →
      |hcirc ω s z - hcirc ω s' z| ≤ dyadicScale k ^ β := by
  have := hh.isProbabilityMeasure
  -- parameters
  set b : ℝ := 2⁻¹ with hbdef
  have hb0 : 0 < b := by norm_num [hbdef]
  have hb1 : b < 1 := by norm_num [hbdef]
  set p : ℝ := 12 + 12 / a with hpdef
  have hp : 0 < p := by positivity
  set c : ℝ := b ^ (1 / 4 : ℝ) with hcdef
  have hc0 : 0 < c := Real.rpow_pos_of_pos hb0 _
  have hc1 : c < 1 := Real.rpow_lt_one hb0.le hb1 (by norm_num)
  set θ : ℝ := (2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p with hθdef
  have hθb : θ = b ^ (3 / a) := by
    rw [hθdef, hcdef, ← Real.rpow_mul hb0.le, hbdef, Real.inv_rpow (by norm_num),
      Real.inv_rpow (by norm_num), div_inv_eq_mul, ← Real.rpow_add (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    congr 1
    rw [hpdef]
    ring
  have hθ0 : 0 < θ := by rw [hθb]; exact Real.rpow_pos_of_pos hb0 _
  have hθ1 : θ < 1 := by rw [hθb]; exact Real.rpow_lt_one hb0.le hb1 (by positivity)
  set K : ℝ := (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2) * 3 * 3 ^ 3 *
    (∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * θ ^ j) with hKdef
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ ∫ t, |t| ^ p ∂(gaussianReal 0 1) := integral_nonneg fun t => by positivity
    have h2 : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * θ ^ j := tsum_nonneg fun j => by positivity
    positivity
  have hB : ∀ n : ℕ, circleModulusBound p c n = K * ((n : ℝ) + 1) ^ 3 * θ ^ n := fun n => rfl
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  set L : ℕ → ℕ := fun k => ⌈R * 2 ^ k⌉₊ with hLdef
  set M : ℕ → ℕ := fun k => max ⌊a * k⌋₊ 1 with hMdef
  have hMge : ∀ k : ℕ, a * k - 1 ≤ (M k : ℝ) := by
    intro k
    have h1 := (Nat.lt_floor_add_one (a * k)).le
    have h2 : (⌊a * (k : ℝ)⌋₊ : ℝ) ≤ (M k : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  set E : ℕ → Set Ω := fun k => circleBadEvent hcirc c (dyadicScale k) (L k) (M k) with hEdef
  have hεpos : ∀ k : ℕ, 0 < dyadicScale k := fun k => by simp only [dyadicScale]; positivity
  have hE : ∀ k, P (E k) ≤ ENNReal.ofReal ((2 * (L k : ℝ) + 1) ^ 2 * circleModulusBound p c (M k)) :=
    fun k => measure_circleBadEvent_le hh (hεpos k) hp hc0 hc1 hθ1 (L k) (le_max_right _ _)
  -- summability of the bounds
  set C : ℝ := (2 * R + 3) ^ 2 * K * (a + 2) ^ 3 * b ^ (-(3 / a)) with hCdef
  have hC : 0 ≤ C := by
    have : 0 < b ^ (-(3 / a)) := Real.rpow_pos_of_pos hb0 _
    positivity
  have hterm : ∀ k : ℕ, (2 * (L k : ℝ) + 1) ^ 2 * circleModulusBound p c (M k)
      ≤ C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k := by
    intro k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hL : 2 * (L k : ℝ) + 1 ≤ (2 * R + 3) * 2 ^ k := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ R * 2 ^ k by positivity)
      have : (L k : ℝ) = (⌈R * 2 ^ k⌉₊ : ℝ) := rfl
      nlinarith
    have h4 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hL2 : (2 * (L k : ℝ) + 1) ^ 2 ≤ (2 * R + 3) ^ 2 * 4 ^ k := by
      rw [← h4, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hL 2
    have hM1 : (M k : ℝ) + 1 ≤ (a + 2) * ((k : ℝ) + 1) := by
      have h1 : (M k : ℝ) ≤ a * k + 1 := by
        rcases le_total ⌊a * (k : ℝ)⌋₊ 1 with h | h
        · have : M k = 1 := max_eq_right h
          rw [this]
          push_cast
          nlinarith [ha.le, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        · have : M k = ⌊a * (k : ℝ)⌋₊ := max_eq_left h
          rw [this]
          have := Nat.floor_le (show 0 ≤ a * (k : ℝ) by positivity)
          linarith
      nlinarith [ha.le, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hM3 : ((M k : ℝ) + 1) ^ 3 ≤ (a + 2) ^ 3 * ((k : ℝ) + 1) ^ 3 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hM1 3
    have hθM : θ ^ M k ≤ b ^ (-(3 / a)) * (1 / 8) ^ k := by
      rw [hθb, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      calc b ^ (3 / a * (M k : ℝ)) ≤ b ^ (3 / a * (a * k - 1)) :=
            Real.rpow_le_rpow_of_exponent_ge hb0 hb1.le
              (mul_le_mul_of_nonneg_left (hMge k) (by positivity))
        _ = b ^ (-(3 / a)) * (1 / 8) ^ k := by
            rw [show 3 / a * (a * k - 1) = -(3 / a) + 3 * (k : ℝ) by field_simp; ring,
              Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le]
            congr 2
            rw [hbdef]
            norm_num
    rw [hB]
    calc (2 * (L k : ℝ) + 1) ^ 2 * (K * ((M k : ℝ) + 1) ^ 3 * θ ^ M k)
        ≤ ((2 * R + 3) ^ 2 * 4 ^ k) *
            (K * ((a + 2) ^ 3 * ((k : ℝ) + 1) ^ 3) * (b ^ (-(3 / a)) * (1 / 8) ^ k)) := by
          apply mul_le_mul hL2 _ (mul_nonneg (mul_nonneg hK (by positivity)) (by positivity))
            (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hM3 hK) hθM (by positivity)
            (mul_nonneg hK (by positivity))
      _ = C * ((k : ℝ) + 1) ^ 3 * (4 * (1 / 8)) ^ k := by
          rw [hCdef, mul_pow]
          ring
      _ = C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k := by norm_num
  have hsum : Summable (fun k : ℕ => C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k) :=
    LatticeProb.summable_polynomial_geometric 3 (by norm_num) (by norm_num)
  have htsum : ∑' k, P (E k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := ∑' k : ℕ, C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
    exact ENNReal.tsum_le_tsum fun k => (hE k).trans (ENNReal.ofReal_le_ofReal (hterm k))
  -- the deterministic eventual bounds
  set q : ℝ := b ^ (a / 8) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hb0 _
  have hq1 : q < 1 := Real.rpow_lt_one hb0.le hb1 (by positivity)
  have hD : ∀ k : ℕ, dyadicScale k ^ (a / 8) = q ^ k := by
    intro k
    simp only [dyadicScale]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ),
      Real.rpow_mul_natCast (by norm_num)]
  have hcM : ∀ k : ℕ, c ^ M k ≤ b ^ (-(1 / 4 : ℝ)) * (q ^ k) ^ 2 := by
    intro k
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    calc b ^ (1 / 4 * (M k : ℝ)) ≤ b ^ (1 / 4 * (a * k - 1)) :=
          Real.rpow_le_rpow_of_exponent_ge hb0 hb1.le (by linarith [hMge k])
      _ = b ^ (-(1 / 4 : ℝ)) * (q ^ k) ^ 2 := by
          rw [hqdef, ← pow_mul, ← Real.rpow_mul_natCast hb0.le, ← Real.rpow_add hb0]
          congr 1
          push_cast
          ring
  have ev1 : ∀ᶠ k : ℕ in atTop, 1 ≤ ⌊a * (k : ℝ)⌋₊ := by
    refine Filter.eventually_atTop.2 ⟨⌈1 / a⌉₊, fun k hk => Nat.le_floor ?_⟩
    have h1 : (1 / a : ℝ) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [div_le_iff₀ ha] at h1
    push_cast
    linarith [mul_comm (k : ℝ) a]
  set A : ℝ := 7 * b ^ (-(1 / 4 : ℝ)) / (1 - c) with hAdef
  have ev2 : ∀ᶠ k : ℕ in atTop, A * q ^ k < 1 := by
    have ht : Tendsto (fun k : ℕ => A * q ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul A
    exact ht.eventually (gt_mem_nhds one_pos)
  refine ⟨a / 8, by positivity, ?_⟩
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω, ev1, ev2] with k hk hk1 hk2
  intro z hz s s' hs1 hs2 hs1' hs2' hss
  have hε := hεpos k
  have hMk : M k = ⌊a * (k : ℝ)⌋₊ := max_eq_left hk1
  -- the lattice centre of `z`
  have h2ε : (2 : ℝ) ^ k * dyadicScale k = 1 := by
    simp only [dyadicScale]
    rw [← mul_pow]
    norm_num
  have hbound : ∀ t : ℝ, |t| ≤ ‖z‖ → |t / dyadicScale k| ≤ R * 2 ^ k := by
    intro t ht
    rw [abs_div, abs_of_pos hε, div_le_iff₀ hε, mul_assoc, h2ε, mul_one]
    exact ht.trans (hz.trans (le_max_left _ _))
  have hmn : (⌊z.re / dyadicScale k⌋, ⌊z.im / dyadicScale k⌋) ∈
      Finset.Icc (-(L k : ℤ)) (L k) ×ˢ Finset.Icc (-(L k : ℤ)) (L k) :=
    Finset.mem_product.2
      ⟨floor_mem_Icc_of_abs_le (hbound _ (Complex.abs_re_le_norm z)) (Nat.le_ceil _),
        floor_mem_Icc_of_abs_le (hbound _ (Complex.abs_im_le_norm z)) (Nat.le_ceil _)⟩
  have hx := circleBoxPoint_mem hε hs1 hs2 z
  have hy := circleBoxPoint_mem hε hs1' hs2' z
  have hεa : dyadicScale k ^ a ≤ 1 / 2 ^ M k := by
    rw [hMk]
    simp only [dyadicScale]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, ← inv_pow,
      ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (by rw [mul_comm]; exact Nat.floor_le (by positivity))
  have hdist : dist (circleBoxPoint (dyadicScale k) s z) (circleBoxPoint (dyadicScale k) s' z)
      < 1 / 2 ^ M k :=
    dist_circleBoxPoint_lt hε (by positivity) z
      (hss.trans_le (mul_le_mul_of_nonneg_left hεa hε.le))
  have hle : |circleRescaled hcirc (dyadicScale k)
        (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋)
        (circleBoxPoint (dyadicScale k) s z) ω -
      circleRescaled hcirc (dyadicScale k)
        (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋)
        (circleBoxPoint (dyadicScale k) s' z) ω| ≤ 7 * c ^ M k / (1 - c) :=
    not_lt.1 fun h => hk (Set.mem_iUnion₂.2 ⟨_, hmn, _, hx, _, hy, hdist, h⟩)
  rw [circleRescaled_circleBoxPoint hcirc hε.ne', circleRescaled_circleBoxPoint hcirc hε.ne']
    at hle
  have hqk : 0 ≤ q ^ k := by positivity
  calc |hcirc ω s z - hcirc ω s' z| ≤ 7 * c ^ M k / (1 - c) := hle
    _ ≤ 7 * (b ^ (-(1 / 4 : ℝ)) * (q ^ k) ^ 2) / (1 - c) := by
        gcongr
        exact hcM k
    _ = (A * q ^ k) * q ^ k := by rw [hAdef]; ring
    _ ≤ 1 * q ^ k := mul_le_mul_of_nonneg_right hk2.le hqk
    _ = dyadicScale k ^ (a / 8) := by rw [one_mul, hD]

end IsWholePlaneGFF

end LatticeProb.Gauss
