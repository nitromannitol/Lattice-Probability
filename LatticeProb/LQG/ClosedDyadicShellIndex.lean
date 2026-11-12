import LatticeProb.LQG.ClosedDyadicCornerCell
import LatticeProb.LQG.InternalMetricWeylScalingAtPoint

/-!
# Closed dyadic subsquares near a corner of a square: the shell decomposition

Let `S = [a, a + s] × [b, b + s]` with `s > 0` and `a, b ∈ {0, -s}`, so that the origin is a corner of `S`.
Suppose a closed dyadic subsquare of `S` avoids the origin but its level-`K` ancestor contains the origin. Then, for
some level `k ≥ K`, it lies in a level-`(k + 1)` child of the corner cell `2^{-k} S` that avoids the origin. That child
is the image under `x ↦ 2^{-k} x` of a level-`1` cell `(I, J)` of `S` avoiding the origin. The subsquare itself is the
image of a closed dyadic subsquare of `[0, 1]²` under `x ↦ (s / 2) 2^{-k} x + 2^{-k} (a + I s / 2, b + J s / 2)`.
For such a level-`1` cell, the points `(s / 2) y + (a + I s / 2, b + J s / 2)`, `y ∈ [0, 1]²`, have modulus between
`s / 2` and `3 s / 2`.

## Main statements
* `LatticeProb.LQG.exists_shell_image_closedDyadicSubsquare`: the shell decomposition of a cell.
* `LatticeProb.LQG.le_norm_and_norm_le_of_zero_not_mem_closedDyadicSubsquare_one`: the modulus bounds on a level-`1`
  cell avoiding the origin.
-/

open Set

namespace LatticeProb.LQG

/-- One coordinate of the shell decomposition. Let `a ∈ {0, -s}` and let `⌊i' / 2⌋` be the corner index of level `k`.
Then the left endpoint of the level-`(k + 1)` interval with index `i'` is `2^{-k}` times the left endpoint of the
level-`1` interval with index `i' mod 2`. -/
theorem add_mul_div_two_pow_succ_eq_of_div_two_eq_cornerIndex {a s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s)
    {k i' : ℕ} (hi' : i' / 2 = if a = 0 then 0 else 2 ^ k - 1) :
    a + (i' : ℝ) * (s / 2 ^ (k + 1)) = ((2 : ℝ) ^ k)⁻¹ * (a + ((i' % 2 : ℕ) : ℝ) * (s / 2)) := by
  have hdm := Nat.div_add_mod i' 2
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rcases ha with rfl | rfl
  · simp only [↓reduceIte] at hi'
    rw [hi', mul_zero, zero_add] at hdm
    rw [hdm, pow_succ]
    field_simp
    ring
  · have hne : -s ≠ 0 := neg_ne_zero.2 hs.ne'
    simp only [hne, ↓reduceIte] at hi'
    rw [hi'] at hdm
    have hcast : (i' : ℝ) = 2 * ((2 : ℝ) ^ k - 1) + ((i' % 2 : ℕ) : ℝ) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hdm
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one] at h
      linarith
    rw [hcast, pow_succ]
    field_simp
    ring

/-- A closed dyadic subsquare of a square of side `s 2^{-(k+1)}` whose corner is `2^{-k} (x, y)` is the image of the
closed dyadic subsquare of `[0, 1]²` with the same level and indices under `z ↦ (s / 2) 2^{-k} z + 2^{-k} (x, y)`. -/
theorem closedDyadicSubsquare_eq_image_unit {s : ℝ} (hs : 0 < s) (k n i₀ j₀ : ℕ) (x y : ℝ) :
    closedDyadicSubsquare (((2 : ℝ) ^ k)⁻¹ * x) (((2 : ℝ) ^ k)⁻¹ * y) (s / 2 ^ (k + 1)) n i₀ j₀ =
      (fun z : ℂ => ((s / 2 / 2 ^ k : ℝ) : ℂ) * z + (2 ^ k : ℂ)⁻¹ * (⟨x, y⟩ : ℂ)) ''
        closedDyadicSubsquare 0 0 1 n i₀ j₀ := by
  have hc : (2 ^ k : ℂ)⁻¹ = ((((2 : ℝ) ^ k)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, closedDyadicSubsquare_eq_reProdIm, closedDyadicSubsquare_eq_reProdIm,
    affine_image_reProdIm (by positivity)]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  congr 1 <;> congr 1 <;> rw [pow_succ] <;> field_simp <;> ring

/-- **Shell decomposition of a closed dyadic subsquare near the corner.** Let `S = [a, a + s] × [b, b + s]` with
`s > 0` and `a, b ∈ {0, -s}`. Let the closed dyadic subsquare of `S` of level `m` with indices `(i, j)` avoid the
origin, while its level-`K` ancestor (`K ≤ m`) contains it. Then there are a level `k ≥ K` and a level-`1` cell
`(I, J)` of `S` avoiding the origin such that the subsquare is the image of a closed dyadic subsquare of `[0, 1]²`
under `x ↦ (s / 2) 2^{-k} x + 2^{-k} (a + I s / 2, b + J s / 2)`. -/
theorem exists_shell_image_closedDyadicSubsquare {a b s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s)
    (hb : b = 0 ∨ b = -s) {K m i j : ℕ} (hKm : K ≤ m) (hi : i < 2 ^ m) (hj : j < 2 ^ m)
    (hK : (0 : ℂ) ∈ closedDyadicSubsquare a b s K (i / 2 ^ (m - K)) (j / 2 ^ (m - K)))
    (h0 : (0 : ℂ) ∉ closedDyadicSubsquare a b s m i j) :
    ∃ k : ℕ, K ≤ k ∧ ∃ I J : ℕ, I < 2 ∧ J < 2 ∧ (0 : ℂ) ∉ closedDyadicSubsquare a b s 1 I J ∧
      ∃ n i₀ j₀ : ℕ, i₀ < 2 ^ n ∧ j₀ < 2 ^ n ∧
        closedDyadicSubsquare a b s m i j =
          (fun x : ℂ => ((s / 2 / 2 ^ k : ℝ) : ℂ) * x +
            (2 ^ k : ℂ)⁻¹ * (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ)) ''
            closedDyadicSubsquare 0 0 1 n i₀ j₀ := by
  classical
  -- the first level at which the ancestor avoids the origin
  have hm0 : (0 : ℂ) ∉ closedDyadicSubsquare a b s (K + (m - K)) (i / 2 ^ (m - (K + (m - K))))
      (j / 2 ^ (m - (K + (m - K)))) := by
    rwa [Nat.add_sub_cancel' hKm, Nat.sub_self, pow_zero, Nat.div_one, Nat.div_one]
  have hex : ∃ n, (0 : ℂ) ∉ closedDyadicSubsquare a b s (K + n) (i / 2 ^ (m - (K + n)))
      (j / 2 ^ (m - (K + n))) := ⟨m - K, hm0⟩
  have hle : Nat.find hex ≤ m - K := Nat.find_min' hex hm0
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    have hs' := Nat.find_spec hex
    rw [h, add_zero] at hs'
    exact hs' hK
  obtain ⟨k, hKk, hk1⟩ : ∃ k, K ≤ k ∧ K + Nat.find hex = k + 1 := ⟨K + (Nat.find hex - 1), by omega, by omega⟩
  have hkm : k + 1 ≤ m := by omega
  have hQk : (0 : ℂ) ∈ closedDyadicSubsquare a b s k (i / 2 ^ (m - k)) (j / 2 ^ (m - k)) := by
    have h := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [not_not, show K + (Nat.find hex - 1) = k by omega] at h
    exact h
  have hQk1 : (0 : ℂ) ∉ closedDyadicSubsquare a b s (k + 1) (i / 2 ^ (m - (k + 1)))
      (j / 2 ^ (m - (k + 1))) := by
    rw [← hk1]
    exact Nat.find_spec hex
  -- the indices of the level-`(k + 1)` ancestor
  obtain ⟨i', hi'⟩ : ∃ i', i' = i / 2 ^ (m - (k + 1)) := ⟨_, rfl⟩
  obtain ⟨j', hj'⟩ : ∃ j', j' = j / 2 ^ (m - (k + 1)) := ⟨_, rfl⟩
  have hdiv : ∀ l : ℕ, l / 2 ^ (m - k) = l / 2 ^ (m - (k + 1)) / 2 := by
    intro l
    rw [Nat.div_div_eq_div_mul, ← pow_succ, show m - (k + 1) + 1 = m - k by omega]
  have hlt : ∀ l : ℕ, l < 2 ^ m → l / 2 ^ (m - k) < 2 ^ k := by
    intro l hl
    refine Nat.div_lt_of_lt_mul ?_
    rwa [← pow_add, show m - k + k = m by omega]
  have hcorner := eq_cornerIndex_of_zero_mem_closedDyadicSubsquare hs ha hb (hlt i hi) (hlt j hj) hQk
  rw [hdiv i, ← hi', hdiv j, ← hj'] at hcorner
  have hxL := add_mul_div_two_pow_succ_eq_of_div_two_eq_cornerIndex hs ha hcorner.1
  have hyL := add_mul_div_two_pow_succ_eq_of_div_two_eq_cornerIndex hs hb hcorner.2
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨k, hKk, i' % 2, j' % 2, Nat.mod_lt _ two_pos, Nat.mod_lt _ two_pos, ?_, m - (k + 1),
    i % 2 ^ (m - (k + 1)), j % 2 ^ (m - (k + 1)), Nat.mod_lt _ (by positivity),
    Nat.mod_lt _ (by positivity), ?_⟩
  · -- the level-`1` cell avoids the origin, since its image under `x ↦ 2^{-k} x` does
    intro h1
    apply hQk1
    rw [← hi', ← hj']
    rw [closedDyadicSubsquare_eq_reProdIm, Complex.mem_reProdIm, pow_one] at h1
    rw [closedDyadicSubsquare_eq_reProdIm, Complex.mem_reProdIm, hxL, hyL]
    have e : s / 2 ^ (k + 1) = ((2 : ℝ) ^ k)⁻¹ * (s / 2) := by rw [pow_succ]; field_simp
    rw [e, ← mul_add, ← mul_add]
    obtain ⟨⟨h11, h12⟩, h13, h14⟩ := h1
    have hk0 : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
    exact ⟨⟨mul_nonpos_of_nonneg_of_nonpos hk0 h11, mul_nonneg hk0 h12⟩,
      ⟨mul_nonpos_of_nonneg_of_nonpos hk0 h13, mul_nonneg hk0 h14⟩⟩
  · rw [closedDyadicSubsquare_eq_of_le a b s hkm i j, ← hi', ← hj', hxL, hyL]
    exact closedDyadicSubsquare_eq_image_unit hs k _ _ _ _ _

/-- One coordinate of the modulus bounds: for `a ∈ {0, -s}`, `I < 2` and `u ∈ [0, 1]`, the point
`w = (s / 2) u + a + I s / 2` satisfies `|w| ≤ s`, and `|w| ≥ s / 2` when the interval `[a + I s / 2, a + (I + 1) s / 2]`
avoids the origin. -/
theorem abs_le_and_le_abs_of_zero_not_mem_Icc {a s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) {I : ℕ} (hI : I < 2)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |s / 2 * u + (a + I * (s / 2))| ≤ s ∧
      ((0 : ℝ) ∉ Icc (a + I * (s / 2)) (a + I * (s / 2) + s / 2) →
        s / 2 ≤ |s / 2 * u + (a + I * (s / 2))|) := by
  obtain ⟨hu0, hu1⟩ := hu
  have p1 : 0 ≤ s / 2 * u := mul_nonneg (by positivity) hu0
  have p2 : s / 2 * u ≤ s / 2 := mul_le_of_le_one_right (by positivity) hu1
  interval_cases I <;> rcases ha with rfl | rfl <;>
    simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] <;>
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, fun h => ?_⟩ <;>
    by_contra hc <;> rw [not_le, abs_lt] at hc <;> apply h <;> rw [mem_Icc] <;>
    constructor <;> linarith

/-- **Modulus bounds on a level-`1` cell avoiding the origin.** Let `S = [a, a + s] × [b, b + s]` with `s > 0` and
`a, b ∈ {0, -s}`, and let the level-`1` cell `(I, J)` of `S` avoid the origin. Then for `y ∈ [0, 1]²` the point
`(s / 2) y + (a + I s / 2, b + J s / 2)` of that cell has modulus between `s / 2` and `3 (s / 2)`. -/
theorem le_norm_and_norm_le_of_zero_not_mem_closedDyadicSubsquare_one {a b s : ℝ} (hs : 0 < s)
    (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s) {I J : ℕ} (hI : I < 2) (hJ : J < 2)
    (h0 : (0 : ℂ) ∉ closedDyadicSubsquare a b s 1 I J) :
    ∀ y ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      s / 2 ≤ ‖((s / 2 : ℝ) : ℂ) * y + (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ)‖ ∧
        ‖((s / 2 : ℝ) : ℂ) * y + (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ)‖ ≤ 3 * (s / 2) := by
  intro y hy
  rw [Complex.mem_reProdIm] at hy
  rw [closedDyadicSubsquare_eq_reProdIm, Complex.mem_reProdIm, pow_one, Complex.zero_re,
    Complex.zero_im, not_and_or] at h0
  set z : ℂ := ((s / 2 : ℝ) : ℂ) * y + (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ) with hz
  have hre : z.re = s / 2 * y.re + (a + I * (s / 2)) := by
    simp only [hz, Complex.add_re, Complex.re_ofReal_mul]
  have him : z.im = s / 2 * y.im + (b + J * (s / 2)) := by
    simp only [hz, Complex.add_im, Complex.im_ofReal_mul]
  obtain ⟨hre1, hre2⟩ := abs_le_and_le_abs_of_zero_not_mem_Icc hs ha hI hy.1
  obtain ⟨him1, him2⟩ := abs_le_and_le_abs_of_zero_not_mem_Icc hs hb hJ hy.2
  rw [← hre] at hre1 hre2
  rw [← him] at him1 him2
  refine ⟨?_, ?_⟩
  · rcases h0 with h | h
    · exact (hre2 h).trans (Complex.abs_re_le_norm z)
    · exact (him2 h).trans (Complex.abs_im_le_norm z)
  · have hsq : ‖z‖ ^ 2 ≤ (3 * (s / 2)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h1 : z.re * z.re ≤ s ^ 2 := by rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
      have h2 : z.im * z.im ≤ s ^ 2 := by rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him1 2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg z) (by positivity) two_ne_zero).1 hsq

end LatticeProb.LQG
