import LatticeProb.LQG.InternalMetricChaining

/-!
# Chaining the internal metric over nested closed dyadic squares

A deterministic multiscale bound for the internal diameter of a closed square `S = [a, a + s] × [b, b + s]` in its own
internal metric, in the form used in the proof of Dubédat-Falconet-Gwynne-Pfeffer-Sun (arXiv:1905.00380,
Proposition 3.10, Step 2). Suppose that each closed dyadic subsquare `S_{n,i,j}` of level `n` of `S` carries a set
`X n i j ⊆ S_{n,i,j}` of internal diameter in `S` at most `L n`, and that the set of each subsquare meets the set of its
parent. Then any two points of `S` are at internal distance in `S` at most `L 0 + 2 ∑_{n ≥ 1} L n`.

Each point `z ∈ S` lies in a nested sequence of closed dyadic subsquares `S_n(z)` (with clamped dyadic indices, so that
points of the right and top sides are included); points `x_n ∈ X(S_n(z)) ∩ X(S_{n+1}(z))` converge to `z`, and the
chaining bound for convergent sequences in a closed bounded set gives `D(x_0, z; S) ≤ ∑_{n ≥ 1} L n`.

In applications `X n i j` is the union of four crossings of the halves of `S_{n,i,j}`, see
`IsEuclideanLengthMetric.internalMetric_le_of_crossings`.

## Main statements

* `dyadicIndex`: the clamped dyadic index `min ⌊2ⁿ u⌋ (2ⁿ - 1)` of `u ∈ [0, 1]`; `dyadicIndex_succ_div_two`.
* `closedDyadicSubsquare`, `mem_closedDyadicSubsquare_dyadicIndex`, `closedDyadicSubsquare_subset`,
  `norm_sub_le_of_mem_closedDyadicSubsquare`.
* `IsEuclideanLengthMetric.internalMetric_le_of_dyadic_chain`: the multiscale bound.
-/

namespace LatticeProb.LQG

open Set Filter
open scoped ENNReal Topology

/-- The clamped dyadic index of `u` at level `n`: `min ⌊2ⁿ u⌋ (2ⁿ - 1)`. For `u ∈ [0, 1]` it is the index `i < 2ⁿ` of a
closed dyadic interval `[i 2⁻ⁿ, (i + 1) 2⁻ⁿ]` containing `u`. -/
noncomputable def dyadicIndex (u : ℝ) (n : ℕ) : ℕ := min ⌊u * 2 ^ n⌋₊ (2 ^ n - 1)

theorem dyadicIndex_lt (u : ℝ) (n : ℕ) : dyadicIndex u n < 2 ^ n := by
  unfold dyadicIndex
  have := Nat.one_le_two_pow (n := n)
  omega

@[simp]
theorem dyadicIndex_zero (u : ℝ) : dyadicIndex u 0 = 0 := by simp [dyadicIndex]

theorem floor_mul_two_pow_le {u : ℝ} (hu1 : u ≤ 1) (n : ℕ) : ⌊u * 2 ^ n⌋₊ ≤ 2 ^ n :=
  Nat.floor_le_of_le (by push_cast; exact mul_le_of_le_one_left (by positivity) hu1)

/-- The dyadic index at level `n + 1` is a child of the dyadic index at level `n`. -/
theorem dyadicIndex_succ_div_two {u : ℝ} (hu1 : u ≤ 1) (n : ℕ) :
    dyadicIndex u (n + 1) / 2 = dyadicIndex u n := by
  have hfl : ⌊u * 2 ^ (n + 1)⌋₊ / 2 = ⌊u * 2 ^ n⌋₊ := by
    rw [← Nat.floor_div_natCast]; congr 1; push_cast; ring
  have hA := floor_mul_two_pow_le hu1 n
  have hB := floor_mul_two_pow_le hu1 (n + 1)
  have hN := Nat.one_le_two_pow (n := n)
  have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  unfold dyadicIndex
  rw [h2] at hB ⊢
  omega

theorem dyadicIndex_le_mul {u : ℝ} (hu0 : 0 ≤ u) (n : ℕ) : (dyadicIndex u n : ℝ) ≤ u * 2 ^ n :=
  (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (by positivity))

theorem mul_le_dyadicIndex_add_one {u : ℝ} (hu1 : u ≤ 1) (n : ℕ) : u * 2 ^ n ≤ dyadicIndex u n + 1 := by
  rcases le_or_gt ⌊u * 2 ^ n⌋₊ (2 ^ n - 1) with h | h
  · have : dyadicIndex u n = ⌊u * 2 ^ n⌋₊ := min_eq_left h
    rw [this]; exact (Nat.lt_floor_add_one _).le
  · have hA := floor_mul_two_pow_le hu1 n
    have hN := Nat.one_le_two_pow (n := n)
    have h1 : dyadicIndex u n + 1 = 2 ^ n := by unfold dyadicIndex; omega
    have hc : (dyadicIndex u n : ℝ) + 1 = 2 ^ n := by exact_mod_cast h1
    rw [hc]; exact mul_le_of_le_one_left (by positivity) hu1

/-- A point of `[a, a + s]` lies in the closed dyadic interval of level `n` given by its clamped dyadic index. -/
theorem mem_Icc_dyadicIndex {a s x : ℝ} (hs : 0 < s) (hx : x ∈ Icc a (a + s)) (n : ℕ) :
    x ∈ Icc (a + dyadicIndex ((x - a) / s) n * (s / 2 ^ n)) (a + (dyadicIndex ((x - a) / s) n + 1) * (s / 2 ^ n)) := by
  set u := (x - a) / s with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hx.1]) hs.le
  have hu1 : u ≤ 1 := (div_le_one hs).2 (by linarith [hx.2])
  have hxu : x = a + u * s := by rw [hu]; field_simp; ring
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 := dyadicIndex_le_mul hu0 n
  have h2 := mul_le_dyadicIndex_add_one hu1 n
  have e : u * 2 ^ n * (s / 2 ^ n) = u * s := by field_simp
  constructor
  · rw [hxu, add_le_add_iff_left, ← e]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · rw [hxu, add_le_add_iff_left, ← e]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- The closed dyadic subsquare `[a + i 2⁻ⁿ s, a + (i + 1) 2⁻ⁿ s] × [b + j 2⁻ⁿ s, b + (j + 1) 2⁻ⁿ s]` of level `n` of the
closed square `[a, a + s] × [b, b + s]`. -/
def closedDyadicSubsquare (a b s : ℝ) (n i j : ℕ) : Set ℂ :=
  Icc (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) ×ℂ Icc (b + j * (s / 2 ^ n)) (b + (j + 1) * (s / 2 ^ n))

@[simp]
theorem closedDyadicSubsquare_zero (a b s : ℝ) :
    closedDyadicSubsquare a b s 0 0 0 = Icc a (a + s) ×ℂ Icc b (b + s) := by
  simp [closedDyadicSubsquare]

/-- A point of the closed square lies in the closed dyadic subsquare of level `n` given by its clamped dyadic
indices. -/
theorem mem_closedDyadicSubsquare_dyadicIndex {a b s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z ∈ Icc a (a + s) ×ℂ Icc b (b + s)) (n : ℕ) :
    z ∈ closedDyadicSubsquare a b s n (dyadicIndex ((z.re - a) / s) n) (dyadicIndex ((z.im - b) / s) n) :=
  Complex.mem_reProdIm.2 ⟨mem_Icc_dyadicIndex hs (Complex.mem_reProdIm.1 hz).1 n,
    mem_Icc_dyadicIndex hs (Complex.mem_reProdIm.1 hz).2 n⟩

theorem Icc_dyadic_subset {a s : ℝ} (hs : 0 < s) {n i : ℕ} (hi : i < 2 ^ n) :
    Icc (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) ⊆ Icc a (a + s) := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hi' : (i : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hi
  have e : (2 : ℝ) ^ n * (s / 2 ^ n) = s := by field_simp
  refine Icc_subset_Icc ?_ ?_
  · have : 0 ≤ (i : ℝ) * (s / 2 ^ n) := by positivity
    linarith
  · have : ((i : ℝ) + 1) * (s / 2 ^ n) ≤ 2 ^ n * (s / 2 ^ n) := mul_le_mul_of_nonneg_right hi' (by positivity)
    linarith

/-- A closed dyadic subsquare with indices `i, j < 2ⁿ` lies in the closed square. -/
theorem closedDyadicSubsquare_subset {a b s : ℝ} (hs : 0 < s) {n i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    closedDyadicSubsquare a b s n i j ⊆ Icc a (a + s) ×ℂ Icc b (b + s) := fun _ hz =>
  Complex.mem_reProdIm.2 ⟨Icc_dyadic_subset hs hi (Complex.mem_reProdIm.1 hz).1,
    Icc_dyadic_subset hs hj (Complex.mem_reProdIm.1 hz).2⟩

/-- Two points of a closed dyadic subsquare of level `n` are at Euclidean distance at most `2 · 2⁻ⁿ s`. -/
theorem norm_sub_le_of_mem_closedDyadicSubsquare {a b s : ℝ} {n i j : ℕ} {z w : ℂ}
    (hz : z ∈ closedDyadicSubsquare a b s n i j) (hw : w ∈ closedDyadicSubsquare a b s n i j) :
    ‖z - w‖ ≤ 2 * (s / 2 ^ n) := by
  rw [closedDyadicSubsquare, Complex.mem_reProdIm] at hz hw
  have hi : ((i : ℝ) + 1) * (s / 2 ^ n) = i * (s / 2 ^ n) + s / 2 ^ n := by ring
  have hj : ((j : ℝ) + 1) * (s / 2 ^ n) = j * (s / 2 ^ n) + s / 2 ^ n := by ring
  have hre : |(z - w).re| ≤ s / 2 ^ n := by
    rw [Complex.sub_re, abs_sub_le_iff]
    constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have him : |(z - w).im| ≤ s / 2 ^ n := by
    rw [Complex.sub_im, abs_sub_le_iff]
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  linarith [Complex.norm_le_abs_re_add_abs_im (z - w)]

/-- Chaining from the coarsest scale: every point `z` of the closed square is at internal distance in the square at most
`∑_{n ≥ 1} L n` from some point of `X 0 0 0`. -/
theorem IsEuclideanLengthMetric.exists_internalMetric_le_of_dyadic_chain {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {a b s : ℝ} (hs : 0 < s) (X : ℕ → ℕ → ℕ → Set ℂ) (L : ℕ → ℝ≥0∞)
    (hXsub : ∀ n i j, i < 2 ^ n → j < 2 ^ n → X n i j ⊆ closedDyadicSubsquare a b s n i j)
    (hXdiam : ∀ n i j, i < 2 ^ n → j < 2 ^ n → ∀ x ∈ X n i j, ∀ y ∈ X n i j,
      internalMetric D (Icc a (a + s) ×ℂ Icc b (b + s)) x y ≤ L n)
    (hXmeet : ∀ n i j, i < 2 ^ (n + 1) → j < 2 ^ (n + 1) → (X n (i / 2) (j / 2) ∩ X (n + 1) i j).Nonempty)
    {z : ℂ} (hz : z ∈ Icc a (a + s) ×ℂ Icc b (b + s)) :
    ∃ x₀ ∈ X 0 0 0, internalMetric D (Icc a (a + s) ×ℂ Icc b (b + s)) x₀ z ≤ ∑' n, L (n + 1) := by
  set S := Icc a (a + s) ×ℂ Icc b (b + s) with hS
  have hz' := Complex.mem_reProdIm.1 hz
  set I : ℕ → ℕ := fun n => dyadicIndex ((z.re - a) / s) n with hI
  set J : ℕ → ℕ := fun n => dyadicIndex ((z.im - b) / s) n with hJ
  have hu0 : 0 ≤ (z.re - a) / s := div_nonneg (by linarith [hz'.1.1]) hs.le
  have hu1 : (z.re - a) / s ≤ 1 := (div_le_one hs).2 (by linarith [hz'.1.2])
  have hv0 : 0 ≤ (z.im - b) / s := div_nonneg (by linarith [hz'.2.1]) hs.le
  have hv1 : (z.im - b) / s ≤ 1 := (div_le_one hs).2 (by linarith [hz'.2.2])
  have hmeet : ∀ n, (X n (I n) (J n) ∩ X (n + 1) (I (n + 1)) (J (n + 1))).Nonempty := by
    intro n
    have h := hXmeet n (I (n + 1)) (J (n + 1)) (dyadicIndex_lt _ _) (dyadicIndex_lt _ _)
    rwa [hI, hJ, dyadicIndex_succ_div_two hu1, dyadicIndex_succ_div_two hv1] at h
  let x : ℕ → ℂ := fun n => (hmeet n).some
  have hx1 : ∀ n, x n ∈ X n (I n) (J n) := fun n => (hmeet n).some_mem.1
  have hx2 : ∀ n, x n ∈ X (n + 1) (I (n + 1)) (J (n + 1)) := fun n => (hmeet n).some_mem.2
  have hx00 : x 0 ∈ X 0 0 0 := by simpa [hI, hJ] using hx1 0
  have hx0S : x 0 ∈ S := by
    have := hXsub 0 0 0 (by norm_num) (by norm_num) hx00
    rwa [closedDyadicSubsquare_zero] at this
  have hdist : ∀ n, ‖x n - z‖ ≤ 2 * (s / 2 ^ n) := fun n =>
    norm_sub_le_of_mem_closedDyadicSubsquare
      (hXsub n (I n) (J n) (dyadicIndex_lt _ _) (dyadicIndex_lt _ _) (hx1 n))
      (mem_closedDyadicSubsquare_dyadicIndex hs hz n)
  have hlim : Tendsto (fun n : ℕ => 2 * (s / 2 ^ n)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := s)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2))).const_mul (2 : ℝ)
  have hx : Tendsto x atTop (𝓝 z) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hdist hlim)
  refine ⟨x 0, hx00, ?_⟩
  refine hD.internalMetric_le_tsum_of_tendsto_of_isClosed_of_le (isClosed_Icc.reProdIm isClosed_Icc)
    ((isCompact_Icc.reProdIm isCompact_Icc).isBounded) hx0S hz hx fun n => ?_
  exact hXdiam (n + 1) (I (n + 1)) (J (n + 1)) (dyadicIndex_lt _ _) (dyadicIndex_lt _ _) _ (hx2 n) _ (hx1 (n + 1))

/-- The multiscale bound for the internal diameter of a closed square in its own internal metric: if each closed dyadic
subsquare of level `n` carries a set of internal diameter in the square at most `L n`, contained in the subsquare and
meeting the set of the parent subsquare, then any two points of the square are at internal distance in the square at
most `L 0 + 2 ∑_{n ≥ 1} L n`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_dyadic_chain {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {a b s : ℝ} (hs : 0 < s) (X : ℕ → ℕ → ℕ → Set ℂ) (L : ℕ → ℝ≥0∞)
    (hXsub : ∀ n i j, i < 2 ^ n → j < 2 ^ n → X n i j ⊆ closedDyadicSubsquare a b s n i j)
    (hXdiam : ∀ n i j, i < 2 ^ n → j < 2 ^ n → ∀ x ∈ X n i j, ∀ y ∈ X n i j,
      internalMetric D (Icc a (a + s) ×ℂ Icc b (b + s)) x y ≤ L n)
    (hXmeet : ∀ n i j, i < 2 ^ (n + 1) → j < 2 ^ (n + 1) → (X n (i / 2) (j / 2) ∩ X (n + 1) i j).Nonempty)
    {z w : ℂ} (hz : z ∈ Icc a (a + s) ×ℂ Icc b (b + s)) (hw : w ∈ Icc a (a + s) ×ℂ Icc b (b + s)) :
    internalMetric D (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ L 0 + 2 * ∑' n, L (n + 1) := by
  obtain ⟨x₀, hx₀, hxz⟩ := hD.exists_internalMetric_le_of_dyadic_chain hs X L hXsub hXdiam hXmeet hz
  obtain ⟨y₀, hy₀, hyw⟩ := hD.exists_internalMetric_le_of_dyadic_chain hs X L hXsub hXdiam hXmeet hw
  have hxy := hXdiam 0 0 0 (by norm_num) (by norm_num) x₀ hx₀ y₀ hy₀
  calc internalMetric D _ z w
      ≤ internalMetric D _ z x₀ + internalMetric D _ x₀ w := hD.internalMetric_triangle _ _ _ _
    _ ≤ internalMetric D _ z x₀ + (internalMetric D _ x₀ y₀ + internalMetric D _ y₀ w) :=
        add_le_add le_rfl (hD.internalMetric_triangle _ _ _ _)
    _ ≤ ∑' n, L (n + 1) + (L 0 + ∑' n, L (n + 1)) := by
        rw [hD.internalMetric_symm _ z x₀]
        exact add_le_add hxz (add_le_add hxy hyw)
    _ = L 0 + 2 * ∑' n, L (n + 1) := by ring

end LatticeProb.LQG
