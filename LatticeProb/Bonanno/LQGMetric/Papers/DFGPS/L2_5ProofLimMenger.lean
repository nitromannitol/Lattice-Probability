/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLimMenger at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.Midpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Menger's lemma with midpoints only for "good" pairs

Variant of `MetricGeometry.exists_lipschitz_curve_of_midpoints` (Petrunin, *Pure metric
geometry*, arXiv:2007.09846, `metric.tex` l. 596–613; Burago–Burago–Ivanov, Thm 2.4.16(1)):
in a complete metric space, if the pairs `(a, b)` satisfying a predicate `G` have a midpoint `z`
with `G a z` and `G z b`, then any `G`-pair `(x, y)` is joined by a `d(x,y)`-Lipschitz curve
`[0,1] → X`. The proof is Petrunin's dyadic construction (as in `Midpoint.lean`), where the
midpoint hypothesis is only used along the dyadic points, which stay `G`-pairs. Used for the
length property of the limits in DFGPS Lemma 2.5 A (arXiv:1905.00380, T:1005–1012), where
midpoints are available only for pairs which are closer than the distance to `∂S_{Rr}(0)`.
-/

open Set Filter Topology

namespace LQGMetric.DFGPS

open MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- dyadic Lipschitz curve from an abstract dyadic family with geometric consecutive bounds -/
theorem exists_lipschitz_curve_of_dyadic [CompleteSpace X] {x y : X} (g : ℕ → ℕ → X) {C : ℝ}
    (hC0 : 0 ≤ C) (h0 : ∀ n, g n 0 = x) (h1 : ∀ n, g n (2 ^ n) = y)
    (h2 : ∀ n k, g (n + 1) (2 * k) = g n k)
    (hcons : ∀ n k, k < 2 ^ n → dist (g n k) (g n (k + 1)) ≤ C / 2 ^ n) :
    ∃ P : ℝ → X, P 0 = x ∧ P 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ C * dist s t := by
  have hlevel : ∀ n {k l : ℕ}, k ≤ l → l ≤ 2 ^ n →
      dist (g n k) (g n l) ≤ ((l : ℝ) - k) * (C / 2 ^ n) := by
    intro n k l hkl hl
    refine (dist_le_Ico_sum_dist (g n) hkl).trans ?_
    calc ∑ i ∈ Finset.Ico k l, dist (g n i) (g n (i + 1))
        ≤ ∑ _i ∈ Finset.Ico k l, C / 2 ^ n :=
          Finset.sum_le_sum fun i hi =>
            hcons n i (by simp only [Finset.mem_Ico] at hi; omega)
      _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hkl]
  have hfloor : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ n : ℕ,
      dist (g n ⌊t * 2 ^ n⌋₊) (g (n + 1) ⌊t * 2 ^ (n + 1)⌋₊) ≤ C / 2 / 2 ^ n := by
    intro t ht0 ht1 n
    have hfl : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
    have hle := floor_mul_two_pow_le ht1 (n + 1)
    rw [hfl] at hle ⊢
    rcases floor_two_mul_eq_or (t * 2 ^ n) (by positivity) with h | h <;> rw [h] <;>
      rw [h] at hle
    · rw [h2, dist_self]; positivity
    · rw [← h2 n ⌊t * 2 ^ n⌋₊]
      refine (hcons (n + 1) _ (by omega)).trans (le_of_eq ?_)
      rw [pow_succ]; ring
  have : Nonempty X := ⟨x⟩
  set u : ℝ → ℕ → X := fun t n => g n ⌊t * 2 ^ n⌋₊ with hu
  have hstep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ n, dist (u t n) (u t (n + 1)) ≤ C / 2 / 2 ^ n :=
    fun t ht n => hfloor t ht.1 ht.2 n
  have hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∃ a, Tendsto (u t) atTop (𝓝 a) := fun t ht =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hstep t ht))
  choose! P hP using hlim
  have hPn : ∀ t ∈ Icc (0 : ℝ) 1, ∀ n, dist (u t n) (P t) ≤ C / 2 ^ n := fun t ht n =>
    dist_le_of_le_geometric_two_of_tendsto (hstep t ht) (hP t ht) n
  refine ⟨P, ?_, ?_, ?_⟩
  · have : Tendsto (u 0) atTop (𝓝 x) := by
      simp only [hu, zero_mul, Nat.floor_zero, h0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hP 0 ⟨le_rfl, zero_le_one⟩) this
  · have hy : ∀ n, u 1 n = y := fun n => by
      show g n ⌊(1 : ℝ) * 2 ^ n⌋₊ = y
      rw [one_mul, show ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast,
        h1]
    have : Tendsto (u 1) atTop (𝓝 y) := by
      rw [show u 1 = fun _ => y from funext hy]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hP 1 ⟨zero_le_one, le_rfl⟩) this
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      dist (P s) (P t) ≤ C * (t - s) := by
    intro s hs t ht hst
    have hn : ∀ n : ℕ, dist (P s) (P t) ≤ C * (t - s) + 3 * (C / 2 ^ n) := by
      intro n
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      have hks : ⌊s * 2 ^ n⌋₊ ≤ ⌊t * 2 ^ n⌋₊ := Nat.floor_le_floor (by gcongr)
      have hlev := hlevel n hks (floor_mul_two_pow_le ht.2 n)
      have h1' : (⌊t * 2 ^ n⌋₊ : ℝ) ≤ t * 2 ^ n := Nat.floor_le (by have := ht.1; positivity)
      have h2' : s * 2 ^ n < ⌊s * 2 ^ n⌋₊ + 1 := Nat.lt_floor_add_one _
      have h3 : ((⌊t * 2 ^ n⌋₊ : ℝ) - ⌊s * 2 ^ n⌋₊) * (C / 2 ^ n) ≤ C * (t - s) + C / 2 ^ n :=
        calc _ ≤ ((t - s) * 2 ^ n + 1) * (C / 2 ^ n) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = C * (t - s) + C / 2 ^ n := by field_simp
      have h4 := dist_triangle4 (P s) (u s n) (u t n) (P t)
      have h5 := hPn s hs n
      have h6 := hPn t ht n
      rw [dist_comm] at h5
      simp only [hu] at h4 h5 h6
      linarith
    have hlim : Tendsto (fun n : ℕ => C * (t - s) + 3 * (C / 2 ^ n)) atTop
        (𝓝 (C * (t - s))) := by
      have : Tendsto (fun n : ℕ => C / 2 ^ n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
      simpa using (this.const_mul 3).const_add (C * (t - s))
    exact ge_of_tendsto' hlim hn
  intro s hs t ht
  rcases le_total s t with hst | hst
  · rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]; exact key s hs t ht hst
  · rw [dist_comm, Real.dist_eq, abs_of_nonneg (by linarith)]; exact key t ht s hs hst

/-- **Menger's lemma for good pairs**: midpoints for `G`-pairs, inherited by both halves, give a
`d(x,y)`-Lipschitz curve between any `G`-pair. -/
theorem exists_lipschitz_curve_of_goodMid [CompleteSpace X] (G : X → X → Prop)
    (hmid : ∀ a b, G a b → ∃ z, dist a z ≤ dist a b / 2 ∧ dist z b ≤ dist a b / 2 ∧
      G a z ∧ G z b) {x y : X} (hxy : G x y) :
    ∃ P : ℝ → X, P 0 = x ∧ P 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ dist x y * dist s t := by
  classical
  let mid : X → X → X := fun a b => if hab : G a b then (hmid a b hab).choose else a
  have hm : ∀ a b, G a b → dist a (mid a b) ≤ dist a b / 2 ∧ dist (mid a b) b ≤ dist a b / 2 ∧
      G a (mid a b) ∧ G (mid a b) b := fun a b hab => by
    simp only [mid, dif_pos hab]; exact (hmid a b hab).choose_spec
  set g := dyadicPts x y (fun _ => mid)
  have hg2 : ∀ n k, g (n + 1) (2 * k) = g n k := fun n k => dyadicPts_two_mul n k
  have hg21 : ∀ n k, g (n + 1) (2 * k + 1) = mid (g n k) (g n (k + 1)) := fun n k =>
    dyadicPts_two_mul_add_one n k
  have hind : ∀ n k, k < 2 ^ n → G (g n k) (g n (k + 1)) ∧
      dist (g n k) (g n (k + 1)) ≤ dist x y / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro k hk
      obtain rfl : k = 0 := by simpa using hk
      simp only [g, dyadicPts, if_pos, pow_zero, div_one, zero_add, one_ne_zero, if_false]
      exact ⟨hxy, le_rfl⟩
    | succ n ih =>
      intro k hk
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · have hj : j < 2 ^ n := by rw [pow_succ] at hk; omega
        obtain ⟨hG, hd⟩ := ih j hj
        obtain ⟨h1, -, h3, -⟩ := hm _ _ hG
        rw [hg2, hg21]
        refine ⟨h3, h1.trans ?_⟩
        rw [pow_succ, ← div_div]; gcongr
      · have hj : j < 2 ^ n := by rw [pow_succ] at hk; omega
        obtain ⟨hG, hd⟩ := ih j hj
        obtain ⟨-, h2, -, h4⟩ := hm _ _ hG
        rw [hg21, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hg2]
        refine ⟨h4, h2.trans ?_⟩
        rw [pow_succ, ← div_div]; gcongr
  exact exists_lipschitz_curve_of_dyadic g dist_nonneg (fun n => dyadicPts_zero n)
    (fun n => dyadicPts_two_pow n) (fun n k => dyadicPts_two_mul n k)
    (fun n k hk => (hind n k hk).2)

end LQGMetric.DFGPS
