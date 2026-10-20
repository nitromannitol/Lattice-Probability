/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/Midpoint.lean.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Topology.Length.Midpoint
import LatticeProb.Topology.Length.VariationCompat

/-!
# Menger's lemma: length spaces from approximate midpoints

A complete metric space in which any two points have an `ε`-midpoint for every `ε > 0` is a length
space (Burago–Burago–Ivanov, Thm. 2.4.16(2)). The proof builds, for each pair of points, a curve on `[0, 1]` from the
dyadic midpoint construction of `LatticeProb.Topology.Length.Midpoint`: the dyadic points at level
`n` are `(d(x, y) + ε) / 2ⁿ`-close consecutively, the limit along each `t` exists by completeness,
and the resulting curve is `(d(x, y) + ε)`-Lipschitz on `[0, 1]`, so its length is at most
`d(x, y) + ε`.

* `dist_dyadicPts_floor_succ_le`: consecutive level-`n` dyadic points near `⌊t 2ⁿ⌋` are
  `(d(x, y) + ε) / 2 / 2ⁿ`-close.
* `exists_lipschitz_curve_of_midpoints`: with `ε / 4ⁿ`-midpoints, there is a
  `(d(x, y) + ε)`-Lipschitz curve `[0, 1] → X` from `x` to `y`.
* `curveLength_le_of_dist_le_mul`: a `C`-Lipschitz curve on `[0, 1]` is continuous and has length
  at most `C`.
* `isLengthSpace_of_hasApproxMidpoints`: Menger's lemma, approximate form.

Sources: Burago–Burago–Ivanov, *A course in metric geometry* (2001), Theorem 2.4.16(2); Petrunin,
*Pure metric geometry* (arXiv:2007.09846), the definition of `ε`-midpoints.
-/

open Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.MetricGeometry

section Menger

variable {X : Type*} [MetricSpace X] {x y : X} {m : ℕ → X → X → X} {ε : ℝ}

/-- Consecutive level-`n` dyadic points at the indices `⌊t 2ⁿ⌋` and `⌊t 2ⁿ⁺¹⌋` are at most
`(d(x, y) + ε) / 2 / 2ⁿ` apart, for `t ∈ [0, 1]`, when the selector `m` chooses
`ε / (4 · 4ⁿ)`-midpoints at level `n`. -/
theorem dist_dyadicPts_floor_succ_le (hε : 0 ≤ ε)
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    dist (dyadicPts x y m n ⌊t * 2 ^ n⌋₊) (dyadicPts x y m (n + 1) ⌊t * 2 ^ (n + 1)⌋₊) ≤
      (dist x y + ε) / 2 / 2 ^ n := by
  have hfl : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
  have hC : 0 ≤ dist x y + ε := add_nonneg dist_nonneg hε
  have hle := floor_mul_two_pow_le ht1 (n + 1)
  rw [hfl] at hle ⊢
  rcases floor_two_mul_eq_or (t * 2 ^ n) (by positivity) with h | h <;> rw [h] <;> rw [h] at hle
  · rw [dyadicPts_two_mul, dist_self]; positivity
  · rw [← dyadicPts_two_mul (m := m) (x := x) (y := y) n ⌊t * 2 ^ n⌋₊]
    refine (dist_dyadicPts_succ_le' hε hm (n + 1) _ (by omega)).trans (le_of_eq ?_)
    rw [pow_succ]; ring

/-- **Core of Menger's lemma**: in a complete metric space, if for every `n` any two points have an
`ε / (4 · 4ⁿ)`-midpoint, then there is a `(d(x, y) + ε)`-Lipschitz curve `P : ℝ → X` with
`P 0 = x` and `P 1 = y`. -/
theorem exists_lipschitz_curve_of_midpoints [CompleteSpace X] (x y : X) (hε : 0 ≤ ε)
    (hm : ∀ (n : ℕ) (a b : X), ∃ z, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b z) :
    ∃ P : ℝ → X, P 0 = x ∧ P 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ (dist x y + ε) * dist s t := by
  choose m hm using hm
  have : Nonempty X := ⟨x⟩
  set C := dist x y + ε with hC
  have hC0 : 0 ≤ C := add_nonneg dist_nonneg hε
  set u : ℝ → ℕ → X := fun t n => dyadicPts x y m n ⌊t * 2 ^ n⌋₊ with hu
  have hstep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ n, dist (u t n) (u t (n + 1)) ≤ C / 2 / 2 ^ n :=
    fun t ht n => dist_dyadicPts_floor_succ_le hε hm ht.1 ht.2 n
  have hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∃ a, Tendsto (u t) atTop (𝓝 a) := fun t ht =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hstep t ht))
  choose! P hP using hlim
  have hPn : ∀ t ∈ Icc (0 : ℝ) 1, ∀ n, dist (u t n) (P t) ≤ C / 2 ^ n := fun t ht n =>
    dist_le_of_le_geometric_two_of_tendsto (hstep t ht) (hP t ht) n
  refine ⟨P, ?_, ?_, ?_⟩
  · have : Tendsto (u 0) atTop (𝓝 x) := by
      simp only [hu, zero_mul, Nat.floor_zero, dyadicPts_zero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hP 0 ⟨le_rfl, zero_le_one⟩) this
  · have hy : ∀ n, u 1 n = y := fun n => by
      show dyadicPts x y m n ⌊(1 : ℝ) * 2 ^ n⌋₊ = y
      rw [one_mul, show ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast,
        dyadicPts_two_pow]
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
      have hlev := dist_dyadicPts_le (x := x) (y := y) hε hm n hks (floor_mul_two_pow_le ht.2 n)
      have h1 : (⌊t * 2 ^ n⌋₊ : ℝ) ≤ t * 2 ^ n := Nat.floor_le (by have := ht.1; positivity)
      have h2 : s * 2 ^ n < ⌊s * 2 ^ n⌋₊ + 1 := Nat.lt_floor_add_one _
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
    have hlim : Tendsto (fun n : ℕ => C * (t - s) + 3 * (C / 2 ^ n)) atTop (𝓝 (C * (t - s))) := by
      have : Tendsto (fun n : ℕ => C / 2 ^ n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
      simpa using (this.const_mul 3).const_add (C * (t - s))
    exact ge_of_tendsto' hlim hn
  intro s hs t ht
  rcases le_total s t with hst | hst
  · rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]; exact key s hs t ht hst
  · rw [dist_comm, Real.dist_eq, abs_of_nonneg (by linarith)]; exact key t ht s hs hst

/-- A curve `P : ℝ → X` that is `C`-Lipschitz on `[0, 1]` (with `0 ≤ C`) is continuous on
`[0, 1]` and has length `curveLength P 0 1` at most `ENNReal.ofReal C`. -/
theorem curveLength_le_of_dist_le_mul {P : ℝ → X} {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ C * dist s t) :
    ContinuousOn P (Icc 0 1) ∧ curveLength P 0 1 ≤ ENNReal.ofReal C := by
  have hL : LipschitzOnWith C.toNNReal P (Icc 0 1) :=
    LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
      rw [Real.coe_toNNReal _ hC]; exact hP s hs t ht
  refine ⟨hL.continuousOn, ?_⟩
  calc curveLength P 0 1 = eVariationOn (P ∘ id) (Icc 0 1) := rfl
    _ ≤ C.toNNReal * eVariationOn id (Icc (0 : ℝ) 1) := hL.comp_eVariationOn_le (mapsTo_id _)
    _ = ENNReal.ofReal C := by rw [eVariationOn_id_Icc]; simp [ENNReal.ofReal]

/-- **Menger's lemma, approximate form** (Burago–Burago–Ivanov, Thm. 2.4.16(2)): a complete metric space with
`ε`-midpoints for all `ε > 0` is a length space. The hypotheses are `[CompleteSpace X]` and
`h : HasApproxMidpoints X`, i.e. any two points `x, y` have an `ε`-midpoint for every `ε > 0`. -/
theorem isLengthSpace_of_hasApproxMidpoints [CompleteSpace X] (h : HasApproxMidpoints X) :
    IsLengthSpace X := by
  rw [isLengthSpace_iff_curves]
  intro x y ε hε
  obtain ⟨P, h0, h1, hP⟩ := exists_lipschitz_curve_of_midpoints x y hε.le
    (fun n a b => h a b _ (by positivity))
  obtain ⟨hc, hlen⟩ := curveLength_le_of_dist_le_mul (add_nonneg dist_nonneg hε.le) hP
  refine ⟨P, 0, 1, zero_le_one, hc, h0, h1, hlen.trans_eq ?_⟩
  rw [ENNReal.ofReal_add dist_nonneg hε.le, edist_dist]

end Menger

/-! ### Nonvacuity examples -/

namespace MengerExample

/-- `ℝ` is a length space: the hypotheses of `isLengthSpace_of_hasApproxMidpoints` hold on `ℝ`,
with the midpoint `(x + y) / 2`. -/
example : IsLengthSpace ℝ :=
  isLengthSpace_of_hasApproxMidpoints
    (fun x y ε hε => ⟨(x + y) / 2, MidpointExample.isApproxMidpoint_real_midpoint ε hε.le x y⟩)

/-- The hypothesis of `exists_lipschitz_curve_of_midpoints` holds on `ℝ`, with selector
`(a + b) / 2`, so the Lipschitz curve from `x` to `y` exists for `ℝ`. -/
example (x y ε : ℝ) (hε : 0 ≤ ε) :
    ∃ P : ℝ → ℝ, P 0 = x ∧ P 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ (dist x y + ε) * dist s t :=
  exists_lipschitz_curve_of_midpoints x y hε fun n a b =>
    ⟨(a + b) / 2, MidpointExample.isApproxMidpoint_real_midpoint
      (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) (div_nonneg hε (by positivity)) a b⟩

end MengerExample

end LatticeProb.MetricGeometry
