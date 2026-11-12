/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.Midpoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Approximate midpoints and length spaces (Menger's lemma)

* `IsApproxMidpoint ε x y z`: `z` is an `ε`-midpoint between `x` and `y`, i.e.
  `d(x, z) ≤ d(x, y)/2 + ε` and `d(y, z) ≤ d(x, y)/2 + ε` (Petrunin's definition).
* `isLengthSpace_of_hasApproxMidpoints`: a complete metric space in which any two points have an
  `ε`-midpoint for every `ε > 0` is a length space (BBI Thm 2.4.16(2); Petrunin, Menger's lemma).
* `exists_pathLength_le_of_hasMidpoints`: if any two points have an exact midpoint, any two points
  are joined by a path of length `≤ d(x, y)` (BBI Thm 2.4.16(1): "strictly intrinsic").
* `hasApproxMidpoints_of_isLengthSpace`: conversely, a length space has `ε`-midpoints
  (BBI Lemma 2.4.10). Hence `isLengthSpace_iff_hasApproxMidpoints` for complete spaces.

Sources: Petrunin, *Pure metric geometry* (arXiv:2007.09846), `metric.tex` l. 559–624
(definition of `ε`-midpoints and Menger's lemma `lem:mid>geod` with proof); Burago–Burago–Ivanov,
*A course in metric geometry* (2001), §2.4.3–2.4.4, Lemma 2.4.10, Theorem 2.4.16,
Corollary 2.4.17 (PDF pp. 50–52).

Proof of Menger's lemma (Petrunin's): with `εₙ = ε/4ⁿ`, define `α` on the dyadic points
`k/2ⁿ` by taking `εₙ`-midpoints of the already defined neighbours; then `α` is
`(d(x,y)+ε)`-Lipschitz on dyadics and extends by completeness. Lean route: the level-`n` points
`g n k` (`k ≤ 2ⁿ`) have consecutive distances `≤ (d(x,y)+ε)/2ⁿ`; for `t ∈ [0,1]` the sequence
`g n ⌊t 2ⁿ⌋` is Cauchy (geometric), its limit `α t` is within `(d(x,y)+ε)/2ⁿ` of it, and the
Lipschitz bound follows from the triangle inequality at level `n` as `n → ∞` (this replaces the
extension-from-dyadics step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology
open scoped ENNReal NNReal

namespace LQGMetric.MetricGeometry

section Defs

variable {X : Type*} [PseudoMetricSpace X]

/-- `z` is an `ε`-midpoint between `x` and `y` (Petrunin, *Pure metric geometry*, `metric.tex`
l. 566; BBI Lemma 2.4.10 uses the equivalent two-sided form). -/
def IsApproxMidpoint (ε : ℝ) (x y z : X) : Prop :=
  dist x z ≤ dist x y / 2 + ε ∧ dist y z ≤ dist x y / 2 + ε

/-- Any two points have an `ε`-midpoint for every `ε > 0`. -/
def HasApproxMidpoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ z, IsApproxMidpoint ε x y z

/-- **BBI Lemma 2.4.10**: a length space has `ε`-midpoints. -/
theorem hasApproxMidpoints_of_isLengthSpace (hX : IsLengthSpace X) : HasApproxMidpoints X := by
  intro x y ε hε
  obtain ⟨γ, hγ⟩ := hX x y ε hε
  set D := dist x y
  have hf : ContinuousOn (fun t => dist x (γ.extend t)) (Icc 0 1) :=
    (continuous_const.dist γ.continuous_extend).continuousOn
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hf
    (show D / 2 ∈ Icc (dist x (γ.extend 0)) (dist x (γ.extend 1)) by
      simp only [Path.extend_zero, Path.extend_one, dist_self]
      exact ⟨by positivity, by linarith [dist_nonneg (x := x) (y := y)]⟩)
  refine ⟨γ.extend t, le_add_of_le_of_nonneg (le_of_eq hft) hε.le, ?_⟩
  simp only at hft
  have h1 := edist_le_curveLength γ.extend ht.1
  have h2 := edist_le_curveLength γ.extend ht.2
  rw [Path.extend_zero] at h1
  rw [Path.extend_one] at h2
  have hsum : edist x (γ.extend t) + edist (γ.extend t) y ≤ edist x y + ENNReal.ofReal ε := by
    refine (add_le_add h1 h2).trans ?_
    rw [curveLength_add _ ht.1 ht.2]
    exact hγ
  rw [edist_dist, edist_dist, edist_dist, hft, ← ENNReal.ofReal_add dist_nonneg hε.le,
    show D + ε = D / 2 + (D / 2 + ε) by ring,
    ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  have := (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 hsum
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  rwa [dist_comm]

end Defs

section Dyadic

variable {X : Type*}

/-- The level-`n` dyadic points of Petrunin's construction, for a midpoint selector `m`
(`m n a b` is the point chosen between `a` and `b` at level `n + 1`). -/
def dyadicPts (x y : X) (m : ℕ → X → X → X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then dyadicPts x y m n (k / 2)
      else m n (dyadicPts x y m n (k / 2)) (dyadicPts x y m n (k / 2 + 1))

variable {x y : X} {m : ℕ → X → X → X}

theorem dyadicPts_zero (n : ℕ) : dyadicPts x y m n 0 = x := by
  induction n with
  | zero => simp [dyadicPts]
  | succ n ih => simp [dyadicPts, ih]

theorem dyadicPts_two_pow (n : ℕ) : dyadicPts x y m n (2 ^ n) = y := by
  induction n with
  | zero => simp [dyadicPts]
  | succ n ih =>
    simp only [dyadicPts, pow_succ, Nat.mul_mod_left, ite_true]
    rwa [Nat.mul_div_cancel _ two_pos]

theorem dyadicPts_two_mul (n k : ℕ) : dyadicPts x y m (n + 1) (2 * k) = dyadicPts x y m n k := by
  simp [dyadicPts]

theorem dyadicPts_two_mul_add_one (n k : ℕ) : dyadicPts x y m (n + 1) (2 * k + 1) =
    m n (dyadicPts x y m n k) (dyadicPts x y m n (k + 1)) := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [dyadicPts, h1, h2]

/-- Consecutive level-`n` points are `≤ (d(x,y) + ε)/2ⁿ − ε/4ⁿ` apart. -/
theorem dist_dyadicPts_succ_le [PseudoMetricSpace X] {ε : ℝ}
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b)) :
    ∀ n k, k < 2 ^ n → dist (dyadicPts x y m n k) (dyadicPts x y m n (k + 1)) ≤
      (dist x y + ε) / 2 ^ n - ε / ((2 : ℝ) ^ n) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by simpa using hk
    simp [dyadicPts]
  | succ n ih =>
    intro k hk
    have key : ∀ j, j < 2 ^ n → ∀ w z : X, dist w z ≤
        dist (dyadicPts x y m n j) (dyadicPts x y m n (j + 1)) / 2 +
          ε / (4 * ((2 : ℝ) ^ n) ^ 2) →
        dist w z ≤ (dist x y + ε) / 2 ^ (n + 1) - ε / ((2 : ℝ) ^ (n + 1)) ^ 2 := by
      intro j hj w z hz
      refine hz.trans (le_of_le_of_eq (add_le_add_left (div_le_div_of_nonneg_right
        (ih j hj) two_pos.le) _) ?_)
      rw [pow_succ]
      field_simp
      ring
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hj : j < 2 ^ n := by rw [pow_succ] at hk; omega
      rw [dyadicPts_two_mul, dyadicPts_two_mul_add_one]
      exact key j hj _ _ (hm n _ _).1
    · have hj : j < 2 ^ n := by rw [pow_succ] at hk; omega
      rw [dyadicPts_two_mul_add_one, show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
        dyadicPts_two_mul, dist_comm]
      exact key j hj _ _ (hm n _ _).2
variable [PseudoMetricSpace X] {ε : ℝ}

theorem dist_dyadicPts_succ_le' (hε : 0 ≤ ε)
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b))
    (n k : ℕ) (hk : k < 2 ^ n) :
    dist (dyadicPts x y m n k) (dyadicPts x y m n (k + 1)) ≤ (dist x y + ε) / 2 ^ n :=
  (dist_dyadicPts_succ_le hm n k hk).trans (sub_le_self _ (by positivity))

/-- Triangle inequality along level `n`: `d(g n k, g n l) ≤ (l − k)(d(x,y)+ε)/2ⁿ`. -/
theorem dist_dyadicPts_le (hε : 0 ≤ ε)
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b))
    (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ 2 ^ n) :
    dist (dyadicPts x y m n k) (dyadicPts x y m n l) ≤
      ((l : ℝ) - k) * ((dist x y + ε) / 2 ^ n) := by
  refine (dist_le_Ico_sum_dist (dyadicPts x y m n) hkl).trans ?_
  calc ∑ i ∈ Finset.Ico k l, dist (dyadicPts x y m n i) (dyadicPts x y m n (i + 1))
      ≤ ∑ _i ∈ Finset.Ico k l, (dist x y + ε) / 2 ^ n :=
        Finset.sum_le_sum fun i hi =>
          dist_dyadicPts_succ_le' hε hm n i (by simp only [Finset.mem_Ico] at hi; omega)
    _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hkl]

end Dyadic

theorem floor_two_mul_eq_or (a : ℝ) (ha : 0 ≤ a) :
    ⌊2 * a⌋₊ = 2 * ⌊a⌋₊ ∨ ⌊2 * a⌋₊ = 2 * ⌊a⌋₊ + 1 := by
  have h1 : 2 * ⌊a⌋₊ ≤ ⌊2 * a⌋₊ := Nat.le_floor (by push_cast; linarith [Nat.floor_le ha])
  have h2 : ⌊2 * a⌋₊ < 2 * ⌊a⌋₊ + 2 :=
    (Nat.floor_lt (by positivity)).2 (by push_cast; linarith [Nat.lt_floor_add_one a])
  omega

theorem floor_mul_two_pow_le {t : ℝ} (ht : t ≤ 1) (n : ℕ) : ⌊t * 2 ^ n⌋₊ ≤ 2 ^ n :=
  Nat.floor_le_of_le (by push_cast; have := pow_pos (two_pos (α := ℝ)) n; nlinarith)

section Menger

variable {X : Type*} [MetricSpace X] {x y : X} {m : ℕ → X → X → X} {ε : ℝ}

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

/-- **Core of Menger's lemma** (Petrunin, `metric.tex` l. 596–613): with `εₙ`-midpoints,
`εₙ = ε/4ⁿ`, there is a `(d(x,y)+ε)`-Lipschitz curve `[0,1] → X` from `x` to `y`. -/
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

/-- A curve that is `C`-Lipschitz on `[0, 1]` has length at most `C`. -/
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

/-- **Menger's lemma, approximate form** (BBI Thm 2.4.16(2); Petrunin, `lem:mid>length`): a
complete metric space with `ε`-midpoints for all `ε > 0` is a length space. -/
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

end LQGMetric.MetricGeometry
