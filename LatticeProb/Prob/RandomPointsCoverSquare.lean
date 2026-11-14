import Mathlib
import LatticeProb.Euclidean.ParentBlock

/-!
# Independent uniform points cover a square at a fixed relative scale

For `δ > 0` there is `N₀` such that, for every `N ≥ N₀` and every closed axis-parallel square `Q`
of side `a > 0`, `N` independent points sampled uniformly from `Q` form, with probability at least
`1 - δ`, a `δ a`-net of `Q`: `Q ⊆ ⋃ j, ball (z j) (δ a)`.  The number `N₀` depends on `δ` only.

This is the covering step in the proof that the exit distribution of a random walk in a random
environment from a square approaches Euclidean harmonic measure uniformly in the starting point
(Gwynne-Miller-Sheffield, *An invariance principle for ergodic scale-free random environments*,
proof of Lemma 3.14, condition 2).

Proof: cut `Q` into `M × M` closed cells of side `a / M` with `2 / M < δ`.  If every cell contains
a sample point, the samples form a `δ a`-net, and a given cell is missed by all `N` points with
probability `(1 - M⁻²) ^ N`, whatever the square.

## Main results

* `measure_pi_not_subset_iUnion_ball_le`: abstract union bound for random nets.
* `volume_closedSquare`: Lebesgue measure of a closed square.
* `exists_measure_pi_not_subset_iUnion_ball_le`: the bad event has probability at most `δ`.
* `exists_le_measure_pi_subset_iUnion_ball`: the covering event has probability at least `1 - δ`.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LatticeProb.RandomPointsCover

open LatticeProb.ParentBlock

/-- **Random nets, abstract union bound.**  If `Q` is covered by the sets `A i`, `i ∈ s`, each of
which has all its pairwise distances below `r`, then the probability that `N` independent
`μ`-distributed points fail to form an `r`-net of `Q` is at most `∑ i ∈ s, μ (A i)ᶜ ^ N`. -/
theorem measure_pi_not_subset_iUnion_ball_le {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {ι : Type*} (s : Finset ι)
    (A : ι → Set α) (Q : Set α) (r : ℝ) (hQ : Q ⊆ ⋃ i ∈ s, A i)
    (hA : ∀ i ∈ s, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < r) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ) {z | ¬ Q ⊆ ⋃ j, ball (z j) r} ≤
      ∑ i ∈ s, μ (A i)ᶜ ^ N := by
  have hsub : {z : Fin N → α | ¬ Q ⊆ ⋃ j, ball (z j) r} ⊆
      ⋃ i ∈ s, Set.pi univ (fun _ : Fin N => (A i)ᶜ) := by
    intro z hz
    obtain ⟨q, hqQ, hq⟩ := Set.not_subset.1 hz
    obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.1 (hQ hqQ)
    refine mem_iUnion₂.2 ⟨i, hi, Set.mem_univ_pi.2 fun j hzj => hq (mem_iUnion.2 ⟨j, ?_⟩)⟩
    exact mem_ball.2 (hA i hi q hqi (z j) hzj)
  calc Measure.pi (fun _ : Fin N => μ) {z | ¬ Q ⊆ ⋃ j, ball (z j) r}
      ≤ Measure.pi (fun _ : Fin N => μ) (⋃ i ∈ s, Set.pi univ fun _ : Fin N => (A i)ᶜ) :=
        measure_mono hsub
    _ ≤ ∑ i ∈ s, Measure.pi (fun _ : Fin N => μ) (Set.pi univ fun _ : Fin N => (A i)ᶜ) :=
        measure_biUnion_finset_le s _
    _ = ∑ i ∈ s, μ (A i)ᶜ ^ N := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Lebesgue measure of the closed square of centre `c` and side `a ≥ 0`. -/
theorem volume_closedSquare (c : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    volume (closedSquare c a) = ENNReal.ofReal (a * a) := by
  have h : closedSquare c a = Complex.measurableEquivRealProd ⁻¹'
      (Icc (c.re - a / 2) (c.re + a / 2) ×ˢ Icc (c.im - a / 2) (c.im + a / 2)) := by
    ext z
    simp only [closedSquare, Set.mem_ofPred_eq, Set.mem_preimage,
      Complex.measurableEquivRealProd_apply, Set.mem_prod, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

/-- The uniform distribution on a nondegenerate closed square is a probability measure. -/
theorem isProbabilityMeasure_cond_closedSquare (c : ℂ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (volume[|closedSquare c a]) :=
  cond_isProbabilityMeasure_of_finite
    (by rw [volume_closedSquare c ha.le]; exact (ENNReal.ofReal_pos.2 (mul_pos ha ha)).ne')
    (by rw [volume_closedSquare c ha.le]; exact ENNReal.ofReal_ne_top)

/-- Centre of the cell `(i, k)` of the subdivision of `closedSquare c a` into `M × M` closed
cells of side `a / M`. -/
noncomputable def cellCentre (c : ℂ) (a : ℝ) (M i k : ℕ) : ℂ :=
  ⟨c.re - a / 2 + (i + 1 / 2) * (a / M), c.im - a / 2 + (k + 1 / 2) * (a / M)⟩

theorem cell_subset_closedSquare (c : ℂ) {a : ℝ} (ha : 0 ≤ a) {M i k : ℕ} (hi : i < M)
    (hk : k < M) : closedSquare (cellCentre c a M i k) (a / M) ⊆ closedSquare c a := by
  intro z hz
  simp only [closedSquare, cellCentre, Set.mem_ofPred_eq, abs_le] at hz ⊢
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hi
  have ht : 0 ≤ a / M := div_nonneg ha hMr.le
  have hMt : (M : ℝ) * (a / M) = a := by field_simp
  have hi' : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi
  have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
  have e1 := mul_le_mul_of_nonneg_right hi' ht
  have e2 := mul_le_mul_of_nonneg_right hk' ht
  have e3 : 0 ≤ (i : ℝ) * (a / M) := mul_nonneg (Nat.cast_nonneg i) ht
  have e4 : 0 ≤ (k : ℝ) * (a / M) := mul_nonneg (Nat.cast_nonneg k) ht
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem exists_lt_le_le_add_one {M : ℕ} (hM : 0 < M) {u : ℝ} (hu0 : 0 ≤ u) (huM : u ≤ M) :
    ∃ i : ℕ, i < M ∧ (i : ℝ) ≤ u ∧ u ≤ i + 1 := by
  rcases lt_or_eq_of_le huM with h | h
  · exact ⟨⌊u⌋₊, (Nat.floor_lt hu0).2 h, Nat.floor_le hu0, (Nat.lt_floor_add_one u).le⟩
  · refine ⟨M - 1, Nat.sub_lt hM one_pos, ?_, ?_⟩ <;>
      rw [Nat.cast_sub (show 1 ≤ M from hM), Nat.cast_one] <;> linarith

/-- The `M × M` closed cells cover the square. -/
theorem closedSquare_subset_biUnion_cell (c : ℂ) {a : ℝ} (ha : 0 < a) {M : ℕ} (hM : 0 < M) :
    closedSquare c a ⊆ ⋃ q ∈ Finset.range M ×ˢ Finset.range M,
      closedSquare (cellCentre c a M q.1 q.2) (a / M) := by
  intro z hz
  simp only [closedSquare, Set.mem_ofPred_eq, abs_le] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have ht : 0 < a / M := div_pos ha hMr
  have hMt : (M : ℝ) * (a / M) = a := by field_simp
  obtain ⟨i, hi, hi1, hi2⟩ := exists_lt_le_le_add_one hM
    (u := (z.re - (c.re - a / 2)) / (a / M)) (div_nonneg (by linarith) ht.le)
    (by rw [div_le_iff₀ ht]; linarith)
  obtain ⟨k, hk, hk1, hk2⟩ := exists_lt_le_le_add_one hM
    (u := (z.im - (c.im - a / 2)) / (a / M)) (div_nonneg (by linarith) ht.le)
    (by rw [div_le_iff₀ ht]; linarith)
  rw [le_div_iff₀ ht] at hi1 hk1
  rw [div_le_iff₀ ht] at hi2 hk2
  refine mem_iUnion₂.2 ⟨(i, k), Finset.mem_product.2 ⟨Finset.mem_range.2 hi,
    Finset.mem_range.2 hk⟩, ?_⟩
  simp only [closedSquare, cellCentre, Set.mem_ofPred_eq, abs_le]
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem dist_lt_of_mem_closedSquare {q : ℂ} {s r : ℝ} (hsr : 2 * s < r) {x y : ℂ}
    (hx : x ∈ closedSquare q s) (hy : y ∈ closedSquare q s) : dist x y < r := by
  simp only [closedSquare, Set.mem_ofPred_eq, abs_le] at hx hy
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := hy
  rw [Complex.dist_eq]
  have h1 := Complex.norm_le_abs_re_add_abs_im (x - y)
  rw [Complex.sub_re, Complex.sub_im] at h1
  have h2 : |x.re - y.re| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  have h3 : |x.im - y.im| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- Each of the `M × M` cells carries uniform mass `1 / M²`. -/
theorem cond_closedSquare_cell (c : ℂ) {a : ℝ} (ha : 0 < a) {M i k : ℕ} (hi : i < M)
    (hk : k < M) :
    volume[|closedSquare c a] (closedSquare (cellCentre c a M i k) (a / M)) =
      ENNReal.ofReal (1 / (M * M)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hi
  rw [cond_apply (isClosed_closedSquare c a).measurableSet,
    Set.inter_eq_right.2 (cell_subset_closedSquare c ha.le hi hk), volume_closedSquare c ha.le,
    volume_closedSquare _ (div_pos ha hMr).le, ← ENNReal.ofReal_inv_of_pos (mul_pos ha ha),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (mul_pos ha ha).le)]
  congr 1
  field_simp

/-- **Independent uniform points form a fine net of a square.**  For `δ > 0` there is `N₀` such
that for all `N ≥ N₀`, all centres `c` and all sides `a > 0`, the probability that `N` independent
uniform points of `closedSquare c a` leave a point of the square at distance `≥ δ a` from all of
them is at most `δ`. -/
theorem exists_measure_pi_not_subset_iUnion_ball_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (c : ℂ) (a : ℝ), 0 < a →
      Measure.pi (fun _ : Fin N => volume[|closedSquare c a])
        {z | ¬ closedSquare c a ⊆ ⋃ j, ball (z j) (δ * a)} ≤ ENNReal.ofReal δ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / δ)
  have hMr : (0 : ℝ) < M := lt_trans (div_pos two_pos hδ) hM
  have hM0 : 0 < M := by exact_mod_cast hMr
  have hpos : (0 : ℝ) < 1 / (M * M) := div_pos one_pos (mul_pos hMr hMr)
  have hp1 : 1 - ENNReal.ofReal (1 / (M * M)) < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.2 hpos).ne'
  have hlim : Filter.Tendsto
      (fun N : ℕ => ((M * M : ℕ) : ℝ≥0∞) * (1 - ENNReal.ofReal (1 / (M * M))) ^ N)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp1)
      (Or.inr (ENNReal.natCast_ne_top (M * M)))
    rwa [mul_zero] at h
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.1 (hlim.eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 hδ)))
  refine ⟨N₀, fun N hN c a ha => ?_⟩
  have := isProbabilityMeasure_cond_closedSquare c ha
  refine (measure_pi_not_subset_iUnion_ball_le _ (Finset.range M ×ˢ Finset.range M)
    (fun q => closedSquare (cellCentre c a M q.1 q.2) (a / M)) _ (δ * a)
    (closedSquare_subset_biUnion_cell c ha hM0) ?_ N).trans ?_
  · intro q _ x hx y hy
    refine dist_lt_of_mem_closedSquare ?_ hx hy
    rw [div_lt_iff₀ hδ] at hM
    have e : 2 * (a / M) = 2 * a / M := by ring
    rw [e, div_lt_iff₀ hMr]
    have := mul_lt_mul_of_pos_right hM ha
    linarith
  · calc ∑ q ∈ Finset.range M ×ˢ Finset.range M,
          volume[|closedSquare c a] (closedSquare (cellCentre c a M q.1 q.2) (a / M))ᶜ ^ N
        = ∑ _q ∈ Finset.range M ×ˢ Finset.range M,
            (1 - ENNReal.ofReal (1 / (M * M))) ^ N := by
          refine Finset.sum_congr rfl fun q hq => ?_
          obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
          rw [prob_compl_eq_one_sub (isClosed_closedSquare _ _).measurableSet,
            cond_closedSquare_cell c ha (Finset.mem_range.1 hq1) (Finset.mem_range.1 hq2)]
      _ = ((M * M : ℕ) : ℝ≥0∞) * (1 - ENNReal.ofReal (1 / (M * M))) ^ N := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal δ := hN₀ N hN

/-- **Covering event, lower bound.**  For `δ > 0` there is `N₀` such that for all `N ≥ N₀`, all
centres `c` and all sides `a > 0`, `N` independent uniform points of `closedSquare c a` form a
`δ a`-net of the square with probability at least `1 - δ`. -/
theorem exists_le_measure_pi_subset_iUnion_ball (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (c : ℂ) (a : ℝ), 0 < a →
      1 - ENNReal.ofReal δ ≤ Measure.pi (fun _ : Fin N => volume[|closedSquare c a])
        {z | closedSquare c a ⊆ ⋃ j, ball (z j) (δ * a)} := by
  obtain ⟨N₀, h⟩ := exists_measure_pi_not_subset_iUnion_ball_le δ hδ
  refine ⟨N₀, fun N hN c a ha => ?_⟩
  have := isProbabilityMeasure_cond_closedSquare c ha
  set ν := Measure.pi (fun _ : Fin N => volume[|closedSquare c a]) with hν
  set E := {z : Fin N → ℂ | closedSquare c a ⊆ ⋃ j, ball (z j) (δ * a)} with hE
  have hc : Eᶜ = {z : Fin N → ℂ | ¬ closedSquare c a ⊆ ⋃ j, ball (z j) (δ * a)} := by
    rw [hE, Set.compl_ofPred]
  have h1 : (1 : ℝ≥0∞) ≤ ν E + ν Eᶜ :=
    calc (1 : ℝ≥0∞) = ν univ := measure_univ.symm
      _ = ν (E ∪ Eᶜ) := by rw [Set.union_compl_self]
      _ ≤ ν E + ν Eᶜ := measure_union_le _ _
  have hle : ν Eᶜ ≤ ENNReal.ofReal δ := by rw [hc]; exact h N hN c a ha
  calc 1 - ENNReal.ofReal δ ≤ 1 - ν Eᶜ := tsub_le_tsub_left hle 1
    _ ≤ ν E := tsub_le_iff_right.2 h1

end LatticeProb.RandomPointsCover
