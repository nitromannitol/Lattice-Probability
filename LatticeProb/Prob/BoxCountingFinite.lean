import Mathlib

/-!
# A box-counting criterion for almost sure finiteness

Let `S ω ⊆ ℝ` be a random set, `p < r`, and partition `[p, r)` into `n` boxes
`I_{n,k} = [p + k h_n, p + (k + 1) h_n)`, `k < n`, of length `h_n = (r - p) / n`. Suppose that the event that
`S ω` meets `I_{n,k}` is contained in a measurable set `E n k` and that `∑_{k < n} μ (E n k) ≤ C < ∞` for every
`n`. Then `S ω ∩ [p, r)` is finite for `μ`-almost every `ω`. No measurability of `S` is assumed.

The proof counts boxes: with `N_n = ∑_{k < n} 1_{E n k}`, a finite subset of `S ω ∩ [p, r)` with `m` points lies
in `m` distinct boxes once `h_n` is below its minimal gap, so `m ≤ N_n ω` for all large `n` and the cardinality of
`S ω ∩ [p, r)` is at most `liminf N_n ω`. By the Fatou lemma `∫⁻ liminf N_n ≤ C < ∞`, so `liminf N_n < ∞` almost
everywhere.

## Main results

* `natFloor_div_lt_and_mem_Ico_box`: the box index `⌊(x - p) / h_n⌋₊` of a point `x ∈ [p, r)` is below `n` and
  `x` lies in the box with that index;
* `eventually_natFloor_div_lt_natFloor_div`: two points `x < y` of `[p, r)` have distinct box indices for all
  large `n`;
* `ae_finite_inter_Ico_of_box_bound`: the box-counting criterion.
-/

namespace LatticeProb

open MeasureTheory Filter Set
open scoped ENNReal

/-- The box index `⌊(x - p) / ((r - p) / n)⌋₊` of a point `x ∈ [p, r)` in the partition of `[p, r)` into `n`
boxes of length `(r - p) / n` is below `n`, and `x` lies in the box with that index. -/
theorem natFloor_div_lt_and_mem_Ico_box {p r x : ℝ} {n : ℕ} (hpr : p < r) (hn : 0 < n)
    (hx : x ∈ Ico p r) :
    ⌊(x - p) / ((r - p) / n)⌋₊ < n ∧
      x ∈ Ico (p + (⌊(x - p) / ((r - p) / n)⌋₊ : ℝ) * ((r - p) / n))
        (p + ((⌊(x - p) / ((r - p) / n)⌋₊ : ℝ) + 1) * ((r - p) / n)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh : 0 < (r - p) / n := div_pos (sub_pos.mpr hpr) hn0
  have ha : 0 ≤ (x - p) / ((r - p) / n) := div_nonneg (sub_nonneg.mpr hx.1) hh.le
  have hnh : (n : ℝ) * ((r - p) / n) = r - p := by field_simp
  refine ⟨(Nat.floor_lt ha).mpr ?_, mem_Ico.mpr ⟨?_, ?_⟩⟩
  · rw [div_lt_iff₀ hh, hnh]
    linarith [hx.2]
  · have := (le_div_iff₀ hh).mp (Nat.floor_le ha)
    linarith
  · have := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((x - p) / ((r - p) / n)))
    linarith

/-- Two points `p ≤ x < y` have distinct box indices `⌊(· - p) / ((r - p) / n)⌋₊` for all large `n`: once the
box length `(r - p) / n` is at most `y - x`, the index of `y` exceeds that of `x`. -/
theorem eventually_natFloor_div_lt_natFloor_div {p r x y : ℝ} (hpr : p < r) (hx : p ≤ x) (hxy : x < y) :
    ∀ᶠ n : ℕ in atTop, ⌊(x - p) / ((r - p) / n)⌋₊ < ⌊(y - p) / ((r - p) / n)⌋₊ := by
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hrp : 0 < r - p := sub_pos.mpr hpr
  filter_upwards [eventually_ge_atTop (⌈(r - p) / (y - x)⌉₊ + 1)] with n hn
  have hq : 0 ≤ (r - p) / (y - x) := div_nonneg hrp.le hyx.le
  have hn' : (r - p) / (y - x) + 1 ≤ n := by
    have hc := Nat.le_ceil ((r - p) / (y - x))
    have h2 : ((⌈(r - p) / (y - x)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hh : 0 < (r - p) / n := div_pos hrp hn0
  have hstep : (r - p) / n ≤ y - x := by
    rw [div_le_iff₀ hn0]
    have h1 : (r - p) / (y - x) ≤ n := by linarith
    rw [div_le_iff₀ hyx] at h1
    linarith
  have ha : 0 ≤ (x - p) / ((r - p) / n) := div_nonneg (sub_nonneg.mpr hx) hh.le
  have key : (x - p) / ((r - p) / n) + 1 ≤ (y - p) / ((r - p) / n) := by
    rw [div_add_one hh.ne', div_le_div_iff_of_pos_right hh]
    linarith
  have hfl : ((⌊(x - p) / ((r - p) / n)⌋₊ + 1 : ℕ) : ℝ) ≤ (y - p) / ((r - p) / n) := by
    push_cast
    linarith [Nat.floor_le ha]
  exact (Nat.lt_add_one _).trans_le (Nat.le_floor hfl)

/-- **Box-counting criterion.** Let `S ω ⊆ ℝ` and `p < r`. For every `n`, partition `[p, r)` into the `n` boxes
`[p + k (r - p) / n, p + (k + 1) (r - p) / n)`, `k < n`, and let `E n k` be a measurable set containing every `ω`
for which `S ω` meets the `k`-th box. If `∑_{k < n} μ (E n k) ≤ C` for every `n`, with `C < ∞`, then
`S ω ∩ [p, r)` is finite for `μ`-almost every `ω`. -/
theorem ae_finite_inter_Ico_of_box_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (S : Ω → Set ℝ)
    {p r : ℝ} (hpr : p < r) (E : ℕ → ℕ → Set Ω) (hE : ∀ n k, MeasurableSet (E n k))
    (hcover : ∀ n k : ℕ, k < n → ∀ ω,
      (S ω ∩ Set.Ico (p + k * ((r - p) / n)) (p + (k + 1) * ((r - p) / n))).Nonempty → ω ∈ E n k)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hsum : ∀ n, ∑ k ∈ Finset.range n, μ (E n k) ≤ C) :
    ∀ᵐ ω ∂μ, (S ω ∩ Set.Ico p r).Finite := by
  have hmeas : ∀ n, Measurable fun ω => ∑ k ∈ Finset.range n, (E n k).indicator (1 : Ω → ℝ≥0∞) ω :=
    fun n => Finset.measurable_sum _ fun k _ => measurable_one.indicator (hE n k)
  have hint : ∀ n, ∫⁻ ω, ∑ k ∈ Finset.range n, (E n k).indicator (1 : Ω → ℝ≥0∞) ω ∂μ ≤ C := by
    intro n
    rw [lintegral_finsetSum _ fun k _ => measurable_one.indicator (hE n k)]
    calc ∑ k ∈ Finset.range n, ∫⁻ ω, (E n k).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
        = ∑ k ∈ Finset.range n, μ (E n k) :=
          Finset.sum_congr rfl fun k _ => lintegral_indicator_one (hE n k)
      _ ≤ C := hsum n
  have hfatou : ∫⁻ ω, liminf (fun n => ∑ k ∈ Finset.range n, (E n k).indicator (1 : Ω → ℝ≥0∞) ω) atTop ∂μ
      ≤ C :=
    (lintegral_liminf_le hmeas).trans (liminf_le_of_frequently_le' (Frequently.of_forall hint))
  have hlm : Measurable fun ω =>
      liminf (fun n => ∑ k ∈ Finset.range n, (E n k).indicator (1 : Ω → ℝ≥0∞) ω) atTop :=
    Measurable.liminf hmeas
  filter_upwards [ae_lt_top hlm (hfatou.trans_lt hC.lt_top).ne] with ω hω
  by_contra hinf
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hω.ne
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf m
  -- for all large `n`, the points of `t` lie in distinct boxes
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ x ∈ t, ∀ y ∈ t,
      ⌊(x - p) / ((r - p) / n)⌋₊ = ⌊(y - p) / ((r - p) / n)⌋₊ → x = y := by
    refine (eventually_gt_atTop 0).and ((eventually_all_finset t).2 fun x hx =>
      (eventually_all_finset t).2 fun y hy => ?_)
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · filter_upwards [eventually_natFloor_div_lt_natFloor_div hpr (hts hx).2.1 hxy] with n hn heq
      exact absurd heq hn.ne
    · exact Eventually.of_forall fun _ _ => rfl
    · filter_upwards [eventually_natFloor_div_lt_natFloor_div hpr (hts hy).2.1 hxy] with n hn heq
      exact absurd heq.symm hn.ne
  -- hence the box count is at least `m` for all large `n`
  have hle : ∀ᶠ n : ℕ in atTop,
      (m : ℝ≥0∞) ≤ ∑ k ∈ Finset.range n, (E n k).indicator (1 : Ω → ℝ≥0∞) ω := by
    filter_upwards [hev] with n hn
    obtain ⟨hn, hinj⟩ := hn
    have hmem : ∀ x ∈ t,
        ⌊(x - p) / ((r - p) / n)⌋₊ < n ∧ ω ∈ E n ⌊(x - p) / ((r - p) / n)⌋₊ := by
      intro x hx
      obtain ⟨hlt, hbox⟩ := natFloor_div_lt_and_mem_Ico_box hpr hn (hts hx).2
      exact ⟨hlt, hcover n _ hlt ω ⟨x, (hts hx).1, hbox⟩⟩
    calc (m : ℝ≥0∞)
        = ∑ x ∈ t, (E n ⌊(x - p) / ((r - p) / n)⌋₊).indicator (1 : Ω → ℝ≥0∞) ω := by
          rw [← htc, Finset.card_eq_sum_ones, Nat.cast_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Set.indicator_of_mem (hmem x hx).2]
          simp
      _ = ∑ k ∈ t.image (fun x => ⌊(x - p) / ((r - p) / n)⌋₊),
            (E n k).indicator (1 : Ω → ℝ≥0∞) ω :=
          (Finset.sum_image (f := fun k => (E n k).indicator (1 : Ω → ℝ≥0∞) ω) hinj).symm
      _ ≤ ∑ k ∈ Finset.range n, (E n k).indicator (1 : Ω → ℝ≥0∞) ω :=
          Finset.sum_le_sum_of_subset fun k hk => by
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
            exact Finset.mem_range.mpr (hmem x hx).1
  exact absurd (le_liminf_of_le (by isBoundedDefault) hle) (not_le.mpr hm)

end LatticeProb
