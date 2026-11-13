import LatticeProb.Analysis.ExcursionCountSandwich
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Scaling of the ladder set, the first passage and the excursion count

Let `r, c > 0` and let `Y` be the path `X` with time scaled by `r` and space scaled by `c`, that is
`Y (r u) = c X u` for every `u` (Brownian scaling is the case `r = c²`). This file shows that the deterministic
objects behind the excursion-count formula scale accordingly:

* `forwardLadderSet_scale`: the forward ladder set of `Y` from `r a` is `r` times the forward ladder set of `X`
  from `a`;
* `firstPassageBelow_scale`: the first passage of `Y` below `Y (r a) - c b` after `r a` is `r` times the first
  passage of `X` below `X a - b` after `a`;
* `excursionCount_mul`: the excursion count is invariant under the dilation `x ↦ r x` of the set, the window and
  the threshold `ε`;
* `excursionCount_firstPassageBelow_scale`: hence the number of excursions of `Y` above its running minimum, of
  length `> r ε`, before its first passage below level `c b`, equals the number of excursions of `X` of length
  `> ε` before its first passage below level `b`.
-/

open Filter Set Topology
open scoped Pointwise

namespace LatticeProb.LadderSet

variable {X Y : ℝ → ℝ} {r c : ℝ}

theorem mul_Icc_diff (hr : 0 < r) (K : Set ℝ) (s t : ℝ) :
    Icc (r * s) (r * t) \ (r * ·) '' K = (r * ·) '' (Icc s t \ K) := by
  ext x
  obtain ⟨y, rfl⟩ : ∃ y, x = r * y := ⟨r⁻¹ * x, (mul_inv_cancel_left₀ hr.ne' x).symm⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hyK⟩
    exact ⟨y, ⟨⟨le_of_mul_le_mul_left h1 hr, le_of_mul_le_mul_left h2 hr⟩, fun hK => hyK ⟨y, hK, rfl⟩⟩, rfl⟩
  · rintro ⟨z, ⟨⟨h1, h2⟩, hzK⟩, hzy⟩
    obtain rfl := mul_right_injective₀ hr.ne' hzy
    refine ⟨⟨mul_le_mul_of_nonneg_left h1 hr.le, mul_le_mul_of_nonneg_left h2 hr.le⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact hzK ((mul_right_injective₀ hr.ne' hwz) ▸ hw)

theorem mul_connectedComponentIn (hr : 0 < r) {S : Set ℝ} {y : ℝ} (hy : y ∈ S) :
    (r * ·) '' connectedComponentIn S y = connectedComponentIn ((r * ·) '' S) (r * y) := by
  have h := (Homeomorph.mulLeft₀ r hr.ne').image_connectedComponentIn hy
  simpa only [Homeomorph.coe_mulLeft₀] using h

/-- The dilation `x ↦ r x`, `r > 0`, maps the complementary intervals of `K` in `[s, t]` onto those of `r K` in
`[r s, r t]`. -/
theorem complementaryIntervals_mul (hr : 0 < r) (K : Set ℝ) (s t : ℝ) :
    complementaryIntervals ((r * ·) '' K) (r * s) (r * t) =
      (fun C => (r * ·) '' C) '' complementaryIntervals K s t := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mul_Icc_diff hr] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨connectedComponentIn (Icc s t \ K) y, ⟨y, hy, rfl⟩, mul_connectedComponentIn hr hy⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨r * y, ?_, ?_⟩
    · rw [mul_Icc_diff hr]
      exact ⟨y, hy, rfl⟩
    · rw [mul_Icc_diff hr]
      exact (mul_connectedComponentIn hr hy).symm

theorem diam_mul_image (hr : 0 < r) (C : Set ℝ) : Metric.diam ((r * ·) '' C) = r * Metric.diam C := by
  have h : (r * ·) '' C = r • C := Set.image_smul (a := r) (t := C)
  rw [h, diam_smul₀, Real.norm_of_nonneg hr.le]

/-- **Dilation invariance of the excursion count.** For `r > 0`, the number of complementary intervals of `r K` in
`[r s, r t]` of length `> r ε` is the number of complementary intervals of `K` in `[s, t]` of length `> ε`. -/
theorem excursionCount_mul (hr : 0 < r) (K : Set ℝ) (s t ε : ℝ) :
    excursionCount ((r * ·) '' K) (r * s) (r * t) (r * ε) = excursionCount K s t ε := by
  unfold excursionCount
  have h : {C ∈ complementaryIntervals ((r * ·) '' K) (r * s) (r * t) | r * ε < Metric.diam C} =
      (fun C => (r * ·) '' C) '' {C ∈ complementaryIntervals K s t | ε < Metric.diam C} := by
    rw [complementaryIntervals_mul hr]
    ext C
    constructor
    · rintro ⟨⟨D, hD, rfl⟩, hε⟩
      rw [diam_mul_image hr] at hε
      exact ⟨D, ⟨hD, lt_of_mul_lt_mul_left hε hr.le⟩, rfl⟩
    · rintro ⟨D, ⟨hD, hε⟩, rfl⟩
      refine ⟨⟨D, hD, rfl⟩, ?_⟩
      rw [diam_mul_image hr]
      exact mul_lt_mul_of_pos_left hε hr
  rw [h, Set.ncard_image_of_injective _ (Set.image_injective.2 (mul_right_injective₀ hr.ne'))]

/-- **Scaling of the forward ladder set.** If `Y (r u) = c X u` for every `u`, with `r, c > 0`, the forward ladder
set of `Y` from `r a` is `r` times the forward ladder set of `X` from `a`. -/
theorem forwardLadderSet_scale (hr : 0 < r) (hc : 0 < c) (hY : ∀ u, Y (r * u) = c * X u) (a : ℝ) :
    forwardLadderSet Y (r * a) = (r * ·) '' forwardLadderSet X a := by
  ext t
  obtain ⟨u, rfl⟩ : ∃ u, t = r * u := ⟨r⁻¹ * t, (mul_inv_cancel_left₀ hr.ne' t).symm⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨u, ⟨le_of_mul_le_mul_left h1 hr, fun s hs => ?_⟩, rfl⟩
    have h := h2 (r * s) ⟨mul_le_mul_of_nonneg_left hs.1 hr.le, mul_le_mul_of_nonneg_left hs.2 hr.le⟩
    rw [hY, hY] at h
    exact le_of_mul_le_mul_left h hc
  · rintro ⟨v, ⟨h1, h2⟩, hv⟩
    obtain rfl := mul_right_injective₀ hr.ne' hv
    refine ⟨mul_le_mul_of_nonneg_left h1 hr.le, fun s hs => ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s', s = r * s' := ⟨r⁻¹ * s, (mul_inv_cancel_left₀ hr.ne' s).symm⟩
    rw [hY, hY]
    exact mul_le_mul_of_nonneg_left
      (h2 s ⟨le_of_mul_le_mul_left hs.1 hr, le_of_mul_le_mul_left hs.2 hr⟩) hc.le

/-- **Scaling of the first passage.** If `Y (r u) = c X u` for every `u`, with `r, c > 0`, the first passage of `Y`
below `Y (r a) - c b` after `r a` is `r` times the first passage of `X` below `X a - b` after `a`. -/
theorem firstPassageBelow_scale (hr : 0 < r) (hc : 0 < c) (hY : ∀ u, Y (r * u) = c * X u) (a b : ℝ) :
    firstPassageBelow Y (r * a) (c * b) = r * firstPassageBelow X a b := by
  have hset : {t | r * a ≤ t ∧ Y t < Y (r * a) - c * b} = r • {u | a ≤ u ∧ X u < X a - b} := by
    ext t
    obtain ⟨u, rfl⟩ : ∃ u, t = r * u := ⟨r⁻¹ * t, (mul_inv_cancel_left₀ hr.ne' t).symm⟩
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨u, ⟨le_of_mul_le_mul_left h1 hr, ?_⟩, rfl⟩
      rw [hY, hY, ← mul_sub] at h2
      exact lt_of_mul_lt_mul_left h2 hc.le
    · rintro ⟨v, ⟨h1, h2⟩, hv⟩
      obtain rfl := mul_right_injective₀ hr.ne' hv
      refine ⟨mul_le_mul_of_nonneg_left h1 hr.le, ?_⟩
      rw [hY, hY, ← mul_sub]
      exact mul_lt_mul_of_pos_left h2 hc
  show sInf _ = r * sInf _
  rw [hset, Real.sInf_smul_of_nonneg hr.le, smul_eq_mul]

/-- **Scaling of the excursion count before a first passage.** If `Y (r u) = c X u` for every `u`, with `r, c > 0`,
the number of excursions of `Y` above its running minimum from `r a`, of length `> r ε`, before its first passage
below `Y (r a) - c b`, equals the number of excursions of `X` above its running minimum from `a`, of length `> ε`,
before its first passage below `X a - b`. For Brownian scaling, `r = c²`. -/
theorem excursionCount_firstPassageBelow_scale (hr : 0 < r) (hc : 0 < c) (hY : ∀ u, Y (r * u) = c * X u)
    (a b ε : ℝ) :
    excursionCount (forwardLadderSet Y (r * a)) (r * a) (firstPassageBelow Y (r * a) (c * b)) (r * ε) =
      excursionCount (forwardLadderSet X a) a (firstPassageBelow X a b) ε := by
  rw [forwardLadderSet_scale hr hc hY, firstPassageBelow_scale hr hc hY, excursionCount_mul hr]

end LatticeProb.LadderSet
