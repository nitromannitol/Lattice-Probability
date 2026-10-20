/-
Adapted from Mathlib's `Mathlib/Topology/EMetricSpace/BoundedVariation.lean` (commit 06535612), which is not in the Mathlib version LP pins.
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Variation of monotone functions and of the identity

Facts about the total variation `eVariationOn` that the pinned Mathlib does not provide, stated under
`LatticeProb` names so that they cannot clash with a later Mathlib:

* `LatticeProb.monotoneOn_eVariationOn_eq`: on `s ∩ Icc a b`, a monotone real function has variation
  equal to its increment `f b - f a`.
* `LatticeProb.eVariationOn_pair`: the variation on a two-point set is the distance of the values.
* `LatticeProb.eVariationOn_image_range_of_monotone`: the variation along the image of `Iic n` under
  a monotone sequence is the sum of the distances between consecutive values.
* `LatticeProb.eVariationOn_id` and `LatticeProb.eVariationOn_id_Icc`: the variation of the identity
  on an interval is the length of the interval.
-/

namespace LatticeProb

open Set

section Variation

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The variation of a function on a two-point set is the distance between the two values. -/
theorem eVariationOn_pair (f : α → E) (a b : α) :
    eVariationOn f {a, b} = edist (f a) (f b) := by
  wlog hab : a ≤ b generalizing a b
  · simpa [edist_comm, pair_comm] using this b a (le_of_not_ge hab)
  · apply le_antisymm _ (eVariationOn.edist_le f (by simp) (by simp))
    simp only [eVariationOn.eVariationOn_eq_strictMonoOn, iSup_le_iff]
    rintro ⟨n, u, hmono, hi⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
    · simp
    · have := hmono (by simp) (by simp) zero_lt_one
      simp [(by grind : u 0 = a), (by grind : u 1 = b), edist_comm]
    · have := hmono (by simp) (by grind) zero_lt_one
      have := hmono (by grind) (by grind) one_lt_two
      grind

/-- The variation of a monotone real-valued function on `s ∩ Icc a b` equals its increment
`f b - f a`. -/
theorem monotoneOn_eVariationOn_eq {f : α → ℝ} {s : Set α} {a b : α} (hf : MonotoneOn f s)
    (ha : a ∈ s) (hb : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) = ENNReal.ofReal (f b - f a) := by
  rcases le_or_gt a b with hab | hab
  · have hle : eVariationOn f (s ∩ Icc a b) ≤ ENNReal.ofReal (f b - f a) :=
      MonotoneOn.eVariationOn_le hf ha hb
    have hfin : BoundedVariationOn f (s ∩ Icc a b) := (hle.trans_lt ENNReal.ofReal_lt_top).ne
    have hb' : b ∈ s ∩ Icc a b := ⟨hb, hab, le_rfl⟩
    have ha' : a ∈ s ∩ Icc a b := ⟨ha, le_rfl, hab⟩
    exact le_antisymm hle (ENNReal.ofReal_le_of_le_toReal (hfin.sub_le hb' ha'))
  · simp [Icc_eq_empty (not_le.2 hab), hf hb ha hab.le]

/-- The variation along the image of `{0, …, n}` under a monotone sequence `u` is the sum of the
distances between consecutive values. -/
theorem eVariationOn_image_range_of_monotone (f : α → E) {u : ℕ → α} (hu : Monotone u) (n : ℕ) :
    eVariationOn f (u '' Iic n) = ∑ i ∈ Finset.range n, edist (f (u i)) (f (u (i + 1))) := by
  induction n with
  | zero => simp [Iic]
  | succ n ih =>
    rw [(by grind : u '' Iic (n + 1) = u '' Iic n ∪ {u n, u (n + 1)}), eVariationOn.union f]
    · simp [Finset.sum_range_succ, ih, eVariationOn_pair]
    · refine ⟨⟨n, by simp, rfl⟩, ?_⟩
      rintro _ ⟨m, hm, rfl⟩
      exact hu (mem_Iic.1 hm)
    · simp [IsLeast, hu n.le_succ]

/-- The variation of the identity on `s ∩ Icc a b` is `b - a`. -/
theorem eVariationOn_id {a b : ℝ} {s : Set ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    eVariationOn id (s ∩ Icc a b) = ENNReal.ofReal (b - a) :=
  monotoneOn_eVariationOn_eq (monotone_id.monotoneOn s) ha hb

/-- The variation of the identity on `Icc a b` is `b - a`. -/
@[simp]
theorem eVariationOn_id_Icc (a b : ℝ) : eVariationOn id (Icc a b) = ENNReal.ofReal (b - a) := by
  simpa using eVariationOn_id (s := univ) (mem_univ a) (mem_univ b)

end Variation

end LatticeProb
