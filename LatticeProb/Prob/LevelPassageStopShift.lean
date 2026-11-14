import Mathlib
import LatticeProb.Prob.UpcrossConcat
import LatticeProb.Prob.StayLastZero
import LatticeProb.Prob.UpcrossMeasurable

/-!
# First passages below negative levels under stopping and shifting

For a continuous path `w` with `w 0 = 0` and levels `0 ≤ a ≤ b ≤ c`, let `T_x = hitFrom (-x) 0 w`
be the first passage time of `w` at `-x`. This file proves the pathwise identities behind the
independent increments of the level-passage process of a pair of paths:

* `hitFrom_neg_le_hitFrom_neg`: `T_a ≤ T_b`;
* `hitFrom_neg_stopAt_hitFrom_neg`: stopping `w` at `T_b` does not change `T_a`;
* `hitFrom_neg_eq_add_shiftPath`: if `T_b < ∞`, then `T_c = T_b + T'_{c-b}`, where `T'` is the
  first passage time of the increments `shiftPath T_b w` after `T_b`.

For a pair of paths `p = (l, r)`, `passageValue a p = r (T_a(l))` is the value of the second path
at the first passage of the first path at `-a`. For two pairs `q = (q₁, q₂)` the level process
`cauchyLevel a q = passageValue a q₂ - passageValue a q₁` satisfies (`cauchyLevel_pairStopAt`,
`cauchyLevel_sub_eq_pairShiftAt`): its values at levels `a ≤ b` are functions of the pairs stopped
at the passages at `-b`, and its increment between `b` and `c` is the level process at `c - b` of
the pairs of increments after these passages.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace LatticeProb

section Passage

variable {w : C(ℝ≥0, ℝ)} {a b c : ℝ}

/-- Before its first passage at `-b ≤ 0`, a path started at `0` stays above `-b`. -/
lemma neg_lt_of_coe_lt_hitFrom_neg (hw0 : w 0 = 0) (hb : 0 ≤ b) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < hitFrom (-b) 0 (w : ℝ≥0 → ℝ)) : -b < w u := by
  by_contra h
  have hmem : -b ∈ Icc (w u) (w 0) := ⟨not_lt.1 h, by rw [hw0]; linarith⟩
  obtain ⟨s, hs, hws⟩ := intermediate_value_Icc' zero_le w.continuous.continuousOn hmem
  exact lt_irrefl _ (hu.trans_le ((hitFrom_le zero_le hws).trans (ENNReal.coe_le_coe.2 hs.2)))

/-- For a path started at `0`, the first passage at `-a` comes no later than the first passage at
`-b` when `0 ≤ a ≤ b`. -/
lemma hitFrom_neg_le_hitFrom_neg (hw0 : w 0 = 0) (ha : 0 ≤ a) (hab : a ≤ b) :
    hitFrom (-a) 0 (w : ℝ≥0 → ℝ) ≤ hitFrom (-b) 0 (w : ℝ≥0 → ℝ) := by
  by_cases hT : hitFrom (-b) 0 (w : ℝ≥0 → ℝ) = ⊤
  · rw [hT]; exact le_top
  obtain ⟨t, ht, -, hwt, -⟩ := exists_hitFrom_eq w.continuous hT
  have hmem : -a ∈ Icc (w t) (w 0) := ⟨by rw [hwt]; linarith, by rw [hw0]; linarith⟩
  obtain ⟨s, hs, hws⟩ := intermediate_value_Icc' zero_le w.continuous.continuousOn hmem
  rw [ht]
  exact (hitFrom_le zero_le hws).trans (ENNReal.coe_le_coe.2 hs.2)

/-- Stopping a path started at `0` at its first passage at `-b` does not change its first passage
at `-a` for `0 ≤ a ≤ b` (also when the passage at `-b` never happens). -/
theorem hitFrom_neg_stopAt_hitFrom_neg (hw0 : w 0 = 0) (ha : 0 ≤ a) (hab : a ≤ b) :
    hitFrom (-a) 0 (stopAt (hitFrom (-b) 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ) =
      hitFrom (-a) 0 (w : ℝ≥0 → ℝ) := by
  set T := hitFrom (-b) 0 (w : ℝ≥0 → ℝ)
  have hle : hitFrom (-a) 0 (w : ℝ≥0 → ℝ) ≤ T := hitFrom_neg_le_hitFrom_neg hw0 ha hab
  apply le_antisymm
  · by_cases hA : hitFrom (-a) 0 (w : ℝ≥0 → ℝ) = ⊤
    · rw [hA]; exact le_top
    obtain ⟨e, he, -, hwe, -⟩ := exists_hitFrom_eq w.continuous hA
    rw [he] at hle ⊢
    refine hitFrom_le zero_le ?_
    rw [stopAt_apply_of_le hle w le_rfl]
    exact hwe
  · refine le_iInf₂ fun s hs => ?_
    by_cases hsT : (s : ℝ≥0∞) ≤ T
    · have h2 := hs.2
      rw [stopAt_apply_of_le hsT w le_rfl] at h2
      exact hitFrom_le zero_le h2
    · exact hle.trans (not_le.1 hsT).le

/-- For a path started at `0` and `0 ≤ b ≤ c`, the first passage at `-c` is the first passage at
`-c` after the first passage at `-b`. -/
lemma hitFrom_neg_eq_hitFrom_neg_from (hw0 : w 0 = 0) (hb : 0 ≤ b) (hbc : b ≤ c) :
    hitFrom (-c) 0 (w : ℝ≥0 → ℝ) =
      hitFrom (-c) (hitFrom (-b) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := by
  apply le_antisymm
  · exact hitFrom_mono_start zero_le _
  · refine le_iInf₂ fun s hs => ?_
    by_cases hsT : (s : ℝ≥0∞) < hitFrom (-b) 0 (w : ℝ≥0 → ℝ)
    · have h1 := neg_lt_of_coe_lt_hitFrom_neg hw0 hb hsT
      rw [hs.2] at h1
      exact absurd h1 (not_lt.2 (by linarith))
    · exact hitFrom_le (not_lt.1 hsT) hs.2

/-- **Additivity of first passages.** For a path started at `0`, `0 ≤ b ≤ c` and a finite first
passage time `T_b` at `-b`, the first passage at `-c` is `T_b` plus the first passage at `-(c - b)`
of the increments of the path after `T_b`. -/
theorem hitFrom_neg_eq_add_shiftPath (hw0 : w 0 = 0) (hb : 0 ≤ b) (hbc : b ≤ c)
    (hT : hitFrom (-b) 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    hitFrom (-c) 0 (w : ℝ≥0 → ℝ) = hitFrom (-b) 0 (w : ℝ≥0 → ℝ) +
      hitFrom (-(c - b)) 0 (shiftPath (hitFrom (-b) 0 (w : ℝ≥0 → ℝ)).toNNReal w : ℝ≥0 → ℝ) := by
  obtain ⟨t, ht, -, hwt, -⟩ := exists_hitFrom_eq w.continuous hT
  rw [hitFrom_neg_eq_hitFrom_neg_from hw0 hb hbc, ht, ENNReal.toNNReal_coe,
    hitFrom_at_first_hit hwt (-c), show -c - -b = -(c - b) by ring]

end Passage

section Pairs

variable {a b c : ℝ}

/-- The value of the second path of a pair at the first passage of the first path at `-a` (at the
junk time `0` when that passage never happens). -/
def passageValue (a : ℝ) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : ℝ :=
  p.2 (hitFrom (-a) 0 (p.1 : ℝ≥0 → ℝ)).toNNReal

/-- A pair of paths, both stopped at the first passage of the first path at `-b`. -/
def pairStopAt (b : ℝ) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) :=
  (stopAt (hitFrom (-b) 0 (p.1 : ℝ≥0 → ℝ)) p.1, stopAt (hitFrom (-b) 0 (p.1 : ℝ≥0 → ℝ)) p.2)

/-- The increments of a pair of paths after the first passage of the first path at `-b`. -/
def pairShiftAt (b : ℝ) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) :=
  (shiftPath (hitFrom (-b) 0 (p.1 : ℝ≥0 → ℝ)).toNNReal p.1,
    shiftPath (hitFrom (-b) 0 (p.1 : ℝ≥0 → ℝ)).toNNReal p.2)

/-- The level-passage process of two pairs of paths `q = (q₁, q₂)`: at level `a`, the passage value
of `q₂` minus the passage value of `q₁`. -/
def cauchyLevel (a : ℝ) (q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) : ℝ :=
  passageValue a q.2 - passageValue a q.1

/-- The passage value at `-a` is unchanged by stopping the pair at the passage at `-b ≤ -a`. -/
theorem passageValue_pairStopAt {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)} (hp : p.1 0 = 0) (ha : 0 ≤ a)
    (hab : a ≤ b) : passageValue a (pairStopAt b p) = passageValue a p := by
  have hle := hitFrom_neg_le_hitFrom_neg hp ha hab
  simp only [passageValue, pairStopAt]
  rw [hitFrom_neg_stopAt_hitFrom_neg hp ha hab]
  exact stopAt_apply_of_le (ENNReal.coe_toNNReal_le_self.trans hle) p.2 le_rfl

/-- The passage value at `-c` is the passage value at `-b` plus the passage value at `-(c - b)` of
the increments after the passage at `-b` (`0 ≤ b ≤ c`, the passage at `-c` happens). -/
theorem passageValue_eq_add_pairShiftAt {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)} (hp : p.1 0 = 0)
    (hb : 0 ≤ b) (hbc : b ≤ c) (hc : hitFrom (-c) 0 (p.1 : ℝ≥0 → ℝ) ≠ ⊤) :
    passageValue c p = passageValue b p + passageValue (c - b) (pairShiftAt b p) := by
  have hT : hitFrom (-b) 0 (p.1 : ℝ≥0 → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top hc (hitFrom_neg_le_hitFrom_neg hp hb hbc)
  have hsum := hitFrom_neg_eq_add_shiftPath hp hb hbc hT
  obtain ⟨t, ht, -, -, -⟩ := exists_hitFrom_eq p.1.continuous hT
  rw [ht, ENNReal.toNNReal_coe] at hsum
  have hH : hitFrom (-(c - b)) 0 (shiftPath t p.1 : ℝ≥0 → ℝ) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsum
    exact hc hsum
  obtain ⟨u, hu, -, -, -⟩ := exists_hitFrom_eq (shiftPath t p.1).continuous hH
  simp only [passageValue, pairShiftAt]
  rw [hsum, ht]
  simp only [ENNReal.toNNReal_coe]
  rw [hu, ← ENNReal.coe_add]
  simp only [ENNReal.toNNReal_coe, shiftPath_apply]
  ring

/-- The level process at levels `0 ≤ a ≤ b` is a function of the two pairs stopped at their
passages at `-b`. -/
theorem cauchyLevel_pairStopAt {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))}
    (h₁ : q.1.1 0 = 0) (h₂ : q.2.1 0 = 0) (ha : 0 ≤ a) (hab : a ≤ b) :
    cauchyLevel a (pairStopAt b q.1, pairStopAt b q.2) = cauchyLevel a q := by
  simp only [cauchyLevel]
  rw [passageValue_pairStopAt h₁ ha hab, passageValue_pairStopAt h₂ ha hab]

/-- The increment of the level process between levels `0 ≤ b ≤ c` is the level process at `c - b`
of the two pairs of increments after their passages at `-b` (both passages at `-c` happen). -/
theorem cauchyLevel_sub_eq_pairShiftAt
    {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))}
    (h₁ : q.1.1 0 = 0) (h₂ : q.2.1 0 = 0) (hb : 0 ≤ b) (hbc : b ≤ c)
    (hc₁ : hitFrom (-c) 0 (q.1.1 : ℝ≥0 → ℝ) ≠ ⊤) (hc₂ : hitFrom (-c) 0 (q.2.1 : ℝ≥0 → ℝ) ≠ ⊤) :
    cauchyLevel c q - cauchyLevel b q =
      cauchyLevel (c - b) (pairShiftAt b q.1, pairShiftAt b q.2) := by
  simp only [cauchyLevel]
  rw [passageValue_eq_add_pairShiftAt h₁ hb hbc hc₁, passageValue_eq_add_pairShiftAt h₂ hb hbc hc₂]
  ring

/-- The first passage time at `-a` of the first path of a pair is measurable. -/
lemma measurable_hitFrom_neg_fst (a : ℝ) :
    Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => hitFrom (-a) 0 (p.1 : ℝ≥0 → ℝ) :=
  (measurable_hitFrom measurable_const (-a)).comp measurable_fst

/-- The passage value is measurable. -/
theorem measurable_passageValue (a : ℝ) : Measurable (passageValue a) :=
  (continuous_eval : Continuous fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2).measurable.comp
    (measurable_snd.prodMk (measurable_hitFrom_neg_fst a).ennreal_toNNReal)

/-- The level process at a fixed level is measurable. -/
theorem measurable_cauchyLevel (a : ℝ) : Measurable (cauchyLevel a) :=
  ((measurable_passageValue a).comp measurable_snd).sub
    ((measurable_passageValue a).comp measurable_fst)

end Pairs

end LatticeProb
