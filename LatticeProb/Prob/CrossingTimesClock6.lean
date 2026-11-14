import Mathlib
import LatticeProb.Prob.CrossingTimesClock5

/-!
# The inverse of a good clock

A *good clock* `c : ℝ≥0 → ℝ≥0∞` (`GoodClock c`) that is nondecreasing is finite and strictly
increasing at every time and unbounded.  Its inverse `A_t = clockInv c t = inf {u : t ≤ c u}` is
then finite, nondecreasing, zero at zero, a left inverse of `c` (`clockInv c (c u) = u`), and a
continuous function of `t`: a nondecreasing function whose range is all of `ℝ≥0` (every `u` is the
value at `t = c u`) has no jump.

* `GoodClock.lt_top`, `GoodClock.strictMono`, `GoodClock.exists_le`;
* `clockInv_mono`, `clockInv_zero`, `GoodClock.clockInv_lt_top`, `GoodClock.clockInv_eq`;
* `GoodClock.continuous_clockInv_toNNReal`, `GoodClock.continuous_clockInv_toReal`,
  `GoodClock.continuous_clockInv_real`.
-/

open Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section GoodClockFacts

variable {c : ℝ≥0 → ℝ≥0∞}

theorem ratTime_coe_of_lt {u : ℝ≥0} {q : ℚ} (h : (u : ℝ) < q) : ((ratTime q : ℝ≥0) : ℝ) = q := by
  unfold ratTime
  exact Real.coe_toNNReal _ (le_trans u.coe_nonneg h.le)

theorem le_ratTime_of_lt {u : ℝ≥0} {q : ℚ} (h : (u : ℝ) < q) : u ≤ ratTime q := by
  rw [← NNReal.coe_le_coe, ratTime_coe_of_lt h]
  exact h.le

theorem ratTime_lt_ratTime_of_lt {u : ℝ≥0} {q q' : ℚ} (h : (u : ℝ) < q) (hq : q < q') :
    ratTime q < ratTime q' := by
  have h' : (u : ℝ) < q' := h.trans (by exact_mod_cast hq)
  rw [← NNReal.coe_lt_coe, ratTime_coe_of_lt h, ratTime_coe_of_lt h']
  exact_mod_cast hq

theorem ratTime_le_of_lt {u u' : ℝ≥0} {q : ℚ} (h : (u : ℝ) < q) (h' : (q : ℝ) ≤ u') :
    ratTime q ≤ u' := by
  rw [← NNReal.coe_le_coe, ratTime_coe_of_lt h]
  exact h'

/-- A nondecreasing good clock is finite at every time. -/
theorem GoodClock.lt_top (hm : Monotone c) (hc : GoodClock c) (u : ℝ≥0) : c u < ⊤ := by
  obtain ⟨q, hq⟩ := exists_rat_gt (u : ℝ)
  exact (hm (le_ratTime_of_lt hq)).trans_lt (hc.2.1 q)

/-- A nondecreasing good clock is strictly increasing at every pair of times. -/
theorem GoodClock.strictMono (hm : Monotone c) (hc : GoodClock c) : StrictMono c := by
  intro u u' huu'
  obtain ⟨q, hqu, hqu'⟩ := exists_rat_btwn (show (u : ℝ) < u' from huu')
  obtain ⟨q', hqq', hq'u'⟩ := exists_rat_btwn hqu'
  have h1 : c u ≤ c (ratTime q) := hm (le_ratTime_of_lt hqu)
  have h2 : c (ratTime q) < c (ratTime q') :=
    hc.2.2.1 q q' (ratTime_lt_ratTime_of_lt hqu (by exact_mod_cast hqq'))
  have h3 : c (ratTime q') ≤ c u' :=
    hm (ratTime_le_of_lt (hqu.trans hqq') hq'u'.le)
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)

/-- A good clock is unbounded: every level is reached. -/
theorem GoodClock.exists_le (hc : GoodClock c) (t : ℝ≥0) : ∃ u : ℝ≥0, (t : ℝ≥0∞) ≤ c u := by
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨r, hr⟩ := hc.2.2.2 n
  refine ⟨ratTime r, le_trans ?_ hr⟩
  exact_mod_cast hn

/-- The inverse of a clock is nondecreasing. -/
theorem clockInv_mono (c : ℝ≥0 → ℝ≥0∞) : Monotone (clockInv c) := by
  intro t t' htt'
  refine le_iInf₂ fun u hu => iInf₂_le_of_le u (le_trans ?_ hu) le_rfl
  exact_mod_cast htt'

theorem clockInv_zero (c : ℝ≥0 → ℝ≥0∞) : clockInv c 0 = 0 :=
  le_antisymm (iInf₂_le_of_le 0 (by simp) (by simp)) zero_le

/-- The inverse of a good clock is finite. -/
theorem GoodClock.clockInv_lt_top (hc : GoodClock c) (t : ℝ≥0) : clockInv c t < ⊤ := by
  obtain ⟨u, hu⟩ := hc.exists_le t
  exact (iInf₂_le_of_le u hu le_rfl).trans_lt ENNReal.coe_lt_top

/-- The inverse of a nondecreasing good clock is a left inverse: `clockInv c (c u) = u`. -/
theorem GoodClock.clockInv_eq (hm : Monotone c) (hc : GoodClock c) {u t : ℝ≥0}
    (h : c u = (t : ℝ≥0∞)) : clockInv c t = (u : ℝ≥0∞) := by
  refine le_antisymm (iInf₂_le_of_le u h.ge le_rfl) (le_iInf₂ fun u' hu' => ?_)
  have h1 : c u ≤ c u' := h ▸ hu'
  exact_mod_cast (hc.strictMono hm).le_iff_le.1 h1

/-- The inverse of a nondecreasing good clock, read in `ℝ≥0`, is nondecreasing. -/
theorem GoodClock.monotone_clockInv_toNNReal (hc : GoodClock c) :
    Monotone fun t : ℝ≥0 => (clockInv c t).toNNReal := fun _ t' htt' =>
  ENNReal.toNNReal_mono (hc.clockInv_lt_top t').ne (clockInv_mono c htt')

/-- **Continuity of the inverse of a good clock**: a nondecreasing function onto `ℝ≥0` is
continuous. -/
theorem GoodClock.continuous_clockInv_toNNReal (hm : Monotone c) (hc : GoodClock c) :
    Continuous fun t : ℝ≥0 => (clockInv c t).toNNReal := by
  refine hc.monotone_clockInv_toNNReal.continuous_of_surjective fun u => ?_
  refine ⟨(c u).toNNReal, ?_⟩
  have h : c u = ((c u).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal (hc.lt_top hm u).ne).symm
  have := hc.clockInv_eq hm h
  simp only [this, ENNReal.toNNReal_coe]

theorem GoodClock.continuous_clockInv_toReal (hm : Monotone c) (hc : GoodClock c) :
    Continuous fun t : ℝ≥0 => (clockInv c t).toReal :=
  NNReal.continuous_coe.comp (hc.continuous_clockInv_toNNReal hm)

/-- The inverse clock as a continuous real-time process (`t ↦ A_{max t 0}`). -/
theorem GoodClock.continuous_clockInv_real (hm : Monotone c) (hc : GoodClock c) :
    Continuous fun t : ℝ => (clockInv c t.toNNReal).toReal :=
  (hc.continuous_clockInv_toReal hm).comp continuous_real_toNNReal

/-- The inverse of a nondecreasing good clock at the real time `max t 0` is nondecreasing. -/
theorem GoodClock.monotone_clockInv_real (hc : GoodClock c) :
    Monotone fun t : ℝ => (clockInv c t.toNNReal).toReal := fun _ _ htt' =>
  NNReal.coe_le_coe.2 (hc.monotone_clockInv_toNNReal (Real.toNNReal_le_toNNReal htt'))

end GoodClockFacts

end LatticeProb
