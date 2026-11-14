/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StoppedCurveProperties at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.Tactic.Abel

/-!
# Exact interpolation and stopping identities

The clamped-sum representative has the prescribed endpoints and agrees with
linear interpolation on each normalized time interval. This includes paths
which exit at step zero.
-/

open scoped BigOperators unitInterval

namespace BouRabeeGwynne

private lemma clamp_eq_zero {x : ℝ} (hx : x ≤ 0) :
    max (0 : ℝ) (min 1 x) = 0 :=
  max_eq_left ((min_le_right _ _).trans hx)

private lemma clamp_eq_one {x : ℝ} (hx : 1 ≤ x) :
    max (0 : ℝ) (min 1 x) = 1 := by
  rw [min_eq_left hx, max_eq_right zero_le_one]

private lemma clamp_eq_self {x : ℝ} (hlo : 0 ≤ x) (hhi : x ≤ 1) :
    max (0 : ℝ) (min 1 x) = x := by
  rw [min_eq_right hhi, max_eq_right hlo]

@[simp] lemma polygonalCurve_start {d : ℕ} {V : Type*} (pos : V → Euc d)
    (ω : ℕ → V) (m : ℕ) : polygonalCurve pos ω m 0 = pos (ω 0) := by
  change pos (ω 0) + ∑ k ∈ Finset.range m,
    max (0 : ℝ) (min 1 ((m : ℝ) * 0 - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k)) = pos (ω 0)
  simp only [mul_zero, zero_sub]
  have hsum : (∑ k ∈ Finset.range m,
      max (0 : ℝ) (min 1 (-(k : ℝ))) •
        (pos (ω (k + 1)) - pos (ω k))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [clamp_eq_zero (neg_nonpos.mpr (Nat.cast_nonneg k)), zero_smul]
  rw [hsum, add_zero]

@[simp] lemma polygonalCurve_end {d : ℕ} {V : Type*} (pos : V → Euc d)
    (ω : ℕ → V) (m : ℕ) : polygonalCurve pos ω m 1 = pos (ω m) := by
  change pos (ω 0) + ∑ k ∈ Finset.range m,
    max (0 : ℝ) (min 1 ((m : ℝ) * 1 - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k)) = pos (ω m)
  simp only [mul_one]
  have hsum : (∑ k ∈ Finset.range m,
      max (0 : ℝ) (min 1 ((m : ℝ) - (k : ℝ))) •
        (pos (ω (k + 1)) - pos (ω k))) =
      ∑ k ∈ Finset.range m, (pos (ω (k + 1)) - pos (ω k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : (k : ℝ) + 1 ≤ m := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    rw [clamp_eq_one (by linarith), one_smul]
  rw [hsum]
  exact (Finset.eq_sum_range_sub (fun k ↦ pos (ω k)) m).symm

/-- On one step's time interval, the representative is the affine segment
from the current vertex to the next, with affine parameter `m * t - j`. -/
lemma polygonalCurve_on_segment_scaled {d : ℕ} {V : Type*} (pos : V → Euc d)
    (ω : ℕ → V) {m j : ℕ} (hj : j < m) (t : unitInterval)
    (hlo : (j : ℝ) ≤ (m : ℝ) * (t : ℝ))
    (hhi : (m : ℝ) * (t : ℝ) ≤ (j : ℝ) + 1) :
    polygonalCurve pos ω m t = pos (ω j) +
      ((m : ℝ) * (t : ℝ) - (j : ℝ)) •
        (pos (ω (j + 1)) - pos (ω j)) := by
  let f : ℕ → Euc d := fun k ↦
    max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k))
  have htruncate : (∑ k ∈ Finset.range m, f k) =
      ∑ k ∈ Finset.range (j + 1), f k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj))
    intro k _ hk
    have hjk : (j : ℝ) + 1 ≤ k := by
      exact_mod_cast Nat.le_of_not_gt (fun h ↦ hk (Finset.mem_range.mpr h))
    dsimp [f]
    rw [clamp_eq_zero (by linarith), zero_smul]
  have hprefix : (∑ k ∈ Finset.range j, f k) = pos (ω j) - pos (ω 0) := by
    calc
      (∑ k ∈ Finset.range j, f k) =
          ∑ k ∈ Finset.range j, (pos (ω (k + 1)) - pos (ω k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkj : (k : ℝ) + 1 ≤ j := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        dsimp [f]
        rw [clamp_eq_one (by linarith), one_smul]
      _ = pos (ω j) - pos (ω 0) :=
        Finset.sum_range_sub (fun k ↦ pos (ω k)) j
  have hcurrent : f j = ((m : ℝ) * (t : ℝ) - (j : ℝ)) •
      (pos (ω (j + 1)) - pos (ω j)) := by
    dsimp [f]
    rw [clamp_eq_self (by linarith) (by linarith)]
  change pos (ω 0) + (∑ k ∈ Finset.range m, f k) = _
  rw [htruncate, Finset.sum_range_succ, hprefix, hcurrent]
  abel

/-- The same exact formula with the normalized interval written as
`[j/m, (j+1)/m]`. The assumption `j < m` also ensures the divisor is positive. -/
lemma polygonalCurve_on_segment {d : ℕ} {V : Type*} (pos : V → Euc d)
    (ω : ℕ → V) {m j : ℕ} (hj : j < m) (t : unitInterval)
    (hlo : (j : ℝ) / (m : ℝ) ≤ (t : ℝ))
    (hhi : (t : ℝ) ≤ ((j : ℝ) + 1) / (m : ℝ)) :
    polygonalCurve pos ω m t = pos (ω j) +
      ((m : ℝ) * (t : ℝ) - (j : ℝ)) •
        (pos (ω (j + 1)) - pos (ω j)) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hj
  apply polygonalCurve_on_segment_scaled pos ω hj t
  · simpa only [mul_comm] using (div_le_iff₀ hm).mp hlo
  · simpa only [mul_comm] using (le_div_iff₀ hm).mp hhi

@[simp] lemma stoppedPolygonalCurve_of_exitTime_zero {d : ℕ} {V : Type*}
    (pos : V → Euc d) (A : Set V) (ω : ℕ → V)
    (hτ : FiniteConductanceNetwork.exitTime A ω = 0) :
    stoppedPolygonalCurve pos A ω =
      CurveSpace.project (ContinuousMap.const _ (pos (ω 0))) := by
  simp [stoppedPolygonalCurve, hτ]

lemma stoppedPolygonalCurve_of_start_not_mem {d : ℕ} {V : Type*}
    (pos : V → Euc d) (A : Set V) (ω : ℕ → V) (hω : ω 0 ∉ A) :
    stoppedPolygonalCurve pos A ω =
      CurveSpace.project (ContinuousMap.const _ (pos (ω 0))) :=
  stoppedPolygonalCurve_of_exitTime_zero pos A ω
    (FiniteConductanceNetwork.exitTime_eq_zero_of_not_mem hω)

@[simp] lemma stoppedPolygonalCurve_endPoint {d : ℕ} {V : Type*}
    (pos : V → Euc d) (A : Set V) (ω : ℕ → V) :
    CurveSpace.endPoint (stoppedPolygonalCurve pos A ω) =
      pos (ω ((FiniteConductanceNetwork.exitTime A ω).untopD 0)) := by
  change polygonalCurve pos ω ((FiniteConductanceNetwork.exitTime A ω).untopD 0) 1 = _
  exact polygonalCurve_end _ _ _

end BouRabeeGwynne
