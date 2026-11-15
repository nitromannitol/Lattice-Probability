/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkSegmentRestriction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ActualWalkSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveProperties

/-! Exact restrictions of the original polygonal walk. The scaled-time
identity avoids division and includes zero total or segment duration. -/

open scoped BigOperators unitInterval

namespace BouRabeeGwynne

lemma polygonalCurve_shift_of_scaled_time {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {a m M : ℕ} (hM : a + m ≤ M)
    (u v : unitInterval)
    (hscale : (M : ℝ) * (v : ℝ) = (a : ℝ) + (m : ℝ) * (u : ℝ)) :
    polygonalCurve pos ω M v = polygonalCurve pos (fun k => ω (a + k)) m u := by
  let f : ℕ → Euc d := fun k =>
    max (0 : ℝ) (min 1 ((M : ℝ) * (v : ℝ) - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k))
  have hlo : (a : ℝ) ≤ (M : ℝ) * (v : ℝ) := by
    rw [hscale]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg m) u.property.1)
  have hhi : (M : ℝ) * (v : ℝ) ≤ (a + m : ℕ) := by
    rw [hscale, Nat.cast_add]
    exact add_le_add le_rfl (mul_le_of_le_one_right (Nat.cast_nonneg m) u.property.2)
  have htruncate : (∑ k ∈ Finset.range M, f k) = ∑ k ∈ Finset.range (a + m), f k := by
    symm
    apply Finset.sum_subset (Finset.range_mono hM)
    intro k _ hk
    have hkm : (a + m : ℕ) ≤ k := Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))
    have hkr : ((a + m : ℕ) : ℝ) ≤ k := by exact_mod_cast hkm
    have hzero : max (0 : ℝ) (min 1 ((M : ℝ) * (v : ℝ) - (k : ℝ))) = 0 :=
      max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr (hhi.trans hkr)))
    simp only [f, hzero, zero_smul]
  have hprefix : (∑ k ∈ Finset.range a, f k) = pos (ω a) - pos (ω 0) := by
    calc
      _ = ∑ k ∈ Finset.range a, (pos (ω (k + 1)) - pos (ω k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hka : (k : ℝ) + 1 ≤ a := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        have hone : max (0 : ℝ) (min 1 ((M : ℝ) * (v : ℝ) - (k : ℝ))) = 1 := by
          rw [min_eq_left (by linarith), max_eq_right zero_le_one]
        simp only [f, hone, one_smul]
      _ = _ := Finset.sum_range_sub (fun k => pos (ω k)) a
  have hshift : (∑ k ∈ Finset.range m, f (a + k)) =
      ∑ k ∈ Finset.range m,
        max (0 : ℝ) (min 1 ((m : ℝ) * (u : ℝ) - (k : ℝ))) •
          (pos (ω (a + (k + 1))) - pos (ω (a + k))) := by
    apply Finset.sum_congr rfl
    intro k _
    have heq : (M : ℝ) * (v : ℝ) - (a + k : ℕ) = (m : ℝ) * (u : ℝ) - k := by
      rw [hscale, Nat.cast_add]
      ring
    simp only [f, heq, Nat.add_assoc]
  change pos (ω 0) + ∑ k ∈ Finset.range M, f k = _
  rw [htruncate, Finset.sum_range_add, hprefix, hshift]
  change pos (ω 0) + (pos (ω a) - pos (ω 0) + _) = pos (ω (a + 0)) + _
  simp only [Nat.add_zero]
  abel

lemma clockedWalkSegment_curve_of_scaled_time {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {a b M : ℕ} (hab : a ≤ b) (hbM : b ≤ M)
    (u v : unitInterval)
    (hscale : (M : ℝ) * (v : ℝ) = (a : ℝ) + ((b - a : ℕ) : ℝ) * (u : ℝ)) :
    ClockedWalkExcursion.curve (FiniteConductanceNetwork.clockedWalkSegment pos ω a b) u =
      polygonalCurve pos ω M v := by
  have heq : ClockedWalkExcursion.curve (FiniteConductanceNetwork.clockedWalkSegment pos ω a b) =
      polygonalCurve pos (fun k => ω (a + k)) (b - a) := by
    change polygonalCurve id (fun k => pos (ω (a + min k (b - a)))) (b - a) = _
    calc
      _ = polygonalCurve id (fun k => pos (ω (a + k))) (b - a) := by
        apply ClockedWalkExcursion.polygonalCurve_congr_prefix
        intro k hk
        rw [min_eq_left hk]
      _ = _ := rfl
  rw [heq]
  exact (polygonalCurve_shift_of_scaled_time pos ω (by omega) u v hscale).symm

end BouRabeeGwynne
