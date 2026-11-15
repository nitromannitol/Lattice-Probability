/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WeakExcursionClock at commit fdb5cad; module paths and a deprecated lemma name are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionConcatenation
import LatticeProb.Bonanno.BouRabeeGwynne.CurvePauses
import Mathlib.Algebra.BigOperators.Intervals

/-! A genuine continuous monotone clock for consecutive pieces with possibly
zero physical duration. The source partition remains strictly increasing. -/

open Set
open scoped unitInterval
namespace BouRabeeGwynne

structure WeakTimeKnots (n : ℕ) where
  knots : Fin (n + 2) → unitInterval
  monotone_knots : Monotone knots
  first : knots 0 = 0
  last : knots (Fin.last (n + 1)) = 1

namespace WeakTimeKnots

variable {n : ℕ} (Q : WeakTimeKnots n)

def increment (i : Fin (n + 1)) : ℝ := Q.knots i.succ - Q.knots i.castSucc

lemma increment_nonneg (i : Fin (n + 1)) : 0 ≤ Q.increment i :=
  sub_nonneg.mpr (Q.monotone_knots i.castSucc_lt_succ.le)

lemma sum_increment_Iio (i : Fin (n + 1)) :
    ∑ j ∈ Finset.Iio i, Q.increment j = (Q.knots i.castSucc : ℝ) := by
  rw [← Finset.Iic_erase, Finset.sum_erase_eq_sub (Finset.mem_Iic.mpr le_rfl)]
  change (∑ j ∈ Finset.Iic i, ((Q.knots j.succ : ℝ) - Q.knots j.castSucc)) -
    ((Q.knots i.succ : ℝ) - Q.knots i.castSucc) = _
  rw [Fin.sum_Iic_sub i (fun j ↦ (Q.knots j : ℝ))]
  simp only [Q.first, Set.Icc.coe_zero]
  ring

lemma sum_increment : ∑ i, Q.increment i = 1 := by
  have h := Fin.sum_Iic_sub (Fin.last n) (fun i ↦ (Q.knots i : ℝ))
  have hIic : Finset.Iic (Fin.last n) = Finset.univ := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact Fin.le_last i
  rw [hIic] at h
  simpa only [increment, Fin.succ_last, Q.first, Q.last,
    Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero] using h

end WeakTimeKnots

namespace TimePartition

variable {n : ℕ} (P : TimePartition n)

lemma monotone_localTime (i : Fin (n + 1)) : Monotone (P.localTime i) := by
  intro s t hst
  apply monotone_projIcc zero_le_one
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (show (s : ℝ) ≤ t from hst) _) (P.gap_pos i).le

lemma localTime_eq_zero_of_le (i : Fin (n + 1)) {t : unitInterval} (ht : t ≤ P.left i) :
    P.localTime i t = 0 := by
  apply le_antisymm
  · exact (P.monotone_localTime i ht).trans_eq (P.localTime_left i)
  · exact (P.localTime i t).property.1

lemma localTime_eq_one_of_le (i : Fin (n + 1)) {t : unitInterval} (ht : P.right i ≤ t) :
    P.localTime i t = 1 := by
  apply le_antisymm
  · exact (P.localTime i t).property.2
  · exact (P.localTime_right i).symm.trans_le (P.monotone_localTime i ht)

noncomputable def weakClockReal (Q : WeakTimeKnots n) (t : unitInterval) : ℝ :=
  ∑ i, Q.increment i * (P.localTime i t : ℝ)

lemma weakClockReal_nonneg (Q : WeakTimeKnots n) (t : unitInterval) :
    0 ≤ P.weakClockReal Q t :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg (Q.increment_nonneg i) (P.localTime i t).property.1)

lemma weakClockReal_le_one (Q : WeakTimeKnots n) (t : unitInterval) :
    P.weakClockReal Q t ≤ 1 := by
  rw [← Q.sum_increment]
  exact Finset.sum_le_sum (fun i _ ↦
    mul_le_of_le_one_right (Q.increment_nonneg i) (P.localTime i t).property.2)

lemma continuous_weakClockReal (Q : WeakTimeKnots n) : Continuous (P.weakClockReal Q) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((P.continuous_localTime i).subtype_val)

noncomputable def weakClock (Q : WeakTimeKnots n) : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨P.weakClockReal Q t, P.weakClockReal_nonneg Q t, P.weakClockReal_le_one Q t⟩,
    (P.continuous_weakClockReal Q).subtype_mk _⟩

lemma weakClock_monotone (Q : WeakTimeKnots n) : Monotone (P.weakClock Q) := by
  intro s t hst
  change P.weakClockReal Q s ≤ P.weakClockReal Q t
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left
    (show (P.localTime i s : ℝ) ≤ P.localTime i t from P.monotone_localTime i hst)
    (Q.increment_nonneg i))

@[simp] lemma weakClock_zero (Q : WeakTimeKnots n) : P.weakClock Q 0 = 0 := by
  apply Subtype.ext
  change (∑ i, Q.increment i * (P.localTime i 0 : ℝ)) = 0
  have hz (i : Fin (n + 1)) : P.localTime i 0 = 0 :=
    P.localTime_eq_zero_of_le i (P.left i).property.1
  simp only [hz, Set.Icc.coe_zero, mul_zero, Finset.sum_const_zero]

@[simp] lemma weakClock_one (Q : WeakTimeKnots n) : P.weakClock Q 1 = 1 := by
  apply Subtype.ext
  change (∑ i, Q.increment i * (P.localTime i 1 : ℝ)) = 1
  have ho (i : Fin (n + 1)) : P.localTime i 1 = 1 :=
    P.localTime_eq_one_of_le i (P.right i).property.2
  simp only [ho, Set.Icc.coe_one, mul_one]
  exact Q.sum_increment

theorem weakClock_apply (Q : WeakTimeKnots n) (i : Fin (n + 1)) {t : unitInterval}
    (ht : P.left i ≤ t ∧ t ≤ P.right i) :
    (P.weakClock Q t : ℝ) =
      (Q.knots i.castSucc : ℝ) + (P.localTime i t : ℝ) * Q.increment i := by
  change (∑ j, Q.increment j * (P.localTime j t : ℝ)) = _
  have hsum : (∑ j, Q.increment j * (P.localTime j t : ℝ)) =
      ∑ j ∈ Finset.Iic i, Q.increment j * (P.localTime j t : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hij : i < j := lt_of_not_ge (by simpa only [Finset.mem_Iic] using hj)
    rw [P.localTime_eq_zero_of_le j (ht.2.trans (P.right_le_left hij)),
      Set.Icc.coe_zero, mul_zero]
  rw [hsum, ← Finset.Iio_insert, Finset.sum_insert (by simp)]
  have hearlier : (∑ j ∈ Finset.Iio i, Q.increment j * (P.localTime j t : ℝ)) =
      ∑ j ∈ Finset.Iio i, Q.increment j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [P.localTime_eq_one_of_le j ((P.right_le_left (Finset.mem_Iio.mp hj)).trans ht.1),
      Set.Icc.coe_one, mul_one]
  rw [hearlier, Q.sum_increment_Iio]
  ring

end TimePartition
end BouRabeeGwynne
