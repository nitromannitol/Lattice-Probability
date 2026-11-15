/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.PhysicalExcursionRecovery at commit fdb5cad; local import paths are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WeakExcursionRecovery

/-! Exact recovery of a continuous path's finite physical-time prefix from
its consecutive excursions, allowing every physical duration to be zero. -/

open Set
open scoped unitInterval NNReal
namespace BouRabeeGwynne

noncomputable def physicalTimeSegment {d : ℕ}
    (z : EuclideanSpace ℝ (Fin d)) (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d)))
    (a b : ℝ≥0) : C(unitInterval, EuclideanSpace ℝ (Fin d)) where
  toFun u := z + ω (⟨(1 - (u : ℝ)) * a + (u : ℝ) * b,
    add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) a.property)
      (mul_nonneg u.property.1 b.property)⟩ : ℝ≥0)
  continuous_toFun := by
    apply continuous_const.add
    apply ω.continuous.comp
    fun_prop

@[simp] lemma physicalTimeSegment_zero {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (a b : ℝ≥0) :
    physicalTimeSegment z ω a b 0 = z + ω a := by
  simp [physicalTimeSegment]
  rfl

@[simp] lemma physicalTimeSegment_one {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (a b : ℝ≥0) :
    physicalTimeSegment z ω a b 1 = z + ω b := by
  simp [physicalTimeSegment]
  rfl

lemma physicalTimeSegment_self {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (a : ℝ≥0) :
    physicalTimeSegment z ω a a = ContinuousMap.const unitInterval (z + ω a) := by
  apply ContinuousMap.ext
  intro u
  change z + ω _ = z + ω a
  apply congrArg (fun t : ℝ≥0 ↦ z + ω t)
  apply Subtype.ext
  ring
  rfl

structure PhysicalTimeKnots (n : ℕ) where
  times : Fin (n + 2) → ℝ≥0
  monotone_times : Monotone times
  first : times 0 = 0

namespace PhysicalTimeKnots

variable {n d : ℕ} (A : PhysicalTimeKnots n)

def duration : ℝ≥0 := A.times (Fin.last (n + 1))

lemma time_le_duration (i : Fin (n + 2)) : A.times i ≤ A.duration :=
  A.monotone_times (Fin.le_last i)

noncomputable def normalize (hT : 0 < (A.duration : ℝ)) : WeakTimeKnots n where
  knots i := ⟨(A.times i : ℝ) / A.duration,
    div_nonneg (A.times i).property hT.le,
    (div_le_one hT).mpr (A.time_le_duration i)⟩
  monotone_knots := by
    intro i j hij
    exact div_le_div_of_nonneg_right (A.monotone_times hij) hT.le
  first := by apply Subtype.ext; simp [A.first]
  last := by apply Subtype.ext; exact div_self (ne_of_gt hT)

noncomputable def chain (z : EuclideanSpace ℝ (Fin d))
    (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) : ExcursionChain n d :=
  ⟨fun i ↦ physicalTimeSegment z ω (A.times i.castSucc) (A.times i.succ), by
    intro i j hij
    rw [physicalTimeSegment_one, physicalTimeSegment_zero, hij]⟩

lemma chain_eq_restrictChain (z : EuclideanSpace ℝ (Fin d))
    (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hT : 0 < (A.duration : ℝ)) :
    A.chain z ω = (A.normalize hT).restrictChain (physicalTimeSegment z ω 0 A.duration) := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro u
  change z + ω _ = z + ω _
  apply congrArg (fun t : ℝ≥0 ↦ z + ω t)
  apply Subtype.ext
  change (1 - (u : ℝ)) * (A.times i.castSucc : ℝ) +
      (u : ℝ) * (A.times i.succ : ℝ) =
    (1 - ((A.normalize hT).intervalParam i u : ℝ)) * 0 +
      ((A.normalize hT).intervalParam i u : ℝ) * (A.duration : ℝ)
  simp only [WeakTimeKnots.intervalParam, WeakTimeKnots.increment, normalize,
    Subtype.coe_mk, mul_zero, zero_add]
  field_simp [ne_of_gt hT]; ring

/-- The fixed concatenation clock and the actual physical clock represent
the same curve, including an identically zero total duration. -/
theorem project_concatenate_chain (P : TimePartition n)
    (z : EuclideanSpace ℝ (Fin d)) (ω : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) :
    CurveSpace.project (P.concatenate (A.chain z ω)) =
      CurveSpace.project (physicalTimeSegment z ω 0 A.duration) := by
  by_cases hT : A.duration = 0
  · have ha (i : Fin (n + 2)) : A.times i = 0 :=
      le_antisymm ((A.time_le_duration i).trans_eq hT) bot_le
    apply congrArg CurveSpace.project
    apply ContinuousMap.ext
    intro u
    rw [P.concatenate_apply (A.chain z ω) (P.interval u) (P.interval_spec u)]
    change physicalTimeSegment z ω _ _ _ = physicalTimeSegment z ω 0 A.duration u
    rw [ha, ha, hT, physicalTimeSegment_self]
    rfl
  · have hpos : 0 < (A.duration : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < A.duration)
    rw [A.chain_eq_restrictChain z ω hpos]
    exact (A.normalize hpos).project_concatenate_restrictChain P _

end PhysicalTimeKnots
end BouRabeeGwynne
