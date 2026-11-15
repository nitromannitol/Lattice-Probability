/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WeakExcursionRecovery at commit fdb5cad; local import paths are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WeakExcursionClock

/-! Pasting the actual restrictions of a path recovers its Fréchet class even
when some physical intervals have zero duration. -/

open Set
open scoped unitInterval
namespace BouRabeeGwynne.WeakTimeKnots

variable {n d : ℕ} (Q : WeakTimeKnots n)

noncomputable def intervalParam (i : Fin (n + 1)) (u : unitInterval) : unitInterval :=
  ⟨Q.knots i.castSucc + (u : ℝ) * Q.increment i,
    ⟨add_nonneg (Q.knots i.castSucc).property.1
      (mul_nonneg u.property.1 (Q.increment_nonneg i)), by
      have hm := mul_le_of_le_one_left (Q.increment_nonneg i) u.property.2
      have heq : (Q.knots i.castSucc : ℝ) + Q.increment i = Q.knots i.succ := by
        unfold increment
        ring
      exact (add_le_add_right hm (Q.knots i.castSucc)).trans
        (heq.le.trans (Q.knots i.succ).property.2)⟩⟩

lemma continuous_intervalParam (i : Fin (n + 1)) : Continuous (Q.intervalParam i) := by
  unfold intervalParam
  fun_prop

@[simp] lemma intervalParam_zero (i : Fin (n + 1)) :
    Q.intervalParam i 0 = Q.knots i.castSucc := by
  apply Subtype.ext
  simp [intervalParam]

@[simp] lemma intervalParam_one (i : Fin (n + 1)) :
    Q.intervalParam i 1 = Q.knots i.succ := by
  apply Subtype.ext
  simp [intervalParam, increment]

noncomputable def restrictChain (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    ExcursionChain n d :=
  ⟨fun i ↦ ⟨fun u ↦ f (Q.intervalParam i u),
      f.continuous.comp (Q.continuous_intervalParam i)⟩, by
    intro i j hij
    change f (Q.intervalParam i 1) = f (Q.intervalParam j 0)
    rw [Q.intervalParam_one, Q.intervalParam_zero, hij]⟩

theorem concatenate_restrictChain (P : TimePartition n)
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    P.concatenate (Q.restrictChain f) = f.comp (P.weakClock Q) := by
  apply ContinuousMap.ext
  intro t
  let i := P.interval t
  have ht := P.interval_spec t
  rw [P.concatenate_apply (Q.restrictChain f) i ht]
  change f (Q.intervalParam i (P.localTime i t)) = f (P.weakClock Q t)
  apply congrArg f
  apply Subtype.ext
  exact (P.weakClock_apply Q i ht).symm

/-- An actual equality in the metric quotient, including all constant pieces. -/
theorem project_concatenate_restrictChain (P : TimePartition n)
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    CurveSpace.project (P.concatenate (Q.restrictChain f)) = CurveSpace.project f := by
  rw [Q.concatenate_restrictChain]
  exact curveSpace_project_comp_monotone f (P.weakClock Q)
    (P.weakClock_monotone Q) (P.weakClock_zero Q) (P.weakClock_one Q)

end BouRabeeGwynne.WeakTimeKnots
