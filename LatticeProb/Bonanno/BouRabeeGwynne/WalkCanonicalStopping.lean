/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkCanonicalStopping at commit fdb5cad; imports are relocated and later exports are omitted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExitParameter
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStoppedReconstruction
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianBoundaryExcursion

/-! The measurable curve obtained by pasting a finite prefix of walk excursions, and its canonical stopping support. -/

open MeasureTheory Set
open scoped unitInterval

namespace BouRabeeGwynne

noncomputable def pastedWalkCurve {d n : ℕ} (P : TimePartition n)
    (e : ℕ → Bool × ClockedWalkExcursion d) : C(unitInterval, Euc d) :=
  P.concatenate (ExcursionTrajectory.prefixChain n d
    (fun k => ClockedWalkExcursion.curve (e k).2))

lemma measurable_pastedWalkCurve {d n : ℕ} (P : TimePartition n) :
    Measurable (pastedWalkCurve (d := d) P) :=
  P.measurable_concatenate.comp ((ExcursionTrajectory.measurable_prefixChain n d).comp
    (Measurable.of_eval fun k => ClockedWalkExcursion.measurable_curve.comp
      (measurable_pi_apply k).snd))

def canonicalWalkStoppingSupport {d n : ℕ} (U : Set (Euc d)) (δ : ℝ) (P : TimePartition n) :
    Set (ℕ → Bool × ClockedWalkExcursion d) :=
  {e | let f := pastedWalkCurve P e
       let a := ClockedWalkExcursion.pastedVertexExitParameter U P e
       CurveSpace.project (prefixUnitCurve f a) = reconstructedVertexStoppedCurve U n e ∧
       f a ∉ U ∧ (a = 0 ∨ prefixUnitCurve f a ∈ curveRangeEvent (Metric.cthickening δ U))}

lemma measurableSet_canonicalWalkStoppingSupport {d n : ℕ} {U : Set (Euc d)}
    (hU : MeasurableSet U) (δ : ℝ) (P : TimePartition n) :
    MeasurableSet (canonicalWalkStoppingSupport U δ P) := by
  have hf := measurable_pastedWalkCurve (d := d) P
  have ha := ClockedWalkExcursion.measurable_pastedVertexExitParameter hU P
  have hp := measurable_prefixUnitCurve.comp (hf.prodMk ha)
  have heval : Measurable (fun p : C(unitInterval, Euc d) × unitInterval => p.1 p.2) :=
    (by fun_prop : Continuous (fun p : C(unitInterval, Euc d) × unitInterval => p.1 p.2)).measurable
  exact (measurableSet_eq_fun (CurveSpace.continuous_project.measurable.comp hp)
      (measurable_reconstructedVertexStoppedCurve hU n)).inter
    ((hU.compl.preimage (heval.comp (hf.prodMk ha))).inter
      ((measurableSet_eq_fun ha measurable_const).union
        ((isClosed_curveRangeEvent Metric.isClosed_cthickening).measurableSet.preimage hp)))

lemma canonicalWalkStoppingSupport_pre {d n : ℕ} {U : Set (Euc d)} {δ : ℝ}
    {P : TimePartition n} {e : ℕ → Bool × ClockedWalkExcursion d}
    (he : e ∈ canonicalWalkStoppingSupport U δ P) :
    ∀ t < ClockedWalkExcursion.pastedVertexExitParameter U P e,
      pastedWalkCurve P e t ∈ Metric.cthickening δ U := by
  intro t ht
  rcases he.2.2 with hz | hrange
  · rw [hz] at ht
    exact False.elim ((not_lt_of_ge (show (0 : unitInterval) ≤ t from t.property.1)) ht)
  · let a := ClockedWalkExcursion.pastedVertexExitParameter U P e
    have ha : (0 : ℝ) < a := lt_of_le_of_lt t.property.1 ht
    let u : unitInterval := ⟨(t : ℝ) / a, div_nonneg t.property.1 ha.le,
      (div_le_one ha).mpr ht.le⟩
    have heq : a * u = t := by
      apply Subtype.ext
      change (a : ℝ) * ((t : ℝ) / a) = t
      rw [mul_comm, div_mul_cancel₀ _ ha.ne']
    have h := hrange u
    change pastedWalkCurve P e (a * u) ∈ Metric.cthickening δ U at h
    rw [heq] at h
    exact h

end BouRabeeGwynne
