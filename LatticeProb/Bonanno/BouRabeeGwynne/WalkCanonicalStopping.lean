/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkCanonicalStopping at commit fdb5cad; imports are relocated and later exports are omitted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory

/-! The measurable curve obtained by pasting a finite prefix of walk excursions. -/

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

end BouRabeeGwynne
