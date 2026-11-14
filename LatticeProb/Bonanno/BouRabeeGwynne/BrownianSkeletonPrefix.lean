/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonPrefix at commit fdb5cad; only the clock lemmas are retained. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonClock

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

lemma brownianSkeletonClock_time_monotone (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (ω : BrownianPath d) :
    Monotone (fun n ↦ (brownianSkeletonClock U z j₀ selector n ω).2) :=
  monotone_nat_of_le_succ (fun n ↦ brownianSkeletonClock_time_le_succ U z j₀ selector n ω)

lemma brownianSkeletonClock_finite_of_le (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (ω : BrownianPath d) {m n : ℕ} (hmn : m ≤ n)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) :
    (brownianSkeletonClock U z j₀ selector m ω).2 ≠ ∞ :=
  ne_top_of_le_ne_top hfinite (brownianSkeletonClock_time_monotone U z j₀ selector ω hmn)

end BouRabeeGwynne
