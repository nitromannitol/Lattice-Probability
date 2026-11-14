/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianNestedClock at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNestedExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonExcursion

/-! Deterministic nested excursions use exactly the first exits of the
original path, including infinite exit times. -/

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

theorem brownianSkeletonClock_nested {d : ℕ} (U : ℕ → Set (Euc d))
    (hU : Monotone U) (z : Euc d) (n : ℕ) (ω : BrownianPath d) :
    brownianSkeletonClock U z 0 (fun n _ => some n) n ω =
      (false, continuousExitTime (U n) z ω) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
    have hclock : brownianSkeletonClock U z 0 (fun n _ => some n) n =
        fun η => (false, continuousExitTime (U n) z η) := funext ih
    simp only [brownianSkeletonClock, brownianClockUpdate, brownianClockChoice,
      hclock, Bool.false_eq_true, ite_false, Option.isNone_some,
      brownianSelectedNextExitTime]
    exact congrArg (fun t : ℝ≥0∞ => (false, t))
      (brownianNextExitTime_from_nested_exit (hU (Nat.le_succ n)) z ω)

lemma stoppedBrownianRepresentative_range_subset {d : ℕ}
    (U K : Set (Euc d)) (x : Euc d) (ω : BrownianPath d)
    (hstay : ∀ t : ℝ≥0, t ≤ (continuousExitTime U x ω).toNNReal → x + ω t ∈ K) :
    range (stoppedBrownianRepresentative U x ω) ⊆ K := by
  rintro _ ⟨u, rfl⟩
  apply hstay
  change (u : ℝ) * ((continuousExitTime U x ω).toNNReal : ℝ) ≤
    ((continuousExitTime U x ω).toNNReal : ℝ)
  exact mul_le_of_le_one_left (NNReal.coe_nonneg _) u.property.2

lemma stoppedBrownianNextRepresentative_range_subset {d : ℕ}
    (U K : Set (Euc d)) (z : Euc d) (τ : BrownianPath d → ℝ≥0∞)
    (ω : BrownianPath d) (hfinite : brownianNextExitTime U z τ ω ≠ ∞)
    (hstay : ∀ t : ℝ≥0, t ≤ (brownianNextExitTime U z τ ω).toNNReal →
      z + ω t ∈ K) :
    range (stoppedBrownianRepresentative U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω)) ⊆ K := by
  have hparts := ENNReal.add_ne_top.mp hfinite
  apply stoppedBrownianRepresentative_range_subset
  intro t ht
  have htime : (τ ω).toNNReal + t ≤ (brownianNextExitTime U z τ ω).toNNReal := by
    rw [brownianNextExitTime, ENNReal.toNNReal_add hparts.1 hparts.2]
    exact add_le_add le_rfl ht
  have hmem := hstay _ htime
  have heq : (z + ω (τ ω).toNNReal) + shiftedBrownianPath (τ ω).toNNReal ω t =
      z + ω ((τ ω).toNNReal + t) := by
    change (z + ω (τ ω).toNNReal) +
      (ω ((τ ω).toNNReal + t) - ω (τ ω).toNNReal) = _
    abel
  exact heq ▸ hmem

theorem brownianSkeletonExcursion_nested_range_subset {d : ℕ}
    (U : ℕ → Set (Euc d)) (hU : Monotone U) (K : Set (Euc d))
    (z : Euc d) (ω : BrownianPath d) (N : ℕ)
    (hfinite : continuousExitTime (U N) z ω ≠ ∞)
    (hstay : ∀ t : ℝ≥0, t ≤ (continuousExitTime (U N) z ω).toNNReal → z + ω t ∈ K)
    (i : ℕ) (hi : i ≤ N) :
    range (brownianSkeletonExcursion U z 0 (fun n _ => some n) i ω).2 ⊆ K := by
  have hle := continuousExitTime_mono (hU hi) z ω
  have hfi := ne_top_of_le_ne_top hfinite hle
  have ht : (continuousExitTime (U i) z ω).toNNReal ≤
      (continuousExitTime (U N) z ω).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_toNNReal hfi, ENNReal.coe_toNNReal hfinite] using hle
  cases i with
  | zero =>
    exact stoppedBrownianRepresentative_range_subset (U 0) K z ω
      (fun t h => hstay t (h.trans ht))
  | succ i =>
    have heq := brownianNextExitTime_from_nested_exit (hU (Nat.le_succ i)) z ω
    have hclock : brownianSkeletonClock U z 0 (fun n _ => some n) i =
        fun η => (false, continuousExitTime (U i) z η) :=
      funext (brownianSkeletonClock_nested U hU z i)
    simp only [brownianSkeletonExcursion, brownianClockChoice, hclock,
      Bool.false_eq_true, ite_false, selectedBrownianExcursionSampler]
    apply stoppedBrownianNextRepresentative_range_subset (U (i + 1)) K z
      (continuousExitTime (U i) z) ω
    · simpa only [heq] using hfi
    · intro t h
      rw [heq] at h
      exact hstay t (h.trans ht)

end BouRabeeGwynne
