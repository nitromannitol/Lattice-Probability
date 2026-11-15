/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonPrefix at commit fdb5cad; local import paths are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonClock
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianPhysicalSegments
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonLaw
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory

/-! The actual finite Brownian excursion prefix is the original path prefix
with its genuine stopping duration. Both pointwise and Fréchet recovery are retained. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal unitInterval
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

noncomputable def brownianSkeletonPhysicalKnots (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) : PhysicalTimeKnots n where
  times := Fin.cases 0 (fun i ↦ (brownianSkeletonClock U z j₀ selector i.val ω).2.toNNReal)
  monotone_times := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · exact bot_le
    · exact ENNReal.toNNReal_mono
        (brownianSkeletonClock_finite_of_le U z j₀ selector ω (by omega) hfinite)
        (brownianSkeletonClock_time_le_succ U z j₀ selector k.val ω)
  first := rfl

@[simp] lemma brownianSkeletonPhysicalKnots_duration (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) :
    (brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite).duration =
      (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal := rfl

theorem brownianSkeletonPhysicalKnots_chain_apply (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) (i : Fin (n + 1)) :
    ((brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite).chain z ω).val i =
      (brownianSkeletonExcursion U z j₀ selector i.val ω).2 := by
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · change physicalTimeSegment z ω 0 (continuousExitTime (U j₀) z ω).toNNReal =
      stoppedBrownianRepresentative (U j₀) z ω
    exact (stoppedBrownianRepresentative_eq_physicalTimeSegment (U j₀) z ω).symm
  · change physicalTimeSegment z ω
        (brownianSkeletonClock U z j₀ selector k.val ω).2.toNNReal
        (brownianSkeletonClock U z j₀ selector (k.val + 1) ω).2.toNNReal =
      (brownianSkeletonExcursion U z j₀ selector (k.val + 1) ω).2
    rw [brownianSkeletonExcursion]
    dsimp only
    cases hc : brownianClockChoice z (selector (k.val + 1))
        (brownianSkeletonClock U z j₀ selector k.val) ω with
    | none =>
      have ht : (brownianSkeletonClock U z j₀ selector (k.val + 1) ω).2 =
          (brownianSkeletonClock U z j₀ selector k.val ω).2 := by
        change brownianSelectedNextExitTime U z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector k.val η).2)
          (brownianClockChoice z (selector (k.val + 1))
            (brownianSkeletonClock U z j₀ selector k.val)) ω = _
        simp only [brownianSelectedNextExitTime, hc]
      simp only [selectedBrownianExcursionSampler, ht, physicalTimeSegment_self]
    | some j =>
      have ht : (brownianSkeletonClock U z j₀ selector (k.val + 1) ω).2 =
          brownianNextExitTime (U j) z
            (fun η ↦ (brownianSkeletonClock U z j₀ selector k.val η).2) ω := by
        change brownianSelectedNextExitTime U z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector k.val η).2)
          (brownianClockChoice z (selector (k.val + 1))
            (brownianSkeletonClock U z j₀ selector k.val)) ω = _
        simp only [brownianSelectedNextExitTime, hc]
      have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω
        (show k.val + 1 ≤ n by omega) hfinite
      rw [ht] at hf ⊢
      simpa only [hc, selectedBrownianExcursionSampler] using
        (stoppedBrownianNextRepresentative_eq_physicalTimeSegment (U j) z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector k.val η).2) ω hf).symm

theorem brownianSkeleton_prefixChain_eq (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) :
    ExcursionTrajectory.prefixChain n d (fun k ↦ (brownianSkeletonExcursion U z j₀ selector k ω).2) =
      (brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite).chain z ω := by
  let A := brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite
  have heq := brownianSkeletonPhysicalKnots_chain_apply U z j₀ selector n ω hfinite
  have hcompat : (fun k ↦ (brownianSkeletonExcursion U z j₀ selector k ω).2) ∈
      ExcursionTrajectory.compatiblePaths n d := by
    intro i j hij
    change (brownianSkeletonExcursion U z j₀ selector i.val ω).2 1 =
      (brownianSkeletonExcursion U z j₀ selector j.val ω).2 0
    rw [← heq i, ← heq j]
    exact (A.chain z ω).property i j hij
  apply Subtype.ext
  funext i
  rw [ExcursionTrajectory.prefixChain_apply hcompat]
  exact (heq i).symm

/-- Pointwise recovery retains the monotone clock for later stopping arguments. -/
theorem brownianSkeleton_concatenate_eq_comp (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞)
    (hpos : 0 < ((brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite).duration : ℝ))
    (P : TimePartition n) :
    P.concatenate (ExcursionTrajectory.prefixChain n d
        (fun k ↦ (brownianSkeletonExcursion U z j₀ selector k ω).2)) =
      (physicalTimeSegment z ω 0 (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal).comp
        (P.weakClock ((brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite).normalize hpos)) := by
  rw [brownianSkeleton_prefixChain_eq U z j₀ selector n ω hfinite,
    PhysicalTimeKnots.chain_eq_restrictChain _ z ω hpos,
    WeakTimeKnots.concatenate_restrictChain]
  rfl

/-- Exact recovery of the genuine prefix in curve space, including duration zero. -/
theorem brownianSkeleton_concatenatedCurve_eq_prefix (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) (P : TimePartition n) :
    ExcursionTrajectory.concatenatedCurve P (fun k ↦ (brownianSkeletonExcursion U z j₀ selector k ω).2) =
      CurveSpace.project
        (physicalTimeSegment z ω 0 (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal) := by
  unfold ExcursionTrajectory.concatenatedCurve
  rw [brownianSkeleton_prefixChain_eq U z j₀ selector n ω hfinite]
  exact (brownianSkeletonPhysicalKnots U z j₀ selector n ω hfinite).project_concatenate_chain P z ω

end BouRabeeGwynne
