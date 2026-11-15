/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppedEndpoint at commit fdb5cad; local import path is adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory

/-! Permanent absorption keeps the actual current endpoint outside the
selector's continuation set; the finite pasted representative has that endpoint. -/

open MeasureTheory Set
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

set_option linter.unusedSectionVars false in
theorem brownianSkeletonClock_position_not_mem_of_stopped (W : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J)
    {C : Set (Euc d)} (hnone : ∀ k x, selector k x = none → x ∉ C)
    (n : ℕ) (ω : BrownianPath d)
    (hstop : (brownianSkeletonClock W z j₀ selector n ω).1 = true) :
    z + ω (brownianSkeletonClock W z j₀ selector n ω).2.toNNReal ∉ C := by
  induction n with
  | zero => cases hstop
  | succ n ih =>
    by_cases hp : (brownianSkeletonClock W z j₀ selector n ω).1 = true
    · rw [brownianSkeletonClock_absorbed W z j₀ selector n ω hp]
      exact ih hp
    · have hc : brownianClockChoice z (selector (n + 1))
          (brownianSkeletonClock W z j₀ selector n) ω = none := by
        change (brownianClockChoice z (selector (n + 1))
          (brownianSkeletonClock W z j₀ selector n) ω).isNone = true at hstop
        cases he : brownianClockChoice z (selector (n + 1))
            (brownianSkeletonClock W z j₀ selector n) ω with
        | none => rfl
        | some j => simp only [he, Option.isNone_some] at hstop; cases hstop
      have hsel : selector (n + 1)
          (z + ω (brownianSkeletonClock W z j₀ selector n ω).2.toNNReal) = none := by
        simpa only [brownianClockChoice, ite_eq_right hp] using hc
      have ht : (brownianSkeletonClock W z j₀ selector (n + 1) ω).2 =
          (brownianSkeletonClock W z j₀ selector n ω).2 := by
        change brownianSelectedNextExitTime W z
          (fun η ↦ (brownianSkeletonClock W z j₀ selector n η).2)
          (brownianClockChoice z (selector (n + 1)) (brownianSkeletonClock W z j₀ selector n)) ω = _
        simp only [brownianSelectedNextExitTime, hc]
      rw [ht]
      exact hnone (n + 1) _ hsel

theorem brownianSkeleton_concatenate_endPoint (W : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J)
    (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock W z j₀ selector n ω).2 ≠ ∞) (P : TimePartition n) :
    P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k ↦ (brownianSkeletonExcursion W z j₀ selector k ω).2)) 1 =
      z + ω (brownianSkeletonClock W z j₀ selector n ω).2.toNNReal := by
  have he := congrArg CurveSpace.endPoint
    (brownianSkeleton_concatenatedCurve_eq_prefix W z j₀ selector n ω hfinite P)
  change P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k ↦ (brownianSkeletonExcursion W z j₀ selector k ω).2)) 1 =
    physicalTimeSegment z ω 0 (brownianSkeletonClock W z j₀ selector n ω).2.toNNReal 1 at he
  simpa only [physicalTimeSegment_one] using he

theorem standardBrownianLaw_skeleton_ae_stopped_endPoint_outside (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (hselector : ∀ k, Measurable (selector k))
    {C : Set (Euc d)} (hC : MeasurableSet C)
    (hnone : ∀ k x, selector k x = none → x ∉ C) (n : ℕ) (P : TimePartition n) :
    ∀ᵐ γ ∂μ.map (fun ω k ↦ brownianSkeletonExcursion W z j₀ selector k ω),
      (γ n).1 = true →
      P.concatenate (ExcursionTrajectory.prefixChain n d (fun k ↦ (γ k).2)) 1 ∉ C := by
  have hΓ : Measurable (fun ω k ↦ brownianSkeletonExcursion W z j₀ selector k ω) := by
    apply Measurable.of_eval
    intro k
    exact measurable_brownianSkeletonExcursion W hW z j₀ hselector k
  have hm : Measurable (fun γ : ℕ → Bool × C(unitInterval, Euc d) ↦ fun k ↦ (γ k).2) := by
    apply Measurable.of_eval
    intro k
    exact measurable_snd.comp (measurable_pi_apply k)
  have hend : Measurable (fun γ : ℕ → Bool × C(unitInterval, Euc d) ↦
      P.concatenate (ExcursionTrajectory.prefixChain n d (fun k ↦ (γ k).2)) 1) :=
    (ContinuousMap.measurable_eval 1).comp
      (P.measurable_concatenate.comp ((ExcursionTrajectory.measurable_prefixChain n d).comp hm))
  have hset : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) | (γ n).1 = true →
      P.concatenate (ExcursionTrajectory.prefixChain n d (fun k ↦ (γ k).2)) 1 ∉ C} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply n))
      measurable_const).compl.union (hC.preimage hend).compl
  apply (ae_map_iff hΓ.aemeasurable hset).mpr
  filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ W hW hWb z j₀ hselector n]
    with ω hfinite
  intro hstop
  rw [brownianSkeletonExcursion_flag] at hstop
  rw [brownianSkeleton_concatenate_endPoint W z j₀ selector n ω hfinite P]
  exact brownianSkeletonClock_position_not_mem_of_stopped W z j₀ selector hnone n ω hstop

end BouRabeeGwynne
