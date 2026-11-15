/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppedSkeleton at commit fdb5cad; local import paths and a deprecated lemma name are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonPrefix
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveExitMonotone
import LatticeProb.Bonanno.BouRabeeGwynne.PhysicalPrefixExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail
import LatticeProb.Bonanno.BouRabeeGwynne.ReconstructedLawComparison

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem brownianSkeletonClock_exit_le_of_stopped (W : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J)
    {U : Set (Euc d)} (hnone : ∀ n x, selector n x = none → x ∉ U)
    (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock W z j₀ selector n ω).2 ≠ ∞)
    (hstop : (brownianSkeletonClock W z j₀ selector n ω).1 = true) :
    continuousExitTime U z ω ≤ (brownianSkeletonClock W z j₀ selector n ω).2 := by
  induction n with
  | zero => cases hstop
  | succ n ih =>
    have hfprev := brownianSkeletonClock_finite_of_le W z j₀ selector ω (Nat.le_succ n) hfinite
    by_cases hp : (brownianSkeletonClock W z j₀ selector n ω).1 = true
    · exact (ih hfprev hp).trans (brownianSkeletonClock_time_le_succ W z j₀ selector n ω)
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
      have he := continuousExitTime_le_of_not_mem (hnone (n + 1) _ hsel)
      rw [ENNReal.coe_toNNReal hfprev] at he
      exact he.trans (brownianSkeletonClock_time_le_succ W z j₀ selector n ω)


theorem brownianSkeleton_stopped_concatenate (W : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J)
    (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock W z j₀ selector n ω).2 ≠ ∞)
    {U : Set (Euc d)} (hU : IsOpen U)
    (hτ : continuousExitTime U z ω ≤ (brownianSkeletonClock W z j₀ selector n ω).2)
    (P : TimePartition n) :
    unitCurveExitProjection U (P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k ↦ (brownianSkeletonExcursion W z j₀ selector k ω).2))) =
      stoppedBrownianCurve U z ω := by
  let A := brownianSkeletonPhysicalKnots W z j₀ selector n ω hfinite
  have hτNN : continuousExitTime U z ω ≤ (A.duration : ℝ≥0∞) := by
    simpa only [A, brownianSkeletonPhysicalKnots_duration, ENNReal.coe_toNNReal hfinite] using hτ
  by_cases hT : A.duration = 0
  · have ha (i : Fin (n + 2)) : A.times i = 0 :=
      le_antisymm ((A.time_le_duration i).trans_eq hT) bot_le
    have hpaste : P.concatenate (A.chain z ω) = physicalTimeSegment z ω 0 A.duration := by
      apply ContinuousMap.ext
      intro u
      rw [P.concatenate_apply (A.chain z ω) (P.interval u) (P.interval_spec u)]
      change physicalTimeSegment z ω _ _ _ = physicalTimeSegment z ω 0 A.duration u
      rw [ha, ha, hT, physicalTimeSegment_self]
      rfl
    rw [brownianSkeleton_prefixChain_eq W z j₀ selector n ω hfinite]
    change unitCurveExitProjection U (P.concatenate (A.chain z ω)) = _
    rw [hpaste]
    exact unitCurveExitProjection_physicalTimeSegment hU z ω A.duration hτNN
  · have hpos : 0 < (A.duration : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < A.duration)
    rw [brownianSkeleton_concatenate_eq_comp W z j₀ selector n ω hfinite hpos P]
    rw [unitCurveExitProjection_comp_monotone hU _ _ (P.weakClock_monotone _)
      (P.weakClock_zero _) (P.weakClock_one _)]
    exact unitCurveExitProjection_physicalTimeSegment hU z ω A.duration hτNN

/-- Reconstruct and continuously stop the actual unflagged finite prefix. -/
noncomputable def reconstructedBrownianStoppedCurve {n : ℕ} (U : Set (Euc d))
    (P : TimePartition n) (γ : ℕ → Bool × C(unitInterval, Euc d)) : CurveSpace d :=
  unitCurveExitProjection U (P.concatenate
    (ExcursionTrajectory.prefixChain n d (fun k ↦ (γ k).2)))

lemma measurable_reconstructedBrownianStoppedCurve {n : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) (P : TimePartition n) :
    Measurable (reconstructedBrownianStoppedCurve U P) := by
  have hm : Measurable (fun γ : ℕ → Bool × C(unitInterval, Euc d) ↦ fun k ↦ (γ k).2) := by
    apply Measurable.of_eval
    intro k
    exact measurable_snd.comp (measurable_pi_apply k)
  exact (measurable_unitCurveExitProjection hU).comp
    (P.measurable_concatenate.comp ((ExcursionTrajectory.measurable_prefixChain n d).comp hm))

theorem levyProkhorov_stoppedBrownian_reconstruction_le (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n))
    {U : Set (Euc d)} (hU : IsOpen U)
    (hnone : ∀ n x, selector n x = none → x ∉ U)
    (n : ℕ) (P : TimePartition n) (r : ℝ≥0) (hr : 0 < r)
    (hbad : μ {ω | (brownianSkeletonClock W z j₀ selector n ω).1 = false} ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist (stoppedBrownianLaw U z μ)
      ((μ.map (fun ω k ↦ brownianSkeletonExcursion W z j₀ selector k ω)).map
        (reconstructedBrownianStoppedCurve U P)) ≤ r := by
  have hΓ : Measurable (fun ω k ↦ brownianSkeletonExcursion W z j₀ selector k ω) := by
    apply Measurable.of_eval
    intro k
    exact measurable_brownianSkeletonExcursion W hW z j₀ hselector k
  have hg := measurable_reconstructedBrownianStoppedCurve hU P
  rw [Measure.map_map hg hΓ]
  apply levyProkhorov_curveLaws_le_of_ae_reconstruction μ (stoppedBrownianCurve U z) _
    (measurable_stoppedBrownianCurve hU z).aemeasurable (hg.comp hΓ).aemeasurable _ r hr hbad
  filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ W hW hWb z j₀ hselector n]
    with ω hfinite
  intro hgood
  have hstop : (brownianSkeletonClock W z j₀ selector n ω).1 = true := by
    cases h : (brownianSkeletonClock W z j₀ selector n ω).1 with
    | false => exact False.elim (hgood h)
    | true => rfl
  exact (brownianSkeleton_stopped_concatenate W z j₀ selector n ω hfinite hU
    (brownianSkeletonClock_exit_le_of_stopped W z j₀ selector hnone n ω hfinite hstop) P).symm


end BouRabeeGwynne
