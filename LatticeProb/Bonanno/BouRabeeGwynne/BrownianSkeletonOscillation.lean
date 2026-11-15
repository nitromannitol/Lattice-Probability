/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonOscillation at commit fdb5cad; local import paths and a deprecated lemma name are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton

/-! Transfer the original Brownian boundary-interval oscillation estimate to
the measurable finite excursion representative, with only the active-tail loss. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

lemma unitCurveExitTime_mono {d : ℕ} {U V : Set (Euc d)} (hUV : U ⊆ V)
    (f : C(unitInterval, Euc d)) : unitCurveExitTime U f ≤ unitCurveExitTime V f := by
  change ((min (continuousExitTime U 0 (extendUnitCurve f)) 1).toNNReal : ℝ) ≤
    ((min (continuousExitTime V 0 (extendUnitCurve f)) 1).toNNReal : ℝ)
  exact ENNReal.toNNReal_mono (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
    (min_le_min (continuousExitTime_mono hUV 0 (extendUnitCurve f)) le_rfl)

theorem physical_clock_not_unitCurveExitOscillationBad {d : ℕ}
    {U V : Set (Euc d)} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (z : Euc d) (ω : BrownianPath d) (T : ℝ≥0)
    (hτ : continuousExitTime V z ω ≤ (T : ℝ≥0∞))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (hzero : φ 0 = 0) (hone : φ 1 = 1) {η : ℝ}
    (hosc : ∀ s ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
      ∀ t ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
        dist (z + ω s) (z + ω t) ≤ η) :
    (physicalTimeSegment z ω 0 T).comp φ ∉ unitCurveExitOscillationBad U V η := by
  let f := (physicalTimeSegment z ω 0 T).comp φ
  let a := unitCurveExitTime U f
  let b := unitCurveExitTime V f
  have hab : a ≤ b := unitCurveExitTime_mono hUV f
  have ha : (φ a : ℝ) * T = (continuousExitTime U z ω).toNNReal := by
    rw [show φ a = unitCurveExitTime U (physicalTimeSegment z ω 0 T) from
      unitCurveExitTime_comp_monotone hU _ φ hmono hzero hone]
    exact unitCurveExitTime_physicalTimeSegment_mul hU z ω T
      ((continuousExitTime_mono hUV z ω).trans hτ)
  have hb : (φ b : ℝ) * T = (continuousExitTime V z ω).toNNReal := by
    rw [show φ b = unitCurveExitTime V (physicalTimeSegment z ω 0 T) from
      unitCurveExitTime_comp_monotone hV _ φ hmono hzero hone]
    exact unitCurveExitTime_physicalTimeSegment_mul hV z ω T hτ
  let time : unitInterval → ℝ≥0 := fun u ↦
    ⟨(φ (unitIntervalAffine a b u) : ℝ) * T,
      mul_nonneg (φ (unitIntervalAffine a b u)).property.1 T.property⟩
  have htime (u : unitInterval) : time u ∈
      Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal := by
    have hu := unitIntervalAffine_mem_Icc a b hab u
    constructor
    · change ((continuousExitTime U z ω).toNNReal : ℝ) ≤ _
      rw [← ha]
      have hl : (φ a : ℝ) ≤ (φ (unitIntervalAffine a b u) : ℝ) := hmono hu.1
      exact mul_le_mul_of_nonneg_right hl T.property
    · change _ ≤ ((continuousExitTime V z ω).toNNReal : ℝ)
      rw [← hb]
      have hr : (φ (unitIntervalAffine a b u) : ℝ) ≤ (φ b : ℝ) := hmono hu.2
      exact mul_le_mul_of_nonneg_right hr T.property
  have hpoint (u : unitInterval) : unitCurveInterval f a b u = z + ω (time u) := by
    exact physicalTimeSegment_initial_apply z ω T (φ (unitIntervalAffine a b u))
  apply not_not.mpr
  intro s t
  change dist (unitCurveInterval f a b s) (unitCurveInterval f a b t) ≤ η
  rw [hpoint, hpoint]
  exact hosc _ (htime s) _ (htime t)

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem brownianSkeleton_not_unitCurveExitOscillationBad (W : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J)
    (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock W z j₀ selector n ω).2 ≠ ∞)
    {U V : Set (Euc d)} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hτ : continuousExitTime V z ω ≤ (brownianSkeletonClock W z j₀ selector n ω).2)
    (P : TimePartition n) {η : ℝ}
    (hosc : ∀ s ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
      ∀ t ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
        dist (z + ω s) (z + ω t) ≤ η) :
    P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k ↦ (brownianSkeletonExcursion W z j₀ selector k ω).2)) ∉
      unitCurveExitOscillationBad U V η := by
  let A := brownianSkeletonPhysicalKnots W z j₀ selector n ω hfinite
  have hτNN : continuousExitTime V z ω ≤ (A.duration : ℝ≥0∞) := by
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
    change P.concatenate (A.chain z ω) ∉ _
    rw [hpaste]
    exact physical_clock_not_unitCurveExitOscillationBad hU hV hUV z ω A.duration hτNN
      (ContinuousMap.id unitInterval) monotone_id rfl rfl hosc
  · have hpos : 0 < (A.duration : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < A.duration)
    rw [brownianSkeleton_concatenate_eq_comp W z j₀ selector n ω hfinite hpos P]
    exact physical_clock_not_unitCurveExitOscillationBad hU hV hUV z ω A.duration hτNN
      _ (P.weakClock_monotone _) (P.weakClock_zero _) (P.weakClock_one _) hosc

theorem brownianSkeleton_oscillationBad_measure_le (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n))
    {U V : Set (Euc d)} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hnone : ∀ k x, selector k x = none → x ∉ V)
    (n : ℕ) (P : TimePartition n) (η : ℝ) (ε r : ℝ≥0∞)
    (hbound : μ {ω | ∃ s ∈ Icc (continuousExitTime U z ω).toNNReal
        (continuousExitTime V z ω).toNNReal,
      ∃ t ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
        η < dist (z + ω s) (z + ω t)} ≤ ε)
    (hbad : μ {ω | (brownianSkeletonClock W z j₀ selector n ω).1 = false} ≤ r) :
    μ {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k ↦ (brownianSkeletonExcursion W z j₀ selector k ω).2)) ∈
      unitCurveExitOscillationBad U V η} ≤ ε + r := by
  let E : Set (BrownianPath d) := {ω | ∃ s ∈ Icc (continuousExitTime U z ω).toNNReal
      (continuousExitTime V z ω).toNNReal,
    ∃ t ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
      η < dist (z + ω s) (z + ω t)}
  let F : Set (BrownianPath d) := {ω | (brownianSkeletonClock W z j₀ selector n ω).1 = false}
  have hsub : {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k ↦ (brownianSkeletonExcursion W z j₀ selector k ω).2)) ∈
      unitCurveExitOscillationBad U V η} ≤ᵐ[μ] E ∪ F := by
    filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ W hW hWb z j₀ hselector n]
      with ω hfinite
    intro hosc
    by_cases hf : ω ∈ F
    · exact Or.inr hf
    · apply Or.inl
      by_contra he
      have hgood : ∀ s ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
          ∀ t ∈ Icc (continuousExitTime U z ω).toNNReal (continuousExitTime V z ω).toNNReal,
            dist (z + ω s) (z + ω t) ≤ η := by
        simpa only [E, mem_ofPred_eq, not_exists, not_and, not_lt] using he
      have hstop : (brownianSkeletonClock W z j₀ selector n ω).1 = true := by
        cases h : (brownianSkeletonClock W z j₀ selector n ω).1 with
        | false => exact False.elim (hf h)
        | true => rfl
      exact (brownianSkeleton_not_unitCurveExitOscillationBad W z j₀ selector n ω hfinite
        hU hV hUV (brownianSkeletonClock_exit_le_of_stopped W z j₀ selector hnone n ω hfinite hstop)
        P hgood) hosc
  exact (measure_mono_ae hsub).trans ((measure_union_le E F).trans (add_le_add hbound hbad))

end BouRabeeGwynne
