/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.ExcursionMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalConfiguration
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.LastLevel

/-!
# Measurability of the first-hit excursion coordinates

The entry and exit times of a rational-point excursion into a bounded open set
are hitting/last-exit functionals of a continuous curve. The reusable last-zero
measurability theorem is `ConeScaling.measurable_sSup_zeroSet`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open LQGMetric

namespace MatedCRTHarmonic.GMS4c

variable (V : TopologicalSpace.Opens ℂ) (z : ℂ)

/-- The closed-set zero detector for times before the first hit of `z`. -/
private def entryDetector (c : C(ℝ, ℂ)) (t : ℝ) : ℝ :=
  infDist (c t) ((V : Set ℂ)ᶜ) + max (t - GMS4b.hitTime c z) 0

private theorem entryDetector_continuous (c : C(ℝ, ℂ)) : Continuous (entryDetector V z c) := by
  unfold entryDetector
  exact ((continuous_infDist_pt _).comp c.continuous).add
    ((continuous_id.sub continuous_const).max continuous_const)

private theorem entryDetector_measurable (t : ℝ) :
    Measurable fun c : C(ℝ, ℂ) => entryDetector V z c t := by
  unfold entryDetector
  have ht : Measurable fun c : C(ℝ, ℂ) => GMS4b.hitTime c z :=
    GMS4b.measurable_hitTime.comp (measurable_id.prodMk measurable_const)
  exact ((continuous_infDist_pt _).measurable.comp (ContinuousMap.measurable_eval t)).add
    ((measurable_const.sub ht).max measurable_const)

/-- The detector vanishes exactly on the closed set defining `entryBefore`, provided the
complement of `V` is nonempty. -/
private theorem entryDetector_zero_iff (hVc : ((V : Set ℂ)ᶜ).Nonempty)
    (c : C(ℝ, ℂ)) (t : ℝ) :
    entryDetector V z c t = 0 ↔ t ≤ GMS4b.hitTime c z ∧ c t ∉ V := by
  have hclosed : IsClosed ((V : Set ℂ)ᶜ) := V.isOpen.isClosed_compl
  have hdist : 0 ≤ infDist (c t) ((V : Set ℂ)ᶜ) := infDist_nonneg
  have hmax : 0 ≤ max (t - GMS4b.hitTime c z) 0 := le_max_right _ _
  rw [entryDetector]
  constructor
  · intro h
    have hdist0 : infDist (c t) ((V : Set ℂ)ᶜ) = 0 := by linarith
    have hmax0 : max (t - GMS4b.hitTime c z) 0 = 0 := by linarith
    exact ⟨by have := le_max_left (t - GMS4b.hitTime c z) 0; linarith,
      (hclosed.mem_iff_infDist_zero hVc).2 hdist0⟩
  · rintro ⟨ht, hnot⟩
    rw [(hclosed.mem_iff_infDist_zero hVc).1 hnot, max_eq_right (sub_nonpos.mpr ht)]
    simp

/-- The frozen last-entry time is Borel on continuous curves for an open set with
nonempty complement. -/
theorem measurable_entryBefore (hVc : ((V : Set ℂ)ᶜ).Nonempty) :
    Measurable fun c : C(ℝ, ℂ) => MatedCRT.entryBefore c V z := by
  have hzero := ConeScaling.measurable_sSup_zeroSet
    (entryDetector_continuous V z) (entryDetector_measurable V z)
  have heq : (fun c : C(ℝ, ℂ) => MatedCRT.entryBefore c V z) =
      fun c => sSup {t : ℝ | entryDetector V z c t = 0} := by
    funext c
    change sSup {t : ℝ | t ≤ GMS4b.hitTime c z ∧ c t ∉ V} =
      sSup {t : ℝ | entryDetector V z c t = 0}
    congr 1
    ext t
    exact (entryDetector_zero_iff V z hVc c t).symm
  rw [heq]
  exact hzero

/-- The reflected zero detector for the first exit after hitting `z`. -/
private def exitDetector (c : C(ℝ, ℂ)) (s : ℝ) : ℝ :=
  infDist (c (-s)) ((V : Set ℂ)ᶜ) + max (s + GMS4b.hitTime c z) 0

private theorem exitDetector_continuous (c : C(ℝ, ℂ)) : Continuous (exitDetector V z c) := by
  unfold exitDetector
  exact ((continuous_infDist_pt _).comp (c.continuous.comp continuous_neg)).add
    ((continuous_id.add continuous_const).max continuous_const)

private theorem exitDetector_measurable (s : ℝ) :
    Measurable fun c : C(ℝ, ℂ) => exitDetector V z c s := by
  unfold exitDetector
  have ht : Measurable fun c : C(ℝ, ℂ) => GMS4b.hitTime c z :=
    GMS4b.measurable_hitTime.comp (measurable_id.prodMk measurable_const)
  exact ((continuous_infDist_pt _).measurable.comp (ContinuousMap.measurable_eval (-s))).add
    ((measurable_const.add ht).max measurable_const)

private theorem exitDetector_zero_iff (hVc : ((V : Set ℂ)ᶜ).Nonempty)
    (c : C(ℝ, ℂ)) (s : ℝ) :
    exitDetector V z c s = 0 ↔ GMS4b.hitTime c z ≤ -s ∧ c (-s) ∉ V := by
  have hclosed : IsClosed ((V : Set ℂ)ᶜ) := V.isOpen.isClosed_compl
  have hdist : 0 ≤ infDist (c (-s)) ((V : Set ℂ)ᶜ) := infDist_nonneg
  have hmax : 0 ≤ max (s + GMS4b.hitTime c z) 0 := le_max_right _ _
  rw [exitDetector]
  constructor
  · intro h
    have hdist0 : infDist (c (-s)) ((V : Set ℂ)ᶜ) = 0 := by linarith
    have hmax0 : max (s + GMS4b.hitTime c z) 0 = 0 := by linarith
    exact ⟨by have := le_max_left (s + GMS4b.hitTime c z) 0; linarith,
      (hclosed.mem_iff_infDist_zero hVc).2 hdist0⟩
  · rintro ⟨ht, hnot⟩
    rw [(hclosed.mem_iff_infDist_zero hVc).1 hnot,
      max_eq_right (show s + GMS4b.hitTime c z ≤ 0 by linarith)]
    simp

/-- The frozen first-exit time is Borel on continuous curves. -/
theorem measurable_exitAfter (hVc : ((V : Set ℂ)ᶜ).Nonempty) :
    Measurable fun c : C(ℝ, ℂ) => MatedCRT.exitAfter c V z := by
  have hzero := ConeScaling.measurable_sSup_zeroSet
    (exitDetector_continuous V z) (exitDetector_measurable V z)
  have heq : (fun c : C(ℝ, ℂ) => MatedCRT.exitAfter c V z) =
      fun c => -(sSup {s : ℝ | exitDetector V z c s = 0}) := by
    funext c
    change sInf {t : ℝ | GMS4b.hitTime c z ≤ t ∧ c t ∉ V} = _
    have hset : {s : ℝ | exitDetector V z c s = 0} =
        -{t : ℝ | GMS4b.hitTime c z ≤ t ∧ c t ∉ V} := by
      ext s
      rw [Set.mem_neg]
      simpa only [Set.mem_ofPred_eq, neg_neg] using exitDetector_zero_iff V z hVc c s
    rw [hset, Real.sSup_neg, neg_neg]
  rw [heq]
  exact hzero.neg

/-- The frozen rational-point excursion segment is measurable in the continuous curve,
with the point and open set fixed. -/
theorem measurable_excursionSegment (hVc : ((V : Set ℂ)ᶜ).Nonempty) :
    Measurable fun c : C(ℝ, ℂ) => MatedCRT.excursionSegment c V z := by
  refine measurable_pi_iff.mpr fun u => ?_
  have hentry := measurable_entryBefore V z hVc
  have hexit := measurable_exitAfter V z hVc
  have htime : Measurable fun c : C(ℝ, ℂ) =>
      MatedCRT.entryBefore c V z +
        max 0 (min u (MatedCRT.exitAfter c V z - MatedCRT.entryBefore c V z)) :=
    hentry.add (measurable_const.max (measurable_const.min (hexit.sub hentry)))
  exact continuous_eval.measurable.comp (measurable_id.prodMk htime)

end MatedCRTHarmonic.GMS4c
