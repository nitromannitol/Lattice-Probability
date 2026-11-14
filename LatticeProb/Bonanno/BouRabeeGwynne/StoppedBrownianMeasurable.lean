/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StoppedBrownianMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Measurability of the actual continuously stopped curve

For an open domain, exit before a given time is a countable union of failures
to stay inside the domain on a compact time interval. Compact-open topology
therefore proves measurability directly, without a Brownian existence or
stopping-time hypothesis.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal unitInterval

namespace BouRabeeGwynne

variable {d : ℕ}

lemma measurable_continuousExitTime {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) :
    Measurable (continuousExitTime U z) := by
  obtain ⟨S, hSc, hSd, _, hStop⟩ := ENNReal.exists_countable_dense_no_zero_top
  letI : Countable S := hSc.to_subtype
  let W : Set (Euc d) := (fun x ↦ z + x) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  apply measurable_of_Iio
  intro a
  have heq : (continuousExitTime U z) ⁻¹' Iio a =
      ⋃ r : S, ⋃ (_ : r.1 < a),
        {ω : BrownianPath d | ¬ MapsTo ω (Icc 0 r.1.toNNReal) W} := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq]
    constructor
    · intro hω
      obtain ⟨⟨t, ht⟩, hta⟩ := iInf_lt_iff.mp hω
      obtain ⟨r, hrS, htr, hra⟩ := hSd.exists_between hta
      refine ⟨⟨r, hrS⟩, hra, ?_⟩
      intro hsurvive
      apply ht
      apply hsurvive
      refine ⟨bot_le, ?_⟩
      have hrne : r ≠ ∞ := fun heq ↦ hStop (heq ▸ hrS)
      rw [← ENNReal.coe_toNNReal hrne] at htr
      exact (ENNReal.coe_lt_coe.mp htr).le
    · rintro ⟨r, hra, hsurvive⟩
      change ¬ ∀ t ∈ Icc (0 : ℝ≥0) r.1.toNNReal, z + ω t ∈ U at hsurvive
      push_neg at hsurvive
      obtain ⟨t, ht, hout⟩ := hsurvive
      have hτ : continuousExitTime U z ω ≤ (t : ℝ≥0∞) :=
        iInf_le_of_le ⟨t, hout⟩ le_rfl
      exact hτ.trans_lt (((ENNReal.coe_le_coe.mpr ht.2).trans
        ENNReal.coe_toNNReal_le_self).trans_lt hra)
  rw [heq]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro _
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hW).measurableSet.compl

lemma measurable_stoppedBrownianRepresentative {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) : Measurable (stoppedBrownianRepresentative U z) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hτ : Measurable (fun ω : BrownianPath d ↦
      (continuousExitTime U z ω).toNNReal) :=
    ENNReal.measurable_toNNReal.comp (measurable_continuousExitTime hU z)
  have htime : Measurable (fun ω : BrownianPath d ↦
      (⟨(t : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
        mul_nonneg t.property.1 (continuousExitTime U z ω).toNNReal.property⟩ : ℝ≥0)) := by
    fun_prop
  have heval : Measurable (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2) :=
    (by fun_prop : Continuous (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2)).measurable
  exact measurable_const.add (heval.comp (measurable_id.prodMk htime))

/-- The totalized, normalized, actual stopped curve is measurable even for paths
that never leave the domain. Finiteness is a separate probabilistic theorem. -/
theorem measurable_stoppedBrownianCurve {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) : Measurable (stoppedBrownianCurve U z) :=
  CurveSpace.continuous_project.measurable.comp
    (measurable_stoppedBrownianRepresentative hU z)

lemma stoppedBrownianLaw_isProbabilityMeasure {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (stoppedBrownianLaw U z μ) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_stoppedBrownianCurve hU z).aemeasurable).mpr inferInstance

end BouRabeeGwynne
