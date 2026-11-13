/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExitStoppingTime at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Process.Stopping

/-!
# The actual exit time in the canonical Brownian filtration

Compact-open survival events prove the stopping-time property directly.
-/
open MeasureTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

noncomputable def brownianNaturalFiltration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (BrownianPath d)) :=
  Filtration.natural (fun t (ω : BrownianPath d) ↦ ω t)
    (fun t ↦ (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω t)).stronglyMeasurable)

def restrictBrownianPath {d : ℕ} (t : ℝ≥0) (ω : BrownianPath d) :
    C(Icc (0 : ℝ≥0) t, Euc d) :=
  ⟨fun s ↦ ω s, ω.continuous.comp continuous_subtype_val⟩

lemma measurable_restrictBrownianPath {d : ℕ} (t : ℝ≥0) :
    Measurable[brownianNaturalFiltration d t] (restrictBrownianPath (d := d) t) := by
  letI : MeasurableSpace (BrownianPath d) := brownianNaturalFiltration d t
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact (comap_measurable (fun ω : BrownianPath d ↦ ω s.val)).mono
    (le_iSup₂_of_le s.val s.property.2 le_rfl) le_rfl

lemma continuousExitTime_le_iff_not_mapsTo {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0) :
    continuousExitTime U z ω ≤ (t : ℝ≥0∞) ↔
      ¬ MapsTo ω (Icc (0 : ℝ≥0) t) ((fun x ↦ z + x) ⁻¹' U) := by
  constructor
  · intro hle hsurvive
    have hfinite : continuousExitTime U z ω ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    have htime : (continuousExitTime U z ω).toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfinite]
      exact hle
    exact continuousExitTime_not_mem hU hfinite (hsurvive ⟨bot_le, htime⟩)
  · intro hsurvive
    change ¬ ∀ s ∈ Icc (0 : ℝ≥0) t, z + ω s ∈ U at hsurvive
    push_neg at hsurvive
    obtain ⟨s, hs, hout⟩ := hsurvive
    exact (continuousExitTime_le_of_not_mem hout).trans (ENNReal.coe_le_coe.mpr hs.2)

/-- The actual first exit from an open set is a stopping time for the canonical
natural filtration. Compact-open survival events prove this directly. -/
theorem isStoppingTime_continuousExitTime {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) :
    IsStoppingTime (brownianNaturalFiltration d) (continuousExitTime U z) := by
  intro t
  let W : Set (Euc d) := (fun x ↦ z + x) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  have hmeas : MeasurableSet[brownianNaturalFiltration d t]
      ((restrictBrownianPath t) ⁻¹'
        {f : C(Icc (0 : ℝ≥0) t, Euc d) | ¬ MapsTo f univ W}) :=
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hW).measurableSet.compl.preimage
      (measurable_restrictBrownianPath t)
  have hset : {ω | continuousExitTime U z ω ≤ (t : ℝ≥0∞)} =
      (restrictBrownianPath t) ⁻¹'
        {f : C(Icc (0 : ℝ≥0) t, Euc d) | ¬ MapsTo f univ W} := by
    ext ω
    rw [mem_setOf_eq, continuousExitTime_le_iff_not_mapsTo hU]
    simp only [mem_preimage, mem_setOf_eq, MapsTo, mem_univ, forall_true_left,
      restrictBrownianPath, ContinuousMap.coe_mk, Subtype.forall]
    rfl
  change MeasurableSet[brownianNaturalFiltration d t]
    {ω | continuousExitTime U z ω ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact hmeas

end BouRabeeGwynne
