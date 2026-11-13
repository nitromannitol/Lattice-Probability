/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.AffineRandomComparison at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.AffineNormalization
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.RandomShiftCM
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.DataProcessing
import Mathlib.MeasureTheory.Measure.WithDensity
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContMarkov
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2D
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.MarkovComparison

/-!
# Comparing a raw translated GFF with its unit-circle recentering

The random circle average is cut off inside a larger Markov disk. The cutoff
is one on the observation disk, so the local shifted law is exactly the raw
translate. The Gaussian square moment gives an `L^p` density for some `p>1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open LQGMetric LQGMetric.GM LQGMetric.MarkovZB LQGMetric.CircleAvg
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.MoTPort.GFFBdry
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

/-- On the smaller observation disk, the smooth cutoff of a constant has the
same distributional restriction as the constant itself. -/
theorem resOn_cutoff_const {V W : Opens ℂ} (hWV : W ≤ V)
    (χ : zsSub (V : Set ℂ)) (hχ : ∀ z ∈ (W : Set ℂ), χ.1 z = 1)
    (k : DistC) (c : ℝ) :
    resOn W V (restrictTo V k + ofFunOn V ((0 : zsSub (V : Set ℂ)) + c • (-χ)).1) =
      restrictTo W (addConst k (-c)) := by
  ext φ
  rw [resOn_add, resOn_restrictTo hWV]
  rw [LQGMetric.DG.L22T.restrictTo_addConst]
  simp only [add_apply]
  rw [resOn_apply, ofFunOn_zsSub_apply]
  have he : ∫ x, ((0 : zsSub (V : Set ℂ)) + c • (-χ)).1 x *
      (GM.testIncl W V φ) x = (∫ x, φ x) * -c := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ (W : Set ℂ)
    · simp only [GM.coe_testIncl hWV]
      simp [hχ x hx, mul_comm]
    · have hφ : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun ht => hx (φ.tsupport_subset ht)
      simp [GM.coe_testIncl hWV, hφ]
  rw [he]

/-- After translation, the local raw GFF law dominates the recentered law
with a density having a finite moment above one. The hypotheses express the
separation of the Markov disk from the two normalization circles. -/
theorem rawTranslate_recentered_local_reverse
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (w : ℂ) {V W : Opens ℂ}
    (hWV : W ≤ V) (hK : IsCompact (closure (W : Set ℂ)))
    (hKV : closure (W : Set ℂ) ⊆ (V : Set ℂ))
    (hadm : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere (-w) 1)) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ D : DistOn W → ℝ≥0∞,
      Measurable D ∧
      P.map (fun ω => restrictTo W (recenteredTranslate h w ω)) =
        (P.map (fun ω => restrictTo W (affineComp 1 w (h ω)))).withDensity D ∧
      ∫⁻ y, D y ^ p ∂(P.map fun ω => restrictTo W (affineComp 1 w (h ω))) < ⊤ := by
  let : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  obtain ⟨χ, hχ, hχ1⟩ := exists_cutoff_of_isCompact hK V.isOpen hKV
  let χz : zsSub (V : Set ℂ) := ⟨χ, hχ⟩
  let t := recenteredTranslate h w
  have ht : IsNormalizedWPGFF t P := (recenteredTranslate_normalized hh w).1
  obtain ⟨M⟩ := exists_localMarkov ht V hV₁
  obtain ⟨p, hp, hp2, D, hDm, hLaw, hMom⟩ :=
    M.randomShift_local_reverse ht hWV hadm hne 1 (-w) one_pos hV₁ hVR
      0 (-χz)
  have hshift : (fun ω => resOn W V
      (restrictTo V (t ω) + ofFunOn V
        ((0 : zsSub (V : Set ℂ)) + cInc t 1 (-w) 1 0 ω • (-χz)).1)) =ᵐ[P]
      (fun ω => restrictTo W (affineComp 1 w (h ω))) := by
    filter_upwards [recenteredTranslate_cInc hh w] with ω hω
    rw [resOn_cutoff_const hWV χz (fun z hz => hχ1 z (subset_closure hz))]
    rw [hω]
    simpa only [neg_neg] using
      (congrArg (restrictTo W) (rawTranslate_eq_recentered_addConst h w ω)).symm
  refine ⟨p, hp, hp2, D, hDm, ?_, ?_⟩
  · rw [← Measure.map_congr hshift]
    exact hLaw
  · rw [← Measure.map_congr hshift]
    exact hMom

end MatedCRTHarmonic.GMSCM
