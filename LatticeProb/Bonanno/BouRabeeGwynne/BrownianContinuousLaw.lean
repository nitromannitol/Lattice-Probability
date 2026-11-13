/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianContinuousLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianProjectiveLaw
import LatticeProb.Bonanno.BouRabeeGwynne.GaussianIncrementBounds
import LatticeProb.Bonanno.BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsov
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Construction of an actual continuous real Brownian law

The canonical Gaussian projective law satisfies the fourth-moment Kolmogorov
condition. The proved Kolmogorov--Chentsov theorem gives a measurable continuous
modification, whose actual pushforward measure is the real Wiener law.
No stochastic-law existence is assumed in these definitions or proofs.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

lemma isKolmogorovProcess_brownianProjectiveLaw :
    IsKolmogorovProcess (fun t (ω : ℝ≥0 → ℝ) ↦ ω t)
      brownianProjectiveLaw 4 2 3 where
  measurablePair s t := by
    rw [← BorelSpace.measurable_eq]
    exact (measurable_pi_apply s).prodMk (measurable_pi_apply t)
  kolmogorovCondition s t := by
    have hmoment :
        (∫⁻ ω : ℝ≥0 → ℝ, edist (ω s) (ω t) ^ (4 : ℝ) ∂brownianProjectiveLaw) =
          (3 : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
      calc
        _ = ∫⁻ ω : ℝ≥0 → ℝ, ENNReal.ofReal (|ω s - ω t| ^ 4)
            ∂brownianProjectiveLaw := by
          apply lintegral_congr
          intro ω
          rw [ENNReal.rpow_ofNat, edist_dist, Real.dist_eq,
            ENNReal.ofReal_pow (abs_nonneg _)]
        _ = 3 * (nndist s.1 t.1 : ℝ≥0∞) ^ 2 :=
          hasLaw_gaussian_lintegral_abs_fourth
            (isPreBrownianReal_brownianProjectiveLaw.hasLaw_sub s t)
        _ = _ := by
          rw [ENNReal.rpow_ofNat, edist_nndist]
          rfl
    exact hmoment.le
  p_pos := by norm_num
  q_pos := by norm_num

lemma exists_continuous_brownianProjective_modification :
    ∃ Y : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[brownianProjectiveLaw] (fun ω ↦ ω t)) ∧
      (∀ ω, Continuous (Y · ω)) := by
  obtain ⟨Y, hmeas, heq, hholder⟩ :=
    exists_modification_holder' isCoverWithBoundedCoveringNumber_Ico_nnreal
      isKolmogorovProcess_brownianProjectiveLaw.IsAEKolmogorovProcess
      (fun n ↦ by finiteness) (by norm_num) (by norm_num)
  refine ⟨Y, hmeas, heq, fun ω ↦ continuous_iff_continuousAt.mpr fun t ↦ ?_⟩
  obtain ⟨U, hUt, hU⟩ := hholder ω t
  obtain ⟨C, hC⟩ := hU (1 / 8) (by norm_num) (by norm_num)
  exact (hC.continuousOn (by norm_num)).continuousAt hUt

noncomputable def continuousBrownianProcess : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  exists_continuous_brownianProjective_modification.choose

lemma continuous_continuousBrownianProcess (ω : ℝ≥0 → ℝ) :
    Continuous (continuousBrownianProcess · ω) :=
  exists_continuous_brownianProjective_modification.choose_spec.2.2 ω

lemma measurable_continuousBrownianProcess (t : ℝ≥0) :
    Measurable (continuousBrownianProcess t) :=
  exists_continuous_brownianProjective_modification.choose_spec.1 t

lemma isBrownianReal_continuousBrownianProcess :
    IsBrownianReal continuousBrownianProcess brownianProjectiveLaw where
  toIsPreBrownianReal := isPreBrownianReal_brownianProjectiveLaw.congr fun t ↦
    (exists_continuous_brownianProjective_modification.choose_spec.2.1 t).symm
  cont := Filter.Eventually.of_forall continuous_continuousBrownianProcess

noncomputable def continuousBrownianPath (ω : ℝ≥0 → ℝ) : C(ℝ≥0, ℝ) :=
  ⟨fun t ↦ continuousBrownianProcess t ω, continuous_continuousBrownianProcess ω⟩

lemma measurable_continuousBrownianPath : Measurable continuousBrownianPath :=
  ContinuousMap.measurable_iff_eval.mpr measurable_continuousBrownianProcess

noncomputable def realWienerLaw : Measure C(ℝ≥0, ℝ) :=
  brownianProjectiveLaw.map continuousBrownianPath

instance realWienerLaw_isProbabilityMeasure : IsProbabilityMeasure realWienerLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_continuousBrownianPath.aemeasurable).mpr
    inferInstance

lemma isBrownianReal_realWienerLaw :
    IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) realWienerLaw where
  toIsPreBrownianReal := by
    constructor
    intro I
    have hm : Measurable (fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t)) := by
      apply Measurable.of_eval
      intro t
      exact (continuous_eval_const (t : ℝ≥0)).measurable
    refine ⟨hm.aemeasurable, ?_⟩
    rw [realWienerLaw, Measure.map_map hm measurable_continuousBrownianPath]
    exact (isBrownianReal_continuousBrownianProcess.hasLaw I).map_eq
  cont := Filter.Eventually.of_forall fun ω ↦ ω.continuous

end BouRabeeGwynne
