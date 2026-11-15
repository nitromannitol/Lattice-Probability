import LatticeProb.Prob.NormalizedExitTransform
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii

/-! # Area-time scaling of restricted planar paths -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace LatticeProb

/-- Express a two-sided complex path in Euclidean coordinates at nonnegative times. -/
noncomputable def planarForwardPath (c : C(ℝ, ℂ)) :
    C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) :=
  (⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩ :
    C(ℂ, EuclideanSpace ℝ (Fin 2))).comp
      (c.comp ⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩)

/-- Restriction and Euclidean coordinates are measurable on path space. -/
theorem measurable_planarForwardPath : Measurable planarForwardPath := by
  exact (ContinuousMap.continuous_postcomp
    (⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩ :
      C(ℂ, EuclideanSpace ℝ (Fin 2)))).measurable.comp
        (ContinuousMap.continuous_precomp
          (⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩ : C(ℝ≥0, ℝ))).measurable

/-- Area-time normalization commutes with restriction to nonnegative times. -/
theorem planarForwardPath_curveRescale (c : C(ℝ, ℂ)) (s : ℝ≥0) (hs : 0 < s) :
    planarForwardPath (MatedCRTHarmonic.GMS4b.curveRescale (s : ℝ) ((s : ℝ) ^ 2) c) =
      ((⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2))).comp
          (planarForwardPath c)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩ := by
  ext t : 1
  simp only [planarForwardPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    MatedCRTHarmonic.GMS4b.curveRescale_apply, ballNormalize_apply, sub_zero]
  change Complex.orthonormalBasisOneI.repr
    (((((s : ℝ)⁻¹ : ℝ) : ℂ)) * c ((s : ℝ) ^ 2 * (t : ℝ))) = _
  rw [← Complex.real_smul, map_smul]
  simp [areaTimeScale]

/-- Fixed area-time scale invariance passes to the nonnegative-time path law. -/
theorem map_planarForwardPath_normalize_of_curveRescale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : Ω → C(ℝ, ℂ))
    (hc : Measurable c) (s : ℝ≥0) (hs : 0 < s)
    (hlaw : P.map (fun ω => MatedCRTHarmonic.GMS4b.curveRescale
      (s : ℝ) ((s : ℝ) ^ 2) (c ω)) = P.map c) :
    (P.map (fun ω => planarForwardPath (c ω))).map
      (fun w => ((⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2))).comp w).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) =
      P.map (fun ω => planarForwardPath (c ω)) := by
  have hn : Measurable (fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) =>
      ((⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2))).comp w).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) :=
    (ContinuousMap.continuous_precomp
      (⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩ : C(ℝ≥0, ℝ≥0))).measurable.comp
        (ContinuousMap.continuous_postcomp
          (⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
            C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2)))).measurable
  have hr : Measurable (fun ω => MatedCRTHarmonic.GMS4b.curveRescale
      (s : ℝ) ((s : ℝ) ^ 2) (c ω)) :=
    (MatedCRTHarmonic.GMS4b.measurable_curveRescale _).comp (measurable_const.prodMk hc)
  change (P.map (planarForwardPath ∘ c)).map _ = _
  rw [Measure.map_map hn (measurable_planarForwardPath.comp hc)]
  calc
    P.map (fun ω => ((⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2))).comp
          (planarForwardPath (c ω))).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) =
        P.map (fun ω => planarForwardPath (MatedCRTHarmonic.GMS4b.curveRescale
          (s : ℝ) ((s : ℝ) ^ 2) (c ω))) := by
            congr 1
            funext ω
            exact (planarForwardPath_curveRescale (c ω) s hs).symm
    _ = (P.map (fun ω => MatedCRTHarmonic.GMS4b.curveRescale
          (s : ℝ) ((s : ℝ) ^ 2) (c ω))).map planarForwardPath :=
        (Measure.map_map measurable_planarForwardPath hr).symm
    _ = (P.map c).map planarForwardPath := by rw [hlaw]
    _ = P.map (fun ω => planarForwardPath (c ω)) := Measure.map_map measurable_planarForwardPath hc

/-- The area-time path in a mating-of-trees coupling has the same forward
path law after any positive area-time normalization. -/
theorem map_planarForwardPath_normalize_of_matingOfTrees
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) (s : ℝ≥0) (hs : 0 < s) :
    (P.map (fun ω => planarForwardPath (ηL ω))).map
      (fun w => ((⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2))).comp w).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) =
      P.map (fun ω => planarForwardPath (ηL ω)) := by
  apply map_planarForwardPath_normalize_of_curveRescale P ηL hC.measurable_curves.1 s hs
  exact MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii
    hC (MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii hC)
    (by exact_mod_cast hs)

end LatticeProb
