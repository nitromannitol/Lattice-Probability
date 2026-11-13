/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.AffineTransport at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.BundleComparison
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.DataProcessing
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112N3

/-!
# Affine transport of the cone-coordinate local comparison

The measurable affine restriction map transports the Cameron–Martin density
from a punctured cone-coordinate region to a translated observation region.
The resulting target is the *raw translated* normalized GFF and IG pair;
the subsequent random circle-average normalization is a separate step.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace LQGMetric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

/-- Affine pullback of the two restricted fields, from `w+W` to `W`. -/
def affineLocalPair (W : Opens ℂ) (w : ℂ) :
    GMS4c.LocalFieldPair (affOpens 1 w W) → GMS4c.LocalFieldPair W :=
  fun x => (distAffine 1 w one_ne_zero x.1,
    distAffine 1 w one_ne_zero x.2)

theorem measurable_affineLocalPair (W : Opens ℂ) (w : ℂ) :
    Measurable (affineLocalPair W w) := by
  have hf : Measurable (distAffine 1 w one_ne_zero :
      DistOn (affOpens 1 w W) → DistOn W) := by
    refine measurable_distOn_iff.2 fun φ => ?_
    exact ((measurable_distOn_apply (zbPull 1 w one_ne_zero φ))).const_mul _
  exact (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)

theorem affineLocalPair_localFieldPair (W : Opens ℂ) (w : ℂ)
    (h hIG : DistC) :
    affineLocalPair W w (restrictTo (affOpens 1 w W) h,
      restrictTo (affOpens 1 w W) hIG) =
      (restrictTo W (affineComp 1 w h), restrictTo W (affineComp 1 w hIG)) := by
  apply Prod.ext
  · exact (LQGMetric.CONF.hlz_restrict_affine one_pos w W h).symm
  · exact (LQGMetric.CONF.hlz_restrict_affine one_pos w W hIG).symm

/-- The c2 cone-coordinate comparison, observed after affine translation.
This is an exact `LocalFieldLawComparison` on `W`; `W` may contain the origin
as long as its image `w+W` stays in the punctured unit disk. -/
theorem IsMatingOfTreesCoupling.exists_affineLocalFieldLawComparison
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (W : Opens ℂ) (w : ℂ)
    (hK : IsCompact (closure ((affOpens 1 w W : Opens ℂ) : Set ℂ)))
    (hV : closure ((affOpens 1 w W : Opens ℂ) : Set ℂ) ⊆
      Metric.ball (0 : ℂ) 1 \ {0}) :
    ∃ (hγm Xt : Ω → DistC),
      Measurable hγm ∧
      (fun ω => coneField (X ω)
        (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) =ᵐ[P] hγm ∧
      IsNormalizedWPGFF Xt P ∧
      Nonempty (GMS4c.LocalFieldLawComparison W P P
        (fun ω => affineComp 1 w (hγm ω))
        (fun ω => affineComp 1 w (hIG₀ ω))
        (fun ω => affineComp 1 w (Xt ω))
        (fun ω => affineComp 1 w (hIG₀ ω)) 2 2) := by
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨hγm, Xt, hm, hae, hXt, ⟨C⟩⟩ :=
    MatedCRTHarmonic.GMSCM.IsMatingOfTreesCoupling.exists_localFieldLawComparison
      hC hγ (affOpens 1 w W) hK hV
  let F := affineLocalPair W w
  have hF : Measurable F := measurable_affineLocalPair W w
  let ν := P.map (GMS4c.localFieldPair (affOpens 1 w W) hγm hIG₀)
  let μ := P.map (GMS4c.localFieldPair (affOpens 1 w W) Xt hIG₀)
  have hνprob : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff C.gamma_measurable.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure ν := hνprob
  have hμprob : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff C.target_measurable.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure μ := hμprob
  have hac : μ ≪ ν := by
    rw [show μ = ν.withDensity C.density from C.law_eq]
    exact withDensity_absolutelyContinuous _ _
  have hL2 : MemLp (fun x => (μ.rnDeriv ν x).toReal) 2 ν :=
    rnDeriv_memLp_two_of_withDensity C.density_measurable C.law_eq C.moment_finite
  let D : GMS4c.LocalFieldPair W → ℝ≥0∞ := (μ.map F).rnDeriv (ν.map F)
  have hD : Measurable D := Measure.measurable_rnDeriv _ _
  have hLaw : μ.map F = (ν.map F).withDensity D :=
    (Measure.withDensity_rnDeriv_eq _ _ (hac.map hF)).symm
  have hMom : ∫⁻ x, D x ^ (2 : ℝ) ∂(ν.map F) < ⊤ :=
    rnDeriv_map_sq_finite hac hF hL2
  have hγF : Measurable (fun ω => affineComp 1 w (hγm ω)) :=
    (measurable_affineComp 1 w).comp hm
  have hIGF : Measurable (fun ω => affineComp 1 w (hIG₀ ω)) :=
    (measurable_affineComp 1 w).comp hC.igField.1.1.measurable
  have hXtF : Measurable (fun ω => affineComp 1 w (Xt ω)) :=
    (measurable_affineComp 1 w).comp hXt.1.measurable
  have hγlaw : P.map (GMS4c.localFieldPair W
      (fun ω => affineComp 1 w (hγm ω))
      (fun ω => affineComp 1 w (hIG₀ ω))) = ν.map F := by
    rw [Measure.map_map hF C.gamma_measurable]
    congr 1
    funext ω
    exact (affineLocalPair_localFieldPair W w (hγm ω) (hIG₀ ω)).symm
  have hXlaw : P.map (GMS4c.localFieldPair W
      (fun ω => affineComp 1 w (Xt ω))
      (fun ω => affineComp 1 w (hIG₀ ω))) = μ.map F := by
    rw [Measure.map_map hF C.target_measurable]
    congr 1
    funext ω
    exact (affineLocalPair_localFieldPair W w (Xt ω) (hIG₀ ω)).symm
  refine ⟨hγm, Xt, hm, hae, hXt,
    ⟨⟨GMS4c.measurable_localFieldPair W hγF hIGF,
      GMS4c.measurable_localFieldPair W hXtF hIGF,
      D, hD, ?_, ?_, Real.HolderConjugate.two_two⟩⟩⟩
  · rw [hγlaw, hXlaw]
    exact hLaw
  · rw [hγlaw]
    exact hMom

end MatedCRTHarmonic.GMSCM
