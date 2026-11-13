/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.GeneralFieldBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.DensityComposition
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.ZeroConeIG

/-!
# Affine local field bridge on a general observation disk

The cone comparison and the normalization comparison use separate regions:
the affine image of the observation disk in cone coordinates, and a larger
Markov disk around the observation disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric LQGMetric
open LQGMetric.CircleAvg
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

/-- General affine version of the composed field marginal comparison. -/
theorem IsMatingOfTreesCoupling.exists_affineFieldComparison
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (W V : Opens ℂ) (t : ℂ)
    (hK : IsCompact (closure ((affOpens 1 t W : Opens ℂ) : Set ℂ)))
    (hCone : closure ((affOpens 1 t W : Opens ℂ) : Set ℂ) ⊆
      ball (0 : ℂ) 1 \ {0})
    (hWV : W ≤ V) (hKW : IsCompact (closure (W : Set ℂ)))
    (hKV : closure (W : Set ℂ) ⊆ (V : Set ℂ))
    (hadm : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere (-t) 1)) :
    ∃ (hγm Xt : Ω → DistC),
      Measurable hγm ∧
      (fun ω => coneField (X ω)
        (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω))) =ᵐ[P] hγm ∧
      IsNormalizedWPGFF Xt P ∧
      ∃ p : ℝ, 1 < p ∧ ∃ D : DistOn W → ℝ≥0∞,
        Measurable D ∧
        P.map (fun ω => restrictTo W (Xt ω)) =
          (P.map (fun ω => restrictTo W (affineComp 1 t (hγm ω)))).withDensity D ∧
        ∫⁻ y, D y ^ p ∂(P.map fun ω =>
          restrictTo W (affineComp 1 t (hγm ω))) < ⊤ := by
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨hγm, Xt, hγmMeas, hγae, hXt, ⟨C⟩⟩ :=
    IsMatingOfTreesCoupling.exists_affineLocalFieldLawComparison
      hC hγ W t hK hCone
  let νpair := P.map (GMS4c.localFieldPair W
    (fun ω => affineComp 1 t (hγm ω))
    (fun ω => affineComp 1 t (hIG₀ ω)))
  let μpair := P.map (GMS4c.localFieldPair W
    (fun ω => affineComp 1 t (Xt ω))
    (fun ω => affineComp 1 t (hIG₀ ω)))
  let ν := P.map (fun ω => restrictTo W (affineComp 1 t (hγm ω)))
  let μ := P.map (fun ω => restrictTo W (affineComp 1 t (Xt ω)))
  have hνpairProb : IsProbabilityMeasure νpair :=
    (Measure.isProbabilityMeasure_map_iff C.gamma_measurable.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure νpair := hνpairProb
  have hμpairProb : IsProbabilityMeasure μpair :=
    (Measure.isProbabilityMeasure_map_iff C.target_measurable.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure μpair := hμpairProb
  have hνproj : νpair.map Prod.fst = ν := by
    rw [Measure.map_map measurable_fst C.gamma_measurable]
    rfl
  have hμproj : μpair.map Prod.fst = μ := by
    rw [Measure.map_map measurable_fst C.target_measurable]
    rfl
  have hacPair : μpair ≪ νpair := by
    rw [show μpair = νpair.withDensity C.density from C.law_eq]
    exact withDensity_absolutelyContinuous _ _
  have hL2 : MemLp (fun z => (μpair.rnDeriv νpair z).toReal) 2 νpair :=
    rnDeriv_memLp_two_of_withDensity C.density_measurable C.law_eq C.moment_finite
  have hac : μ ≪ ν := by
    rw [← hμproj, ← hνproj]
    exact hacPair.map measurable_fst
  let D₁ : DistOn W → ℝ≥0∞ := μ.rnDeriv ν
  have hD₁ : Measurable D₁ := Measure.measurable_rnDeriv _ _
  have hLaw₁ : μ = ν.withDensity D₁ :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  have hD₁2 : ∫⁻ y, D₁ y ^ (2 : ℝ) ∂ν < ⊤ := by
    have hx := rnDeriv_map_sq_finite hacPair measurable_fst hL2
    rw [hνproj, hμproj] at hx
    exact hx
  obtain ⟨r, hr, -, D₂, hD₂, hLaw₂, hD₂r⟩ :=
    rawTranslate_recentered_local_reverse hXt t hWV hKW hKV hadm hne hV₁ hVR
  have hμrec : P.map (fun ω => restrictTo W (recenteredTranslate Xt t ω)) =
      P.map (fun ω => restrictTo W (Xt ω)) := by
    have ht := recenteredTranslate_normalized hXt t
    calc
      P.map (fun ω => restrictTo W (recenteredTranslate Xt t ω)) =
          (P.map (recenteredTranslate Xt t)).map (restrictTo W) := by
            rw [Measure.map_map (measurable_restrictTo W) ht.1.1.measurable]
            rfl
      _ = (P.map Xt).map (restrictTo W) := by rw [ht.2]
      _ = P.map (fun ω => restrictTo W (Xt ω)) := by
        rw [Measure.map_map (measurable_restrictTo W) hXt.1.measurable]
        rfl
  have hLaw₂' : P.map (fun ω => restrictTo W (Xt ω)) = μ.withDensity D₂ := by
    rw [← hμrec]
    exact hLaw₂
  have hD₂r' : ∫⁻ y, D₂ y ^ r ∂(ν.withDensity D₁) < ⊤ := by
    rw [← hLaw₁]
    exact hD₂r
  obtain ⟨hp, hcomp, hMom⟩ :=
    withDensity_compose_moment ν D₁ D₂ hD₁ hD₂ hD₁2 hr hD₂r'
  refine ⟨hγm, Xt, hγmMeas, hγae, hXt,
    2 * r / (r + 1), hp, (fun y => D₁ y * D₂ y), hD₁.mul hD₂, ?_, hMom⟩
  calc
    P.map (fun ω => restrictTo W (Xt ω)) = μ.withDensity D₂ := hLaw₂'
    _ = (ν.withDensity D₁).withDensity D₂ := by rw [← hLaw₁]
    _ = ν.withDensity (fun y => D₁ y * D₂ y) := hcomp

end MatedCRTHarmonic.GMSCM
