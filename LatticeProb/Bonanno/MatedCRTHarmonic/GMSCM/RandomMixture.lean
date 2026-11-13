/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.RandomMixture at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (the measurability argument goes to eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top). -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.DataProcessing
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Data processing for the moment of a random Cameron–Martin mixture

The conditional Cameron–Martin density for the local field is the density of a
joint law on the outside data and the zero-boundary GFF, pushed forward to the
observation. This file proves the Rényi-moment contraction under that pushforward
for every finite exponent at least one. It is the Jensen step in continuation c1.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]

/-- Conditional expectation contracts the real-valued Radon–Nikodym derivative
in every `L^p`, `p ≥ 1`. -/
theorem rnDeriv_map_memLp (hμν : μ ≪ ν) {f : Ω → S} (hf : Measurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hLp : MemLp (fun ω => (μ.rnDeriv ν ω).toReal) p ν) :
    MemLp (fun x => ((μ.map f).rnDeriv (ν.map f) x).toReal) p (ν.map f) := by
  let : IsProbabilityMeasure (ν.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  have hcond : MemLp
      (ν[fun ω => (μ.rnDeriv ν ω).toReal | MeasurableSpace.comap f ‹MeasurableSpace S›]) p ν :=
    hLp.condExp hp
  have hae := toReal_rnDeriv_map hμν hf
  have hcomp : MemLp
      ((fun x => ((μ.map f).rnDeriv (ν.map f) x).toReal) ∘ f) p ν :=
    (memLp_congr_ae hae).2 hcond
  exact (memLp_map_measure_iff
    ((Measure.measurable_rnDeriv (μ.map f) (ν.map f)).ennreal_toReal.aestronglyMeasurable)
    hf.aemeasurable).2 hcomp

/-- A finite `p`-moment of an RN derivative remains finite after any measurable
observation. This is the measure-theoretic mixture/Jensen inequality needed for
the random normalization constant. -/
theorem rnDeriv_map_moment_finite (hμν : μ ≪ ν) {f : Ω → S} (hf : Measurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hLp : MemLp (fun ω => (μ.rnDeriv ν ω).toReal) p ν) :
    ∫⁻ x, ((μ.map f).rnDeriv (ν.map f) x) ^ p.toReal ∂(ν.map f) < ⊤ := by
  have hLp' := rnDeriv_map_memLp hμν hf hp hLp
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hLp'
  have hae : ∀ᵐ x ∂(ν.map f), (μ.map f).rnDeriv (ν.map f) x ≠ ⊤ :=
    Measure.rnDeriv_ne_top (μ.map f) (ν.map f)
  convert hfin using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp [hx]

omit [IsFiniteMeasure μ] in
/-- An explicit density with a finite `p`-moment is an `L^p` RN derivative.
This conversion lets the conditional expectation theorem handle the random
mixture without writing a separate perspective-convexity proof. -/
theorem rnDeriv_memLp_of_withDensity {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ)
    (hμ : μ = ν.withDensity ρ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (hρp : ∫⁻ ω, ρ ω ^ p.toReal ∂ν < ⊤) :
    MemLp (fun ω => (μ.rnDeriv ν ω).toReal) p ν := by
  have hρLp : MemLp (fun ω => (ρ ω).toReal) p ν := by
    refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop
      hρ.ennreal_toReal.aestronglyMeasurable).2 ?_
    calc
      (∫⁻ ω, ‖(ρ ω).toReal‖ₑ ^ p.toReal ∂ν) ≤
          ∫⁻ ω, ρ ω ^ p.toReal ∂ν := by
            refine lintegral_mono fun ω => ?_
            by_cases hω : ρ ω = ⊤
            · have hppos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
              simp [hω, hppos]
            · simp [hω]
      _ < ⊤ := hρp
  have hae : μ.rnDeriv ν =ᵐ[ν] ρ := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity ν hρ
  exact (memLp_congr_ae (hae.mono fun ω hω => by rw [hω])).2 hρLp

end MatedCRTHarmonic.GMSCM

namespace MatedCRTHarmonic.GMSCM

variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    {κ : Measure A} {ν : Measure Z} [SFinite ν]

/-- The density of a mixture of shifted component laws is the component density
on the joint space of outside data and the zero-boundary field. The component
law identity is supplied pointwise by Cameron–Martin; the conclusion is a new
joint law identity, proved by Tonelli. -/
theorem mixture_map_eq_withDensity
    {shift : A → Z → Z} (hshift : Measurable (fun x : A × Z => shift x.1 x.2))
    {ρ : A → Z → ℝ≥0∞} (hρ : Measurable (fun x : A × Z => ρ x.1 x.2))
    (hcm : ∀ a, ν.map (shift a) = ν.withDensity (ρ a)) :
    (κ.prod ν).map (fun x : A × Z => (x.1, shift x.1 x.2)) =
      (κ.prod ν).withDensity (fun x => ρ x.1 x.2) := by
  have hT : Measurable (fun x : A × Z => (x.1, shift x.1 x.2)) :=
    measurable_fst.prodMk hshift
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  calc
    (∫⁻ x, Φ x ∂(κ.prod ν).map (fun x : A × Z => (x.1, shift x.1 x.2))) =
        ∫⁻ x, Φ (x.1, shift x.1 x.2) ∂κ.prod ν :=
      lintegral_map hΦ hT
    _ = ∫⁻ a, ∫⁻ z, Φ (a, shift a z) ∂ν ∂κ :=
      lintegral_prod _ (hΦ.comp hT).aemeasurable
    _ = ∫⁻ a, ∫⁻ z, ρ a z * Φ (a, z) ∂ν ∂κ := by
      refine lintegral_congr fun a => ?_
      have hsa : Measurable (shift a) := hshift.of_uncurry_left
      have hρa : Measurable (ρ a) := hρ.of_uncurry_left
      have hΦa : Measurable (fun z : Z => Φ (a, z)) :=
        hΦ.comp (measurable_const.prodMk measurable_id)
      calc
        (∫⁻ z, Φ (a, shift a z) ∂ν) = ∫⁻ z, Φ (a, z) ∂(ν.map (shift a)) :=
          (lintegral_map hΦa hsa).symm
        _ = ∫⁻ z, Φ (a, z) ∂(ν.withDensity (ρ a)) := by rw [hcm a]
        _ = ∫⁻ z, ρ a z * Φ (a, z) ∂ν :=
          lintegral_withDensity_eq_lintegral_mul ν hρa hΦa
    _ = ∫⁻ x, ρ x.1 x.2 * Φ x ∂κ.prod ν :=
      (lintegral_prod _ (hρ.mul hΦ).aemeasurable).symm
    _ = ∫⁻ x, Φ x ∂(κ.prod ν).withDensity (fun x => ρ x.1 x.2) :=
      (lintegral_withDensity_eq_lintegral_mul (κ.prod ν) hρ hΦ).symm

/-- The observed mixture has an `L^p` Radon–Nikodym density whenever the
component Cameron–Martin densities have an integrable joint `p`-moment. This
is the rigorous joint-convexity/Jensen step for random shifts. -/
theorem mixture_observation_comparison [IsProbabilityMeasure κ] [IsProbabilityMeasure ν]
    {shift : A → Z → Z} (hshift : Measurable (fun x : A × Z => shift x.1 x.2))
    {ρ : A → Z → ℝ≥0∞} (hρ : Measurable (fun x : A × Z => ρ x.1 x.2))
    (hcm : ∀ a, ν.map (shift a) = ν.withDensity (ρ a))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hρp : ∫⁻ x, ρ x.1 x.2 ^ p.toReal ∂(κ.prod ν) < ⊤)
    {S : Type*} [MeasurableSpace S] (observe : A × Z → S) (hobserve : Measurable observe) :
    ∃ M : S → ℝ≥0∞, Measurable M ∧
      (κ.prod ν).map (fun x : A × Z => observe (x.1, shift x.1 x.2)) =
        ((κ.prod ν).map observe).withDensity M ∧
      ∫⁻ x, M x ^ p.toReal ∂((κ.prod ν).map observe) < ⊤ := by
  let ξ : Measure (A × Z) := κ.prod ν
  have hξprob : IsProbabilityMeasure ξ := inferInstance
  let : IsProbabilityMeasure ξ := hξprob
  let T : A × Z → A × Z := fun x => (x.1, shift x.1 x.2)
  have hT : Measurable T := measurable_fst.prodMk hshift
  let μ : Measure (A × Z) := ξ.map T
  have hμprob : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure μ := hμprob
  let : IsFiniteMeasure μ := inferInstance
  have heq : μ = ξ.withDensity (fun x => ρ x.1 x.2) :=
    mixture_map_eq_withDensity hshift hρ hcm
  have hac : μ ≪ ξ := by
    rw [heq]
    exact withDensity_absolutelyContinuous _ _
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hLp : MemLp (fun x => (μ.rnDeriv ξ x).toReal) p ξ :=
    rnDeriv_memLp_of_withDensity hρ heq hp0 hptop hρp
  let M : S → ℝ≥0∞ := (μ.map observe).rnDeriv (ξ.map observe)
  refine ⟨M, Measure.measurable_rnDeriv _ _, ?_, ?_⟩
  · calc
      ξ.map (observe ∘ T) = μ.map observe := (Measure.map_map hobserve hT).symm
      _ = (ξ.map observe).withDensity M :=
        (Measure.withDensity_rnDeriv_eq _ _ (hac.map hobserve)).symm
  · exact rnDeriv_map_moment_finite hac hobserve hp hptop hLp

end MatedCRTHarmonic.GMSCM
