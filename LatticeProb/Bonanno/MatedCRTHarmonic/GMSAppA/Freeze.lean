/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.Freeze at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Freezing lemma for conditional expectations, integrable version

If `S` is `𝒢`-measurable and `R` is independent of `𝒢`, then for every measurable `f` with `f(S, R)` integrable,
`E[f(S, R) | 𝒢] = F̄(S)` with `F̄(s) = ∫ f(s, r) d(law R)(r)`. No standard-Borel hypothesis on the target of `R` is
needed (in the GFF applications `R` is distribution-valued). This extends LQGMetric's `CONF.condExp_comp_indep`
(bounded `f`) to integrable `f`; it is used for the two conditional expectations of [18] Lemma A.3
.

* `GMSAppA.condExp_comp_indep_of_integrable`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace MatedCRTHarmonic.GMSAppA

variable {Ω α β : Type*} {𝓖 m0 : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Freezing (integrable version)**: `E[f(S, R) | 𝓖] = ∫ f(S, r) d(law R)(r)` for `S` `𝓖`-measurable, `R`
independent of `𝓖`, `f` measurable with `f(S, R)` integrable. -/
theorem condExp_comp_indep_of_integrable (h𝓖 : 𝓖 ≤ m0) {S : Ω → α} {R : Ω → β}
    (hS : Measurable[𝓖] S) (hR : Measurable R)
    (hind : Indep 𝓖 (MeasurableSpace.comap R inferInstance) P) {f : α × β → ℝ}
    (hf : Measurable f) (hfi : Integrable (fun ω => f (S ω, R ω)) P) :
    P[fun ω => f (S ω, R ω) | 𝓖] =ᵐ[P] fun ω => ∫ r, f (S ω, r) ∂(P.map R) := by
  have hSm : Measurable S := hS.mono h𝓖 le_rfl
  have hR' : IsProbabilityMeasure (P.map R) :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 ‹_›
  have hS' : IsProbabilityMeasure (P.map S) :=
    (Measure.isProbabilityMeasure_map_iff hSm.aemeasurable).2 ‹_›
  -- the joint law of `(S, R)` is the product
  have hSR : IndepFun S R P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind hS.comap_le
  have hmapSR := (indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable hR.aemeasurable).1 hSR
  have hfprod : Integrable f ((P.map S).prod (P.map R)) := by
    rw [← hmapSR]
    exact (integrable_map_measure hf.aestronglyMeasurable (hSm.prodMk hR).aemeasurable).2 hfi
  set Fb : α → ℝ := fun s => ∫ r, f (s, r) ∂(P.map R) with hFb_def
  have hFbm : Measurable Fb := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hFbi : Integrable (fun ω => Fb (S ω)) P := by
    have := hfprod.integral_prod_left
    exact (integrable_map_measure hFbm.aestronglyMeasurable hSm.aemeasurable).1 this
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝓖 hfi
    (fun s _ _ => hFbi.integrableOn) ?_ ((hFbm.comp hS).stronglyMeasurable.aestronglyMeasurable)).symm
  intro A hA _
  -- `Z = (S, 1_A)` is `𝓖`-measurable, hence independent of `R`
  let Z : Ω → α × ℝ := fun ω => (S ω, A.indicator (fun _ => (1 : ℝ)) ω)
  have hZ𝓖 : Measurable[𝓖] Z := hS.prodMk ((measurable_const (a := (1 : ℝ))).indicator hA)
  have hZ : Measurable Z := hZ𝓖.mono h𝓖 le_rfl
  have hZR : IndepFun Z R P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind hZ𝓖.comap_le
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hR.aemeasurable).1 hZR
  have hZ' : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 ‹_›
  let G : (α × ℝ) × β → ℝ := fun p => p.1.2 * f (p.1.1, p.2)
  have hGm : Measurable G := (measurable_snd.comp measurable_fst).mul
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hGZR : (fun ω => G (Z ω, R ω)) = A.indicator fun ω => f (S ω, R ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [G, Z, hω]
  have hGi : Integrable (fun ω => G (Z ω, R ω)) P := by
    rw [hGZR]; exact hfi.indicator (h𝓖 _ hA)
  have hGprod : Integrable G ((P.map Z).prod (P.map R)) := by
    rw [← hmap]
    exact (integrable_map_measure hGm.aestronglyMeasurable (hZ.prodMk hR).aemeasurable).2 hGi
  have h1 : ∫ ω in A, f (S ω, R ω) ∂P = ∫ ω, G (Z ω, R ω) ∂P := by
    rw [hGZR, integral_indicator (h𝓖 _ hA)]
  have h2 : ∫ ω, G (Z ω, R ω) ∂P = ∫ z, ∫ r, G (z, r) ∂(P.map R) ∂(P.map Z) := by
    rw [← integral_prod _ hGprod, ← hmap,
      integral_map (hZ.prodMk hR).aemeasurable hGm.aestronglyMeasurable]
  have h3 : ∀ z : α × ℝ, ∫ r, G (z, r) ∂(P.map R) = z.2 * Fb z.1 := fun z => by
    simp only [G, hFb_def]; rw [integral_const_mul]
  have h4 : ∫ z, z.2 * Fb z.1 ∂(P.map Z) = ∫ ω, (Z ω).2 * Fb (Z ω).1 ∂P :=
    integral_map hZ.aemeasurable
      ((measurable_snd.mul (hFbm.comp measurable_fst)).aestronglyMeasurable)
  have h5 : (fun ω => (Z ω).2 * Fb (Z ω).1) = A.indicator fun ω => Fb (S ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Z, hω]
  rw [h1, h2]
  simp_rw [h3]
  rw [h4, h5, integral_indicator (h𝓖 _ hA)]

end MatedCRTHarmonic.GMSAppA
