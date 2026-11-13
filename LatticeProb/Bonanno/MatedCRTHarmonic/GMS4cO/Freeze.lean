/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Freeze at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

/-!
# Freezing an independent local factor

The probabilistic core of the proof of [18] Lemma 4.9 :
after the affine rescaling of the proof, the localized observable at `z` is bounded by a jointly measurable
function `G(a, L)` of the conditioning variable `a` (the circle averages) and of a *local* random element `L`
which is independent of `a` ([18] Lemma A.2; in this formalization the Radon–Nikodym derivative of Lemma A.2
is identically `1`, `GMSAppA.lemmaA2_indepFun`). If every frozen slice `x ↦ E[G(x, L)]` is bounded by `M`
(the `ε`-uniform moment of [18] Theorem 4.4), then the conditional expectation given `a` is at most `M`.

* `L43O.setLIntegral_comp_indep_le`: `∫⁻_{a ∈ A} G(a, L) ≤ M · P(a ∈ A)` for every measurable `A`;
* `L43O.setLIntegral_le_of_le_comp_indep`: the same for any `Y ≤ G(a, L)` a.e.;
* `L43O.condExp_le_of_setIntegral_le`: a real integrable `f` whose set integrals over `σ(a)` are bounded by
  `M · P(a ∈ A)` has `E[f | σ(a)] ≤ M` almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MatedCRTHarmonic.L43O

variable {Ω F E : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]
/-- **Freezing.** If `a ⟂ L` and every frozen slice `x ↦ E[G(x, L)]` is at most `M`, then
`∫⁻_{a ∈ A} G(a, L) dP ≤ M · P(a ∈ A)` for every measurable `A`. -/
theorem setLIntegral_comp_indep_le {a : Ω → F} {L : Ω → E} (ha : AEMeasurable a P)
    (hL : AEMeasurable L P) (hind : IndepFun a L P) {G : F × E → ℝ≥0∞} (hG : Measurable G)
    {M : ℝ≥0∞} (hM : ∀ x, ∫⁻ ω, G (x, L ω) ∂P ≤ M) {A : Set F} (hA : MeasurableSet A) :
    ∫⁻ ω in a ⁻¹' A, G (a ω, L ω) ∂P ≤ M * P (a ⁻¹' A) := by
  have hprod : P.map (fun ω => (a ω, L ω)) = (P.map a).prod (P.map L) :=
    (indepFun_iff_map_prod_eq_prod_map_map ha hL).1 hind
  have hGA : Measurable fun y : F × E => A.indicator (fun _ => (1 : ℝ≥0∞)) y.1 * G y :=
    ((measurable_const.indicator hA).comp measurable_fst).mul hG
  have hSFL : SFinite (P.map L) := inferInstance
  have hpre : NullMeasurableSet (a ⁻¹' A) P := ha.nullMeasurable hA
  calc ∫⁻ ω in a ⁻¹' A, G (a ω, L ω) ∂P
      = ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) (a ω) * G (a ω, L ω) ∂P := by
        rw [← lintegral_indicator₀ hpre]
        congr 1
        funext ω
        by_cases hω : a ω ∈ A
        · simp [Set.indicator, hω]
        · simp [Set.indicator, hω]
    _ = ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) y.1 * G y ∂(P.map fun ω => (a ω, L ω)) := by
        rw [lintegral_map' hGA.aemeasurable (ha.prodMk hL)]
    _ = ∫⁻ x, ∫⁻ ℓ, A.indicator (fun _ => (1 : ℝ≥0∞)) x * G (x, ℓ) ∂(P.map L) ∂(P.map a) := by
        rw [hprod, lintegral_prod _ hGA.aemeasurable]
    _ = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * ∫⁻ ℓ, G (x, ℓ) ∂(P.map L) ∂(P.map a) := by
        congr 1
        funext x
        rw [lintegral_const_mul (f := fun ℓ => G (x, ℓ)) _ (hG.comp measurable_prodMk_left)]
    _ ≤ ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * M ∂(P.map a) := by
        refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
        rw [lintegral_map' (f := fun ℓ => G (x, ℓ)) (hG.comp measurable_prodMk_left).aemeasurable hL]
        exact hM x
    _ = M * P (a ⁻¹' A) := by
        rw [lintegral_mul_const _ (measurable_const.indicator hA), lintegral_indicator hA,
          setLIntegral_const, one_mul, Measure.map_apply_of_aemeasurable ha hA, mul_comm]

/-- **Freezing with an almost-everywhere slice bound.** As `setLIntegral_comp_indep_le`, but the frozen slices
need only be bounded for `law(a)`-almost every value. -/
theorem setLIntegral_comp_indep_le_ae {a : Ω → F} {L : Ω → E} (ha : AEMeasurable a P)
    (hL : AEMeasurable L P) (hind : IndepFun a L P) {G : F × E → ℝ≥0∞} (hG : Measurable G)
    {M : ℝ≥0∞} (hM : ∀ᵐ x ∂(P.map a), ∫⁻ ω, G (x, L ω) ∂P ≤ M) {A : Set F}
    (hA : MeasurableSet A) :
    ∫⁻ ω in a ⁻¹' A, G (a ω, L ω) ∂P ≤ M * P (a ⁻¹' A) := by
  have hprod : P.map (fun ω => (a ω, L ω)) = (P.map a).prod (P.map L) :=
    (indepFun_iff_map_prod_eq_prod_map_map ha hL).1 hind
  have hGA : Measurable fun y : F × E => A.indicator (fun _ => (1 : ℝ≥0∞)) y.1 * G y :=
    ((measurable_const.indicator hA).comp measurable_fst).mul hG
  have hpre : NullMeasurableSet (a ⁻¹' A) P := ha.nullMeasurable hA
  calc ∫⁻ ω in a ⁻¹' A, G (a ω, L ω) ∂P
      = ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) (a ω) * G (a ω, L ω) ∂P := by
        rw [← lintegral_indicator₀ hpre]
        congr 1
        funext ω
        by_cases hω : a ω ∈ A
        · simp [Set.indicator, hω]
        · simp [Set.indicator, hω]
    _ = ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) y.1 * G y ∂(P.map fun ω => (a ω, L ω)) := by
        rw [lintegral_map' hGA.aemeasurable (ha.prodMk hL)]
    _ = ∫⁻ x, ∫⁻ ℓ, A.indicator (fun _ => (1 : ℝ≥0∞)) x * G (x, ℓ) ∂(P.map L) ∂(P.map a) := by
        rw [hprod, lintegral_prod _ hGA.aemeasurable]
    _ = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * ∫⁻ ℓ, G (x, ℓ) ∂(P.map L) ∂(P.map a) := by
        congr 1
        funext x
        rw [lintegral_const_mul (f := fun ℓ => G (x, ℓ)) _ (hG.comp measurable_prodMk_left)]
    _ ≤ ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * M ∂(P.map a) := by
        refine lintegral_mono_ae (hM.mono fun x hx => mul_le_mul' le_rfl ?_)
        rw [lintegral_map' (f := fun ℓ => G (x, ℓ)) (hG.comp measurable_prodMk_left).aemeasurable hL]
        exact hx
    _ = M * P (a ⁻¹' A) := by
        rw [lintegral_mul_const _ (measurable_const.indicator hA), lintegral_indicator hA,
          setLIntegral_const, one_mul, Measure.map_apply_of_aemeasurable ha hA, mul_comm]

/-- **Freezing with domination.** If `Y ≤ G(a, L)` almost surely, `a ⟂ L` and every frozen slice of `G` has
expectation at most `M`, then `∫⁻_{a ∈ A} Y ≤ M · P(a ∈ A)`. -/
theorem setLIntegral_le_of_le_comp_indep {a : Ω → F} {L : Ω → E} (ha : AEMeasurable a P)
    (hL : AEMeasurable L P) (hind : IndepFun a L P) {G : F × E → ℝ≥0∞} (hG : Measurable G)
    {M : ℝ≥0∞} (hM : ∀ x, ∫⁻ ω, G (x, L ω) ∂P ≤ M) {Y : Ω → ℝ≥0∞}
    (hY : ∀ᵐ ω ∂P, Y ω ≤ G (a ω, L ω)) {A : Set F} (hA : MeasurableSet A) :
    ∫⁻ ω in a ⁻¹' A, Y ω ∂P ≤ M * P (a ⁻¹' A) :=
  (lintegral_mono_ae (ae_restrict_of_ae hY)).trans
    (setLIntegral_comp_indep_le ha hL hind hG hM hA)

/-- **From set bounds to a conditional-expectation bound.** If a real integrable `f` satisfies
`∫_{a ∈ A} f ≤ M · P(a ∈ A)` for every measurable `A`, then `E[f | σ(a)] ≤ M` almost surely. -/
theorem condExp_le_of_setIntegral_le {a : Ω → F} (ha : Measurable a) {f : Ω → ℝ}
    (hf : Integrable f P) {M : ℝ}
    (hbound : ∀ A : Set F, MeasurableSet A →
      ∫ ω in a ⁻¹' A, f ω ∂P ≤ M * (P (a ⁻¹' A)).toReal) :
    ∀ᵐ ω ∂P, P[f | MeasurableSpace.comap a inferInstance] ω ≤ M := by
  have hle : MeasurableSpace.comap a inferInstance ≤ ‹MeasurableSpace Ω› := ha.comap_le
  have hcm : StronglyMeasurable[MeasurableSpace.comap a inferInstance]
      (P[f | MeasurableSpace.comap a inferInstance]) := stronglyMeasurable_condExp
  have hint_c : Integrable (P[f | MeasurableSpace.comap a inferInstance]) (P.trim hle) :=
    integrable_condExp.trim hle hcm
  have hint_M : Integrable (fun _ : Ω => M) (P.trim hle) := integrable_const M
  have key : ∀ᵐ ω ∂P.trim hle, P[f | MeasurableSpace.comap a inferInstance] ω ≤ M := by
    refine ae_le_of_forall_setIntegral_le hint_c hint_M fun S hS _ => ?_
    rw [← setIntegral_trim hle hcm hS, setIntegral_condExp hle hf hS,
      ← setIntegral_trim hle stronglyMeasurable_const hS, setIntegral_const, smul_eq_mul]
    obtain ⟨A, hA, rfl⟩ := hS
    rw [Measure.real, mul_comm]
    exact hbound A hA
  exact ae_of_ae_trim hle key

end MatedCRTHarmonic.L43O
