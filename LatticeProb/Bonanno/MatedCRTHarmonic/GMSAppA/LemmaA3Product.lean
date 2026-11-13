/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3Product at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.CoupledLongRange
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.Freeze

/-!
# [18] Lemma A.3 for product data: conditional expectations as integrals

The probabilistic skeleton of [18] Lemma A.3 (proof ): the
field restricted to `𝔻` is `Φ`-determined by three random elements — the harmonic part minus its centre value `E`,
The circle average `C = h_1(0)` and the zero-boundary part `Z` — with `(E, C)` measurable for the exterior σ-algebra
`𝒢`, `Z` independent of `𝒢`, `C` independent of `(E, Z)` and `E` independent of `Z`. Then

* `E[X | 𝒢](ω) = ∫ Φ(E ω, C ω, z) dν_Z(z)` and `E[X | σ(C)](ω) = ∫∫ Φ(E ω', C ω, z) dν_Z(z) dP(ω')`
  (`condExp_eq_A`, `condExp_eq_B`, from the freezing lemma `condExp_comp_indep_of_integrable`).

With a Cameron–Martin change of measure between `ν_Z` shifted by the two harmonic parts `e, e'` (density `ρ` with the
moments of a Gaussian tilt of variance `≤ M(e, e')`) and an exponential moment of `M`, the sandwich (A.13)–(A.14) at
fixed `(ω, ω')` (`TiltSandwich`) and the coupled moment bound (`coupled_longRange`) give (A.6)
(`lemmaA3_product`, for `X ≥ 0`).

* `condExp_eq_A`, `condExp_eq_B` — the two representations.
* `lintegral_comp_eq_of_indep` — law identities used for the moments.
* **`lemmaA3_product`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {Ω 𝓔 𝓒 𝓩 : Type*} {𝓖 m0 : MeasurableSpace Ω} [MeasurableSpace 𝓔] [MeasurableSpace 𝓒]
  [MeasurableSpace 𝓩] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `E[Φ(E, C, Z) | 𝒢] = ∫ Φ(E, C, z) dν_Z(z)` when `(E, C)` is `𝒢`-measurable and `Z` is independent of `𝒢`. -/
theorem condExp_eq_A (h𝓖 : 𝓖 ≤ m0) {E : Ω → 𝓔} {C : Ω → 𝓒} {Z : Ω → 𝓩}
    (hE : Measurable[𝓖] E) (hC : Measurable[𝓖] C) (hZ : Measurable Z)
    (hind : Indep 𝓖 (MeasurableSpace.comap Z inferInstance) P) {Φ : 𝓔 × 𝓒 × 𝓩 → ℝ}
    (hΦ : Measurable Φ) (hi : Integrable (fun ω => Φ (E ω, C ω, Z ω)) P) :
    P[fun ω => Φ (E ω, C ω, Z ω) | 𝓖] =ᵐ[P] fun ω => ∫ z, Φ (E ω, C ω, z) ∂(P.map Z) := by
  have hf : Measurable fun p : (𝓔 × 𝓒) × 𝓩 => Φ (p.1.1, p.1.2, p.2) :=
    hΦ.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact condExp_comp_indep_of_integrable (S := fun ω => (E ω, C ω)) (R := Z)
    (f := fun p => Φ (p.1.1, p.1.2, p.2)) h𝓖 (hE.prodMk hC) hZ hind hf hi

/-- `E[Φ(E, C, Z) | σ(C)] = ∫ Φ(e, C, z) d(ν_E ⊗ ν_Z)(e, z)` when `C` is independent of `(E, Z)` and `E` of `Z`. -/
theorem condExp_eq_B {E : Ω → 𝓔} {C : Ω → 𝓒} {Z : Ω → 𝓩} (hE : Measurable E) (hC : Measurable C)
    (hZ : Measurable Z) (hCEZ : IndepFun C (fun ω => (E ω, Z ω)) P) (hEZ : IndepFun E Z P)
    {Φ : 𝓔 × 𝓒 × 𝓩 → ℝ} (hΦ : Measurable Φ) (hi : Integrable (fun ω => Φ (E ω, C ω, Z ω)) P) :
    P[fun ω => Φ (E ω, C ω, Z ω) | MeasurableSpace.comap C inferInstance] =ᵐ[P]
      fun ω => ∫ x, Φ (x.1, C ω, x.2) ∂((P.map E).prod (P.map Z)) := by
  have hf : Measurable fun p : 𝓒 × (𝓔 × 𝓩) => Φ (p.2.1, p.1, p.2.2) :=
    hΦ.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hind : Indep (MeasurableSpace.comap C inferInstance)
      (MeasurableSpace.comap (fun ω => (E ω, Z ω)) inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).1 hCEZ
  have h := condExp_comp_indep_of_integrable (S := C) (R := fun ω => (E ω, Z ω))
    (f := fun p => Φ (p.2.1, p.1, p.2.2)) hC.comap_le (comap_measurable C) (hE.prodMk hZ) hind
    hf hi
  have hmap : P.map (fun ω => (E ω, Z ω)) = (P.map E).prod (P.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map hE.aemeasurable hZ.aemeasurable).1 hEZ
  rw [hmap] at h
  exact h

/-! ### Law identities -/

/-- `∫∫ f(E ω, C ω, z) dν_Z dP = E f(E, C, Z)` when `Z` is independent of `(E, C)`. -/
theorem lintegral_lintegral_eq_of_indepFun {E : Ω → 𝓔} {C : Ω → 𝓒} {Z : Ω → 𝓩} (hE : Measurable E)
    (hC : Measurable C) (hZ : Measurable Z) (hECZ : IndepFun (fun ω => (E ω, C ω)) Z P)
    {f : 𝓔 × 𝓒 × 𝓩 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ z, f (E ω, C ω, z) ∂(P.map Z) ∂P = ∫⁻ ω, f (E ω, C ω, Z ω) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hE.prodMk hC).aemeasurable
    hZ.aemeasurable).1 hECZ
  have hg : Measurable fun p : (𝓔 × 𝓒) × 𝓩 => f (p.1.1, p.1.2, p.2) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  calc ∫⁻ ω, ∫⁻ z, f (E ω, C ω, z) ∂(P.map Z) ∂P
      = ∫⁻ y, ∫⁻ z, f (y.1, y.2, z) ∂(P.map Z) ∂(P.map fun ω => (E ω, C ω)) := by
        rw [lintegral_map (hg.lintegral_prod_right') (hE.prodMk hC)]
    _ = ∫⁻ p, f (p.1.1, p.1.2, p.2) ∂((P.map fun ω => (E ω, C ω)).prod (P.map Z)) :=
        (lintegral_prod _ hg.aemeasurable).symm
    _ = ∫⁻ ω, f (E ω, C ω, Z ω) ∂P := by
        rw [← hmap, lintegral_map hg ((hE.prodMk hC).prodMk hZ)]

/-- `∫∫∫ f(E ω', C ω, z) dν_Z dP(ω') dP(ω) = E f(E, C, Z)` when `C` is independent of `(E, Z)` and `E` of `Z`. -/
theorem lintegral_lintegral_lintegral_eq_of_indepFun {E : Ω → 𝓔} {C : Ω → 𝓒} {Z : Ω → 𝓩}
    (hE : Measurable E) (hC : Measurable C) (hZ : Measurable Z)
    (hCEZ : IndepFun C (fun ω => (E ω, Z ω)) P) (hEZ : IndepFun E Z P)
    {f : 𝓔 × 𝓒 × 𝓩 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ ω', ∫⁻ z, f (E ω', C ω, z) ∂(P.map Z) ∂P ∂P = ∫⁻ ω, f (E ω, C ω, Z ω) ∂P := by
  have hmapEZ := (indepFun_iff_map_prod_eq_prod_map_map hE.aemeasurable hZ.aemeasurable).1 hEZ
  have hmapC := (indepFun_iff_map_prod_eq_prod_map_map hC.aemeasurable
    (hE.prodMk hZ).aemeasurable).1 hCEZ
  have hg : Measurable fun p : 𝓒 × (𝓔 × 𝓩) => f (p.2.1, p.1, p.2.2) :=
    hf.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hinner : ∀ c : 𝓒, ∫⁻ ω', ∫⁻ z, f (E ω', c, z) ∂(P.map Z) ∂P =
      ∫⁻ y, f (y.1, c, y.2) ∂(P.map fun ω => (E ω, Z ω)) := by
    intro c
    have hgc : Measurable fun y : 𝓔 × 𝓩 => f (y.1, c, y.2) :=
      hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    rw [hmapEZ, lintegral_prod _ hgc.aemeasurable,
      lintegral_map (hgc.lintegral_prod_right') hE]
  simp_rw [hinner]
  calc ∫⁻ ω, ∫⁻ y, f (y.1, C ω, y.2) ∂(P.map fun ω => (E ω, Z ω)) ∂P
      = ∫⁻ c, ∫⁻ y, f (y.1, c, y.2) ∂(P.map fun ω => (E ω, Z ω)) ∂(P.map C) := by
        rw [lintegral_map (hg.lintegral_prod_right') hC]
    _ = ∫⁻ p, f (p.2.1, p.1, p.2.2) ∂((P.map C).prod (P.map fun ω => (E ω, Z ω))) :=
        (lintegral_prod _ hg.aemeasurable).symm
    _ = ∫⁻ ω, f (E ω, C ω, Z ω) ∂P := by
        rw [← hmapC, lintegral_map hg (hC.prodMk (hE.prodMk hZ))]

end MatedCRTHarmonic.GMSAppA
