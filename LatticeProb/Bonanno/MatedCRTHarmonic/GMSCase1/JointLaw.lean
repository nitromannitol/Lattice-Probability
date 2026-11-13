/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.JointLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.FieldLaw

/-!
# [18] Proposition 4.10, Case 1: the rooted joint law on the frozen coupling

Source: [18] (Case 1) and DMS14 Lemma A.10
.

On the frozen coupling `D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm` the
**whole-plane data** of [18] §4 are :

* the unit-normalized whole-plane GFF `h₀ = X₀ − (X₀)_1(0)` (CANON's `normalizeWholePlane`);
* the imaginary-geometry coordinates `(hIG₀, U)` (the IG field is `hIG₀ + U`; the phase `U` is
  kept);
* the Lebesgue-time whole-plane space-filling SLE `ηL`.

Every whole-plane observable of [18] §4 — the GMC area of the field, the area-time curve
`ηWP = ηL` reparametrized by that area (the area-scaling construction's measurable `JointScalingO.parEval`), the local
degrees, `u_*^ε`, the bad events of (4.40) — is a function of these data `wpData`. With the root
`z` sampled from `Canon.rootMeasure` (normalized Lebesgue measure on `𝔻`) independently, i.e.
under `Canon.rootedLaw P = P ⊗ rootMeasure`, the Case 1 field is
`h₁ = Canon.rootedField γ h₀ z` and the rooted data are `rootedWPData = (h₁, (hIG₀, U), ηL)`.

**Main theorem** (`rootedWPData_law`): the law of the rooted data is the law of the unrooted data
weighted by `μ_{h₀}(𝔻) / E[μ_{h₀}(𝔻)] = μ_{h₀}(𝔻) / π`. The proof lifts the rooting construction's field-law identity
to the joint law using the frozen independence `indep_curve` (the IG data are independent of
`X₀`) and the IG-measurability of `ηL` (`igMap`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-! ## The whole-plane data carrier -/

/-- The auxiliary whole-plane coordinates `((hIG₀, U), ηL)`. -/
abbrev AuxData : Type := (DistC × ℝ) × C(ℝ, ℂ)

/-- The whole-plane data `(field, ((hIG₀, U), ηL))`. -/
abbrev WPData : Type := DistC × AuxData

section Maps

variable {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ) (ηL : Ω → C(ℝ, ℂ))

/-- The unit-normalized whole-plane GFF `h₀` of the coupling. -/
def wpField (ω : Ω) : DistC := Canon.normalizeWholePlane (X₀ ω)

/-- The auxiliary coordinates of the coupling. -/
def wpAux (ω : Ω) : AuxData := ((hIG₀ ω, U ω), ηL ω)

/-- The unrooted whole-plane data `(h₀, ((hIG₀, U), ηL))`. -/
def wpData (ω : Ω) : WPData := (wpField X₀ ω, wpAux hIG₀ U ηL ω)

/-- The Case 1 field `h₁ = normalize(h₀ − γ log|·−z| + γ log max(|·|,1))` at the marked root. -/
def rootedWPField (v : Ω × ℂ) : DistC := Canon.rootedField γ (wpField X₀ v.1) v.2

/-- The Case 1 data `(h₁, ((hIG₀, U), ηL))` on the marked carrier `Ω × ℂ`. -/
def rootedWPData (v : Ω × ℂ) : WPData :=
  (rootedWPField γ X₀ v, wpAux hIG₀ U ηL v.1)

end Maps

/-- The rooting of whole-plane data: `((h, a), z) ↦ (rootedField γ h z, a)`. -/
def rootData (γ : ℝ) (y : WPData × ℂ) : WPData := (Canon.rootedField γ y.1.1 y.2, y.1.2)

theorem measurable_rootData (γ : ℝ) : Measurable (rootData γ) :=
  ((measurable_rootingMap γ).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst)

/-- The root law (normalized Lebesgue measure on `𝔻`) is a probability measure. -/
instance isProbabilityMeasure_rootMeasure : IsProbabilityMeasure Canon.rootMeasure := by
  change IsProbabilityMeasure GMS4.GMSA.normalizedLebesgueOnRootingDisk
  infer_instance

/-! ## Measurability and independence on the frozen coupling -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The unit-normalization `h ↦ h − h_1(0)` is measurable. -/
theorem measurable_normalizeWholePlane : Measurable Canon.normalizeWholePlane :=
  LQGMetric.DFGPS.L219.measurable_addConst_of measurable_id
    (measurable_circleAvg_left 1 0).neg

theorem measurable_wpField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable (wpField X₀) :=
  Canon.measurable_normalizedWholePlane D

theorem isNormalizedWPGFF_wpField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IsNormalizedWPGFF (wpField X₀) P :=
  Canon.normalizedWPGFF_of_coupling D

theorem aemeasurable_wpAux
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (wpAux hIG₀ U ηL) P :=
  (D.igField.1.1.measurable.aemeasurable.prodMk (Canon.aemeasurable_phase D hγ)).prodMk
    D.measurable_curves.1.aemeasurable

theorem aemeasurable_wpData
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (wpData X₀ hIG₀ U ηL) P :=
  (measurable_wpField D).aemeasurable.prodMk (aemeasurable_wpAux D hγ)

/-- The IG input `(ρ, w) ↦ circleAvg hIG₀ ρ w + U` of the bundle's curve map, as a measurable
function of `(hIG₀, U)`. -/
def igInput (a : DistC × ℝ) : ℝ → ℂ → ℝ := fun ρ w => circleAvg a.1 ρ w + a.2

theorem measurable_igInput : Measurable igInput := by
  refine measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun w => ?_
  exact ((measurable_circleAvg_left ρ w).comp measurable_fst).add measurable_snd

/-- **Independence of the field and the auxiliary data.** The normalized whole-plane GFF `h₀`
is independent of `((hIG₀, U), ηL)`: `indep_curve` makes `(hIG₀, U)` independent of `X₀`, and
`ηL` is a.s. a measurable function of `(hIG₀, U)` (`igMap`). -/
theorem indepFun_wpField_wpAux
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (wpField X₀) (wpAux hIG₀ U ηL) P := by
  obtain ⟨Φ, hΦ, -, hηL, -⟩ := D.igMap
  have hproj : Measurable fun t : DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × DistC × (ℝ≥0 → ℝ) ×
      (ℝ≥0 → ℝ) => Canon.normalizeWholePlane t.2.2.2.1 :=
    measurable_normalizeWholePlane.comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  let G : DistC × ℝ → AuxData := fun a => (a, Φ (igInput a))
  have hG : Measurable G := measurable_id.prodMk (hΦ.comp measurable_igInput)
  have h1 : IndepFun (fun ω => G (hIG₀ ω, U ω)) (wpField X₀) P :=
    D.indep_curve.comp hG hproj
  have h2 : (fun ω => G (hIG₀ ω, U ω)) =ᵐ[P] wpAux hIG₀ U ηL := by
    filter_upwards [hηL] with ω hω
    simp only [G, wpAux, hω]
    rfl
  exact (h1.congr h2 (Filter.EventuallyEq.refl _ _)).symm

/-- The unrooted data law is the product of the field law and the auxiliary law. -/
theorem map_wpData_eq_prod
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    P.map (wpData X₀ hIG₀ U ηL) = (P.map (wpField X₀)).prod (P.map (wpAux hIG₀ U ηL)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact (indepFun_wpField_wpAux D).map_prod_eq_prod_map_map
    (measurable_wpField D).aemeasurable (aemeasurable_wpAux D hγ)

/-- On the marked carrier, the pair (unrooted data, root) has law `P.map wpData ⊗ rootMeasure`. -/
theorem map_wpData_root_eq_prod
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (Canon.rootedLaw P).map (fun v : Ω × ℂ => (wpData X₀ hIG₀ U ηL v.1, v.2)) =
      (P.map (wpData X₀ hIG₀ U ηL)).prod Canon.rootMeasure := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hW := aemeasurable_wpData D hγ
  have hae : (fun v : Ω × ℂ => (wpData X₀ hIG₀ U ηL v.1, v.2)) =ᵐ[Canon.rootedLaw P]
      Prod.map (hW.mk _) id := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Canon.rootMeasure)).ae_eq_comp
      hW.ae_eq_mk
    filter_upwards [h] with v hv
    exact Prod.ext hv rfl
  rw [Measure.map_congr hae, Canon.rootedLaw,
    ← Measure.map_prod_map _ _ hW.measurable_mk measurable_id, Measure.map_id,
    Measure.map_congr hW.ae_eq_mk]

theorem aemeasurable_rootedWPData
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (rootedWPData γ X₀ hIG₀ U ηL) (Canon.rootedLaw P) := by
  have hpair : AEMeasurable (fun v : Ω × ℂ => (wpData X₀ hIG₀ U ηL v.1, v.2))
      (Canon.rootedLaw P) :=
    ((aemeasurable_wpData D hγ).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable
  have e : rootedWPData γ X₀ hIG₀ U ηL =
      rootData γ ∘ fun v : Ω × ℂ => (wpData X₀ hIG₀ U ηL v.1, v.2) := rfl
  rw [e]
  exact (measurable_rootData γ).comp_aemeasurable hpair

/-! ## The Case 1 joint law -/

/-- **[18] Proposition 4.10, Case 1, on the data carrier.** The rooted data law is the unrooted
data law weighted by the measurable DMS A.10 density of the field coordinate. -/
theorem map_rootedWPData_eq_withDensity
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (Canon.rootedLaw P).map (rootedWPData γ X₀ hIG₀ U ηL) =
      (P.map (wpData X₀ hIG₀ U ηL)).withDensity (fun x => areaDensity γ x.1) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hpair : AEMeasurable (fun v : Ω × ℂ => (wpData X₀ hIG₀ U ηL v.1, v.2))
      (Canon.rootedLaw P) :=
    ((aemeasurable_wpData D hγ).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable
  have hcomp : (Canon.rootedLaw P).map (rootedWPData γ X₀ hIG₀ U ηL) =
      ((Canon.rootedLaw P).map fun v : Ω × ℂ => (wpData X₀ hIG₀ U ηL v.1, v.2)).map
        (rootData γ) :=
    (AEMeasurable.map_map_of_aemeasurable (measurable_rootData γ).aemeasurable hpair).symm
  have hfield := map_rootedField_eq_withDensity (isNormalizedWPGFF_wpField D) hγ
  rw [hcomp, map_wpData_root_eq_prod D hγ, map_wpData_eq_prod D hγ]
  exact map_rootedPair_eq_withDensity _ _ _ (measurable_rootingMap γ)
    (measurable_areaDensity γ).aemeasurable hfield

/-- The DMS A.10 weight `μ_{h₀}(𝔻)/π` agrees a.s. with the measurable density of `h₀`. -/
theorem ae_areaDensity_wpField_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, areaDensity γ (wpField X₀ ω) =
      (Canon.referenceSample D hγ ω).wholePlaneArea (ball 0 1) / ENNReal.ofReal Real.pi :=
  ae_areaDensity_eq (isNormalizedWPGFF_wpField D).1 hγ

end Coupling

end MatedCRTHarmonic.GMSCase1
