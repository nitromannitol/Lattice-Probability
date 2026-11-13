/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.WPCase34 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Translate
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTAffineReroot
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldDecomp
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Bundle
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.Case2Local
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.Representations

/-!
# [18] Proposition 4.10, Cases 3–4 on the whole-plane data `WPData` (route (c))

Source: (`[18]:N`), Proposition 4.10, Cases 3–4 and the final
paragraph, `[18]`; the Cases 1–2 on `WPData` (`GMSCase1/*`); the IG
data `((hIG₀, U), ηL)` are kept in full).

**Route (c) (repair of the Case 3 random-mesh gap).** [18] passes from the Case 2 field
`h² = h₀ − γ log|· − z|` to the γ-cone by renormalizing (`h³ = h² − h²_{1/2}(z)`) and dilating
(`h⁴ = h³(·/2 + z)`); the dilation changes the mesh by the random factor `e^{γ h²_{1/2}(z)}`, and
Case 2's fixed-mesh bounds do not control the resulting random-mesh events. Here no renormalization
and no dilation are used: for every root `z` with `‖z‖ + r ≤ 1` the translated Case 2 field
`h²(· + z) = h₀(· + z) − γ log|·|` restricted to `B_r(0)`, jointly with the IG data re-rooted at `z`
(`igTransformS (2πχ) 1 z`, curve `affineReroot z 1 0 ηL = ηL(τ_z + ·) − z`), has the law of the
γ-cone field restricted to `B_r(0)` jointly with the IG data. Thus the cone's events at mesh `ε`
are the Case 2 field's events at the **same** mesh `ε` for the translated test pair `(D + z, f(· − z))`.

Main results (namespace `MatedCRTHarmonic.GMSCase`; all on the frozen coupling `D`):

* `map_shiftedCase2_eq_cone` — fixed root `z`, `‖z‖ + r ≤ 1`;
* `map_shiftedCase2_marked_eq_cone` — independent random root `z ∼ lam`, `‖z‖ + r ≤ 1` a.s.;
* **`smallRoot_shiftedCase2_eq_cone`** — the conditional rooted law given `{z ∈ B_{ρ₀}(0)}`,
  `ρ₀ + r ≤ 1`, events of the `case2WPData` re-rooted at the marked root (`rerootData`);
* **`cone_event_le_of_case2`** — the chain to the Case 2 bound: a cone event of
  `(cone|_{B_r(0)}, wpAux)` whose re-rooted Case 2 version is contained (on the small-root event) in a
  fixed local Case 2 event has probability `≤ case1Moment^{1/p} δ^{1/q} / ρ₀²`.

Helpers: `shiftedCase2Field`, `rerootData`, `affineComp_one_ofFunC` (translation of a function
distribution), `affineComp_one_case2_eq`, `ae_rerootData_case2_eq`, `map_igTransformS_igObs`,
`map_restrict_ball_coneField`. The deterministic translation covariance of the area parametrization
and of `u_*^ε` at the same mesh is `GMSCase/AreaTranslate.lean` (imported here, so this module is the
single entry point of the Case 3–4 results).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw
open MatedCRTHarmonic.GMSCase1 (WPData AuxData wpField wpAux wpData case2WPData restrictData)

/-! ## Translation of function distributions -/

theorem locallyIntegrable_comp_add_right {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (z : ℂ) :
    LocallyIntegrable (fun w => f (w + z)) volume := by
  rw [locallyIntegrable_iff] at hf ⊢
  intro K hK
  set K' : Set ℂ := (fun w : ℂ => w + z) '' K
  have hK' : IsCompact K' := hK.image (continuous_id.add continuous_const)
  have h1 : Integrable (K'.indicator f) volume :=
    (integrable_indicator_iff hK'.measurableSet).2 (hf K' hK')
  have h2 : Integrable (fun w => K'.indicator f (w + z)) volume := h1.comp_add_right z
  have hpre : MeasurableSet ((fun w : ℂ => w + z) ⁻¹' K') :=
    hK'.isClosed.measurableSet.preimage (continuous_id.add continuous_const).measurable
  have h3 : IntegrableOn (fun w => f (w + z)) ((fun w : ℂ => w + z) ⁻¹' K') volume := by
    rw [← integrable_indicator_iff hpre]
    have e : ((fun w : ℂ => w + z) ⁻¹' K').indicator (fun w => f (w + z)) =
        fun w => K'.indicator f (w + z) := by
      funext w
      by_cases hw : w + z ∈ K'
      · rw [indicator_of_mem (show w ∈ (fun w : ℂ => w + z) ⁻¹' K' from hw),
          indicator_of_mem hw]
      · rw [indicator_of_notMem (show w ∉ (fun w : ℂ => w + z) ⁻¹' K' from hw),
          indicator_of_notMem hw]
    rw [e]
    exact h2
  exact h3.mono_set (subset_preimage_image _ _)

theorem ofFunC_apply_of_locallyIntegrable {f : ℂ → ℝ} (hf : LocallyIntegrable f volume)
    (φ : TestC) : MoTPort.ofFunC f φ = ∫ x, φ x * f x := by
  rw [MoTPort.ofFunC, Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  rfl

/-- **Translation of a function distribution**: `(ofFunC f)(· + z) = ofFunC (f(· + z))`. -/
theorem affineComp_one_ofFunC {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (z : ℂ) :
    affineComp 1 z (MoTPort.ofFunC f) = MoTPort.ofFunC (fun w => f (w + z)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.affineComp_apply, ofFunC_apply_of_locallyIntegrable hf,
    ofFunC_apply_of_locallyIntegrable (locallyIntegrable_comp_add_right hf z), one_pow, inv_one,
    one_mul, ← integral_add_right_eq_self (fun x => testAffinePull 1 z φ x * f x) z]
  congr 1
  funext v
  rw [testAffinePull_apply _ _ one_ne_zero, add_sub_cancel_right, Complex.ofReal_one, div_one]

/-! ## The re-rooted Case 2 data -/

/-- The Case 2 field `h − γ log|· − z|` translated to its root: `h(· + z) − γ log|·|`. -/
def shiftedCase2Field (γ : ℝ) (h : DistC) (z : ℂ) : DistC := addLogSing γ (affineComp 1 z h)

theorem measurable_shiftedCase2Field (γ : ℝ) :
    Measurable fun p : DistC × ℂ => shiftedCase2Field γ p.1 p.2 :=
  (measurable_addLogSing γ).comp (measurable_affineComp_center 1)

theorem restrictTo_addLogSing_on (V : Opens ℂ) (γ : ℝ) (g : DistC) :
    restrictTo V (addLogSing γ g) = restrictTo V g + restrictTo V (MoTPort.ofFunC (logSing γ)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rfl

/-- `(h − γ log|· − z|)(· + z) = h(· + z) − γ log|·|`. -/
theorem affineComp_one_case2_eq (γ : ℝ) (h : DistC) (z : ℂ) :
    affineComp 1 z (h + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖)) =
      shiftedCase2Field γ h z := by
  have hli : LocallyIntegrable (fun w : ℂ => -γ * Real.log ‖w - z‖) volume := by
    refine (locallyIntegrable_comp_add_right (locallyIntegrable_logSing γ) (-z)).congr
      (Eventually.of_forall fun w => ?_)
    simp only [logSing, ← sub_eq_add_neg]
    ring
  have e : CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖) =
      MoTPort.ofFunC (fun w => -γ * Real.log ‖w - z‖) := rfl
  rw [GM.affineComp_add, shiftedCase2Field, addLogSing, e, affineComp_one_ofFunC hli z]
  congr 2
  funext w
  simp only [logSing, add_sub_cancel_right]
  ring

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The general-scale IG transformation preserves the law of the full IG observation. -/
theorem map_igTransformS_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    [Fact (0 < 2 * Real.pi * igChi γ)] {s : ℝ} (hs : 0 < s) (z₀ : ℂ) :
    P.map (fun ω => igTransformS (2 * Real.pi * igChi γ) s z₀ (igObs hIG₀ U ηL ω)) =
      P.map (igObs hIG₀ U ηL) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Φ, hΦ, hroot, hcc⟩ :=
    igMapPos_of_igMapPositiveRadii (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D)
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.1
  exact map_igTransformS_of_ccPos D.igField.1 rfl D.igField.2.1 D.igField.2.2 hΦ hroot hcc htr hs z₀

/-- **The γ-cone on `B_r(0)` with the IG data** has the law of `(h₀ − γ log|·|)|_{B_r(0)}` with
The IG data, `h₀ = wpField X₀` (`0 < r ≤ 1`). -/
theorem map_restrict_ball_coneField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {r : ℝ} (hr1 : r ≤ 1) :
    P.map (fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), wpAux hIG₀ U ηL ω)) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω)),
        wpAux hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hh : IsNormalizedWPGFF (wpField X₀) P := GMSCase1.isNormalizedWPGFF_wpField D
  have hYa : AEMeasurable (wpAux hIG₀ U ηL) P := aemeasurable_igObs D
  have hle : ballO (0 : ℂ) r ≤ ballO (0 : ℂ) 1 := ballO_le_ballO hr1 0
  have hcm := aemeasurable_coneField D hγ
  have hcmD : AEMeasurable (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hcm
  have hcmR : AEMeasurable (fun ω => restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hcm
  have hconeR : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))))
      (wpAux hIG₀ U ηL) P :=
    (indepFun_coneField_igObs D hγ).comp (measurable_restrictTo _) measurable_id
  have hFm : Measurable fun g : DistC => restrictTo (ballO (0 : ℂ) r) (addLogSing γ g) :=
    (measurable_restrictTo _).comp (measurable_addLogSing γ)
  have hFhm : Measurable fun ω => restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω)) :=
    hFm.comp hh.1.measurable
  have hfieldR : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω)))
      (wpAux hIG₀ U ηL) P :=
    (GMSCase1.indepFun_wpField_wpAux D).comp hFm measurable_id
  rw [hconeR.map_prod_eq_prod_map_map hcmR hYa, hfieldR.map_prod_eq_prod_map_map hFhm.aemeasurable hYa]
  congr 1
  -- the cone's law on `B_r(0)` from its law on `𝔻`
  have eC : (fun ω => restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =
      resSub (ballO (0 : ℂ) r) (ballO (0 : ℂ) 1) ∘ fun ω => restrictTo (ballO (0 : ℂ) 1)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) :=
    funext fun ω => restrictTo_eq_resSub hle _
  have eF : (fun ω => restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω))) =
      resSub (ballO (0 : ℂ) r) (ballO (0 : ℂ) 1) ∘
        fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (wpField X₀ ω)) :=
    funext fun ω => restrictTo_eq_resSub hle _
  have hFDm : Measurable fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (wpField X₀ ω)) :=
    ((measurable_restrictTo _).comp (measurable_addLogSing γ)).comp hh.1.measurable
  rw [eC, eF, ← AEMeasurable.map_map_of_aemeasurable
      (measurable_resSub _ _).aemeasurable hcmD,
    ← Measure.map_map (measurable_resSub _ _) hFDm,
    map_restrict_coneField hγ D.gff D.bm_B D.bm_B' D.indep_cone hh]

/-- **Cases 3–4, fixed root** (route (c)): for `0 < r` and `‖z‖ + r ≤ 1`, the translated Case 2
field `h₀(· + z) − γ log|·|` on `B_r(0)`, jointly with the IG data re-rooted at `z`, has the law of
The γ-cone field on `B_r(0)` jointly with the IG data. -/
theorem map_shiftedCase2_eq_cone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) :
    P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ ω) z),
        igTransformS (2 * Real.pi * igChi γ) 1 z (wpAux hIG₀ U ηL ω))) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), wpAux hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hr1 : r ≤ 1 := by linarith [norm_nonneg z]
  rw [map_restrict_ball_coneField D hγ hr1]
  set ρ := 2 * Real.pi * igChi γ with hρ
  set h : Ω → DistC := wpField X₀ with hdef
  have hh : IsNormalizedWPGFF h P := GMSCase1.isNormalizedWPGFF_wpField D
  set Y := wpAux hIG₀ U ηL with hYdef
  have hYa : AEMeasurable Y P := aemeasurable_igObs D
  set Y' := hYa.mk Y with hY'def
  have hY'm : Measurable Y' := hYa.measurable_mk
  have hYY' : Y =ᵐ[P] Y' := hYa.ae_eq_mk
  have hτ : Measurable fun q : ℂ × AuxData => igTransformS ρ 1 q.1 q.2 :=
    measurable_igTransformS ρ 1
  have hind' : IndepFun h Y' P := (GMSCase1.indepFun_wpField_wpAux D).congr (ae_eq_refl _) hYY'
  have hlaw' : P.map (fun ω => igTransformS ρ 1 z (Y' ω)) = P.map Y' := by
    have e1 : P.map (fun ω => igTransformS ρ 1 z (Y' ω)) =
        P.map (fun ω => igTransformS ρ 1 z (Y ω)) :=
      Measure.map_congr (by filter_upwards [hYY'] with ω hω; rw [hω])
    rw [e1]
    exact (map_igTransformS_igObs D one_pos z).trans (Measure.map_congr hYY')
  have hpair := map_restrict_affineComp_one_pair hh hr hY'm hτ hind' hz hlaw'
  set G : DistOn (ballO (0 : ℂ) r) × AuxData → DistOn (ballO (0 : ℂ) r) × AuxData :=
    Prod.map (fun T => T + restrictTo (ballO (0 : ℂ) r) (MoTPort.ofFunC (logSing γ))) id
    with hGdef
  have hGm : Measurable G := by
    refine Measurable.prodMap ?_ measurable_id
    refine measurable_distOn_iff.2 fun φ => ?_
    exact (measurable_distOn_apply φ).add measurable_const
  have hm1 : Measurable fun ω =>
      (restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)), igTransformS ρ 1 z (Y' ω)) :=
    ((measurable_restrict_affineComp_one r z).comp hh.1.measurable).prodMk
      ((measurable_transform_right hτ z).comp hY'm)
  have hm2 : Measurable fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y' ω) :=
    ((measurable_restrictTo _).comp hh.1.measurable).prodMk hY'm
  calc P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (h ω) z),
          igTransformS ρ 1 z (Y ω)))
      = P.map (G ∘ fun ω =>
          (restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)), igTransformS ρ 1 z (Y' ω))) := by
        refine Measure.map_congr ?_
        filter_upwards [hYY'] with ω hω
        simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, shiftedCase2Field,
          restrictTo_addLogSing_on, hω]
    _ = P.map (G ∘ fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y' ω)) := by
        rw [← Measure.map_map hGm hm1, hpair, Measure.map_map hGm hm2]
    _ = P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (addLogSing γ (h ω)), Y ω)) := by
        refine Measure.map_congr ?_
        filter_upwards [hYY'] with ω hω
        simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, restrictTo_addLogSing_on, hω]

end Coupling

end MatedCRTHarmonic.GMSCase
