/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePushL2 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable); eLpNorm_eq_lintegral_rpow_enorm_toReal takes the measurability argument. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePush

/-!
# The conformal pushforward operator on `L²(ℝ × ℂ)` (task P2-DDDFL6)

For `F : U → V = F(U)` conformal, DDDF (arXiv:1904.08021, `tightness.tex` l. 541–543) set
`∫ ω(y',t') W̃(dy',dt') = ∫ ω(F(y), t|F'(y)|²) |F'(y)|² W(dy,dt)`. The kernel on the right is

  `(T ω)(t, y) := 1_{(0,∞)×U}(t, y) |F'(y)|² ω(t|F'(y)|², F(y))`,

and by the change of variables `lintegral_pushMap` (Jacobian `|F'|⁴`), `‖T ω‖² = ‖ω 1_{(0,∞)×V}‖²`
("both sides have variance `‖ω‖²`", l. 543). Here `T` is built as a linear map
`pushLM : WNSpace →ₗ[ℝ] WNSpace`; well-definedness on a.e.-classes uses that the space-time map
does not charge null sets (`comp_pushMap_ae`, again from the change of variables).
`cutLM A` is the restriction `ω ↦ ω 1_A` (used for the independent part of `W̃` outside `V`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace WNPush

open WhiteNoise

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The image `F(U)` is measurable (mathlib `measurable_image_of_fderivWithin`). -/
lemma measurableSet_image (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) :
    MeasurableSet (F '' U) :=
  measurable_image_of_fderivWithin hU.measurableSet
    (fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt
      |>.hasFDerivWithinAt) hinj

lemma aemeasurable_comp_pushMap (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {β : Type*}
    [MeasurableSpace β] {g : ℝ × ℂ → β} (hg : Measurable g) :
    AEMeasurable (fun p => g (pushMap F p)) (volume.restrict (Ioi 0 ×ˢ U)) := by
  have hFm : AEMeasurable F (volume.restrict U) := hF.continuousOn.aemeasurable hU.measurableSet
  have hn : Measurable fun p : ℝ × ℂ => ‖deriv F p.2‖ :=
    ((measurable_deriv F).comp measurable_snd).norm
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hg.comp_aemeasurable ((measurable_fst.mul (hn.pow_const 2)).aemeasurable.prodMk
    (hFm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))

/-- The space-time map does not charge null sets: a.e.-equal functions have a.e.-equal
compositions on `(0,∞) × U`. -/
lemma comp_pushMap_ae (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (hd : ∀ y ∈ U, deriv F y ≠ 0) {β : Type*} {u v : ℝ × ℂ → β} (huv : u =ᵐ[volume] v) :
    (fun p => u (pushMap F p)) =ᵐ[volume.restrict (Ioi 0 ×ˢ U)] fun p => v (pushMap F p) := by
  set N := toMeasurable volume {q | u q ≠ v q}
  have hN : volume N = 0 := by rw [measure_toMeasurable]; exact huv
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have h1 := lintegral_pushMap hU hF hinj hd (g := N.indicator 1) (measurable_one.indicator hNm)
  rw [lintegral_indicator_one hNm, Measure.restrict_apply hNm,
    measure_mono_null inter_subset_left hN] at h1
  have hm : AEMeasurable (fun p : ℝ × ℂ => ENNReal.ofReal (‖deriv F p.2‖ ^ 4) *
      N.indicator 1 (pushMap F p)) (volume.restrict (Ioi 0 ×ˢ U)) :=
    ((((measurable_deriv F).comp measurable_snd).norm.pow_const 4).ennreal_ofReal.aemeasurable).mul
      (aemeasurable_comp_pushMap hU hF (measurable_one.indicator hNm))
  have h2 := (lintegral_eq_zero_iff' hm).1 h1
  filter_upwards [h2, ae_restrict_mem (measurableSet_Ioi.prod hU.measurableSet)] with p hp hpD
  have hpos : 0 < ‖deriv F p.2‖ ^ 4 := pow_pos (norm_pos_iff.2 (hd p.2 hpD.2)) 4
  have hnot : pushMap F p ∉ N := by
    intro hmem
    simp [indicator_of_mem hmem] at hp
    exact hd p.2 hpD.2 hp
  by_contra hne
  exact hnot (subset_toMeasurable _ _ hne)

variable (F U) in
/-- The kernel transform `(T u)(t,y) = 1_{(0,∞)×U} |F'(y)|² u(t|F'(y)|², F(y))` on functions. -/
def pushFunOf (u : ℝ × ℂ → ℝ) : ℝ × ℂ → ℝ :=
  (Ioi 0 ×ˢ U).indicator fun p => ‖deriv F p.2‖ ^ 2 * u (pushMap F p)

lemma pushFunOf_add (u v : ℝ × ℂ → ℝ) :
    pushFunOf F U (u + v) = pushFunOf F U u + pushFunOf F U v := by
  funext p
  by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ U <;> simp [pushFunOf, hp, mul_add]

lemma pushFunOf_smul (c : ℝ) (u : ℝ × ℂ → ℝ) :
    pushFunOf F U (c • u) = c • pushFunOf F U u := by
  funext p
  by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ U <;> simp [pushFunOf, hp]
  ring

lemma pushFunOf_congr (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (hd : ∀ y ∈ U, deriv F y ≠ 0) {u v : ℝ × ℂ → ℝ} (huv : u =ᵐ[volume] v) :
    pushFunOf F U u =ᵐ[volume] pushFunOf F U v := by
  have h := comp_pushMap_ae hU hF hinj hd huv
  have hD : MeasurableSet (Ioi (0 : ℝ) ×ˢ U) := measurableSet_Ioi.prod hU.measurableSet
  filter_upwards [(ae_restrict_iff' hD).1 h] with p hp
  by_cases hpD : p ∈ Ioi (0 : ℝ) ×ˢ U
  · simp [pushFunOf, indicator_of_mem hpD, hp hpD]
  · simp [pushFunOf, indicator_of_notMem hpD]

/-- `∫ (T u)² = ∫_{(0,∞)×F(U)} u²` (in `ℝ≥0∞` form). -/
lemma lintegral_pushFunOf (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (hd : ∀ y ∈ U, deriv F y ≠ 0) {u : ℝ × ℂ → ℝ} (hu : Measurable u) :
    ∫⁻ p, ‖pushFunOf F U u p‖ₑ ^ (2 : ℝ) = ∫⁻ q in Ioi 0 ×ˢ (F '' U), ‖u q‖ₑ ^ (2 : ℝ) := by
  have hD : MeasurableSet (Ioi (0 : ℝ) ×ˢ U) := measurableSet_Ioi.prod hU.measurableSet
  rw [← lintegral_pushMap hU hF hinj hd (hu.enorm.pow_const (2 : ℝ)),
    ← lintegral_indicator hD]
  congr 1; funext p
  by_cases hpD : p ∈ Ioi (0 : ℝ) ×ˢ U
  · simp only [pushFunOf, indicator_of_mem hpD]
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      Real.enorm_of_nonneg (by positivity)]
    simp only [ENNReal.rpow_two]
    rw [← ENNReal.ofReal_pow (by positivity)]
    ring_nf
  · simp [pushFunOf, indicator_of_notMem hpD]

/-- `‖f‖² = ∫ |f|²` for `f ∈ L²(ℝ × ℂ)`, in `ℝ≥0∞` form. -/
lemma norm_sq_eq_lintegral (f : WNSpace) :
    ‖f‖ ^ 2 = (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ)).toReal := by
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable f),
    ENNReal.toReal_ofNat, ← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma lintegral_enorm_sq_lt_top (f : WNSpace) : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) < ∞ := by
  have h := Lp.eLpNorm_lt_top f
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable f),
    ENNReal.toReal_ofNat] at h
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_rpow_of_pos (by norm_num)] at h
  exact lt_irrefl _ h

lemma memLp_pushFunOf (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (hd : ∀ y ∈ U, deriv F y ≠ 0) (g : WNSpace) :
    MemLp (pushFunOf F U ((Lp.aestronglyMeasurable g).mk g)) 2 volume := by
  set u := (Lp.aestronglyMeasurable g).mk g
  have hum : Measurable u := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable
  have hD : MeasurableSet (Ioi (0 : ℝ) ×ˢ U) := measurableSet_Ioi.prod hU.measurableSet
  have hmeas : AEStronglyMeasurable (pushFunOf F U u) volume := by
    rw [pushFunOf, aestronglyMeasurable_indicator_iff hD]
    exact ((((measurable_deriv F).comp measurable_snd).norm.pow_const 2).aemeasurable.mul
      (aemeasurable_comp_pushMap hU hF hum)).aestronglyMeasurable
  refine memLp_iff.2 ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hmeas, ENNReal.toReal_ofNat,
    lintegral_pushFunOf hU hF hinj hd hum]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
  rw [lintegral_congr_ae (g := fun p => ‖g p‖ₑ ^ (2 : ℝ))]
  · exact lintegral_enorm_sq_lt_top g
  · filter_upwards [(Lp.aestronglyMeasurable g).ae_eq_mk] with p hp
    rw [hp]

variable (F U) in
/-- The pushforward operator `T` on `L²(ℝ × ℂ)` (junk `0` unless the conformal hypotheses
hold). -/
def pushL2 (g : WNSpace) : WNSpace := by
  classical
  exact if h : IsOpen U ∧ DifferentiableOn ℂ F U ∧ InjOn F U ∧ ∀ y ∈ U, deriv F y ≠ 0 then
    (memLp_pushFunOf h.1 h.2.1 h.2.2.1 h.2.2.2 g).toLp _ else 0

lemma coeFn_pushL2 (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (hd : ∀ y ∈ U, deriv F y ≠ 0) (g : WNSpace) :
    (pushL2 F U g : ℝ × ℂ → ℝ) =ᵐ[volume] pushFunOf F U g := by
  have h : IsOpen U ∧ DifferentiableOn ℂ F U ∧ InjOn F U ∧ ∀ y ∈ U, deriv F y ≠ 0 :=
    ⟨hU, hF, hinj, hd⟩
  rw [pushL2, dite_cond_eq_true (eq_true h)]
  exact (MemLp.coeFn_toLp _).trans
    (pushFunOf_congr hU hF hinj hd (Lp.aestronglyMeasurable g).ae_eq_mk.symm)

/-- The standing hypotheses on `F` and `U` (DDDF l. 539: `F : U → V` conformal; `U` open,
`F` holomorphic and injective with non-vanishing derivative). -/
structure ConfHyp (F : ℂ → ℂ) (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  diff : DifferentiableOn ℂ F U
  inj : InjOn F U
  deriv_ne : ∀ y ∈ U, deriv F y ≠ 0

namespace ConfHyp

variable (h : ConfHyp F U)
include h

lemma pushL2_add (f g : WNSpace) : pushL2 F U (f + g) = pushL2 F U f + pushL2 F U g := by
  apply Lp.ext
  filter_upwards [coeFn_pushL2 h.1 h.2 h.3 h.4 (f + g), coeFn_pushL2 h.1 h.2 h.3 h.4 f,
    coeFn_pushL2 h.1 h.2 h.3 h.4 g, Lp.coeFn_add (pushL2 F U f) (pushL2 F U g),
    pushFunOf_congr h.1 h.2 h.3 h.4 (Lp.coeFn_add f g)] with p h1 h2 h3 h4 h5
  rw [h4, h1, h5, pushFunOf_add, Pi.add_apply, Pi.add_apply, h2, h3]

lemma pushL2_smul (c : ℝ) (g : WNSpace) : pushL2 F U (c • g) = c • pushL2 F U g := by
  apply Lp.ext
  filter_upwards [coeFn_pushL2 h.1 h.2 h.3 h.4 (c • g), coeFn_pushL2 h.1 h.2 h.3 h.4 g,
    Lp.coeFn_smul c (pushL2 F U g),
    pushFunOf_congr h.1 h.2 h.3 h.4 (Lp.coeFn_smul c g)] with p h1 h2 h4 h5
  rw [h4, h1, h5, pushFunOf_smul, Pi.smul_apply, Pi.smul_apply, h2]

/-- The pushforward operator `T` as a linear map. -/
def pushLM : WNSpace →ₗ[ℝ] WNSpace where
  toFun := pushL2 F U
  map_add' := h.pushL2_add
  map_smul' := h.pushL2_smul

lemma pushLM_apply (g : WNSpace) : h.pushLM g = pushL2 F U g := rfl

/-- **Variance identity** (DDDF l. 543): `‖T g‖² = ∫_{(0,∞)×F(U)} g²`. -/
lemma norm_sq_pushL2 (g : WNSpace) :
    ‖pushL2 F U g‖ ^ 2 = (∫⁻ q in Ioi 0 ×ˢ (F '' U), ‖g q‖ₑ ^ (2 : ℝ)).toReal := by
  set u := (Lp.aestronglyMeasurable g).mk g
  have hum : Measurable u := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable
  have hgu : (g : ℝ × ℂ → ℝ) =ᵐ[volume] u := (Lp.aestronglyMeasurable g).ae_eq_mk
  rw [norm_sq_eq_lintegral]
  congr 1
  rw [lintegral_congr_ae (g := fun p => ‖pushFunOf F U u p‖ₑ ^ (2 : ℝ)),
    lintegral_pushFunOf h.1 h.2 h.3 h.4 hum]
  · refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hgu] with q hq
    rw [hq]
  · filter_upwards [coeFn_pushL2 h.1 h.2 h.3 h.4 g, pushFunOf_congr h.1 h.2 h.3 h.4 hgu]
      with p h1 h2
    rw [h1, h2]

end ConfHyp

/-- The restriction `g ↦ g 1_A` on `L²(ℝ × ℂ)`. -/
def cutL2 {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) : WNSpace :=
  ((Lp.memLp g).indicator hA).toLp _

lemma coeFn_cutL2 {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) :
    (cutL2 hA g : ℝ × ℂ → ℝ) =ᵐ[volume] A.indicator g :=
  MemLp.coeFn_toLp _

/-- The restriction as a linear map. -/
def cutLM {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) : WNSpace →ₗ[ℝ] WNSpace where
  toFun := cutL2 hA
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_cutL2 hA (f + g), coeFn_cutL2 hA f, coeFn_cutL2 hA g,
      Lp.coeFn_add (cutL2 hA f) (cutL2 hA g), Lp.coeFn_add f g] with p h1 h2 h3 h4 h5
    rw [h4, h1, Pi.add_apply, h2, h3]
    by_cases hp : p ∈ A
    · simpa [hp] using h5
    · simp [hp]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [coeFn_cutL2 hA (c • g), coeFn_cutL2 hA g,
      Lp.coeFn_smul c (cutL2 hA g), Lp.coeFn_smul c g] with p h1 h2 h4 h5
    rw [RingHom.id_apply, h4, h1, Pi.smul_apply, h2]
    by_cases hp : p ∈ A
    · simpa [hp] using h5
    · simp [hp]

lemma cutLM_apply {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) :
    cutLM hA g = cutL2 hA g := rfl

lemma norm_sq_cutL2 {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) :
    ‖cutL2 hA g‖ ^ 2 = (∫⁻ q in A, ‖g q‖ₑ ^ (2 : ℝ)).toReal := by
  rw [norm_sq_eq_lintegral, ← lintegral_indicator hA]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [coeFn_cutL2 hA g] with p hp
  by_cases hpA : p ∈ A <;> simp [hp, hpA]

/-- Pythagoras for a measurable set and its complement. -/
lemma norm_sq_split {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) :
    ‖g‖ ^ 2 = (∫⁻ q in A, ‖g q‖ₑ ^ (2 : ℝ)).toReal + (∫⁻ q in Aᶜ, ‖g q‖ₑ ^ (2 : ℝ)).toReal := by
  have hfin := lintegral_enorm_sq_lt_top g
  rw [← ENNReal.toReal_add, lintegral_add_compl _ hA, norm_sq_eq_lintegral]
  · exact ne_top_of_le_ne_top hfin.ne (setLIntegral_le_lintegral _ _)
  · exact ne_top_of_le_ne_top hfin.ne (setLIntegral_le_lintegral _ _)

end WNPush
end LQGMetric
