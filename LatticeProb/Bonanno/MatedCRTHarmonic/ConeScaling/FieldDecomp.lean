/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.FieldDecomp at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.LastLevel
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3B
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# The rescaled cone field in lateral/radial coordinates

DMS Def 4.10 writes the circle-average embedding of a
quantum cone as `h = h^{lat} + A_{−log|·|}`; Prop 4.13(i) re-centres it. With `R = R_b = e^{L}`, `L = L_y(A)` and `y = γ⁻¹ log b`,

  `h_b = h(R ·) + Q log R − y = h^{lat}(R ·) + (radShift Q y A)_{−log|·|}`

(`coneRescaleField_fieldOf`). Here `fieldOf l w = l + w(−log|·|)` (`CellScaling.ofFunC`), and the radial
summand transforms by the change of variables `x = R z` (`affineComp_ofFunC`, using the local
integrability of `z ↦ f(R z)`, `locallyIntegrable_comp_smul`) and `ofFunC f + c = ofFunC (f + c)`
(`addConst_ofFunC`); the two radial functions agree off `0` (`ofFunC` only sees the a.e. class).
Identification with the cell model's field and scale: `coneFieldOf_eq_fieldOf`,
`coneScale_eq_exp_lastLevel`. The coordinate identities are proved directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace MatedCRTHarmonic.ConeScaling

open LQGMetric MatedCRTHarmonic.CellScaling

/-- The radial function `z ↦ w(−log|z|)` of a path. -/
def radialOf (w : C(ℝ, ℝ)) (z : ℂ) : ℝ := w (-Real.log ‖z‖)

/-- The field with lateral part `l` and radial path `w`: `l + w(−log|·|)` (DMS Def 4.10). -/
def fieldOf (l : DistC) (w : C(ℝ, ℝ)) : DistC := l + ofFunC (radialOf w)

theorem measurable_radialOf_uncurry : Measurable fun p : C(ℝ, ℝ) × ℂ => radialOf p.1 p.2 := by
  have h : Continuous fun p : C(ℝ, ℝ) × ℝ => p.1 p.2 := continuous_eval
  exact h.measurable.comp (measurable_fst.prodMk
    ((Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg))

theorem measurable_fieldOf : Measurable fun p : DistC × C(ℝ, ℝ) => fieldOf p.1 p.2 := by
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  have hF : Measurable fun q : (DistC × C(ℝ, ℝ)) × ℂ => radialOf q.1.2 q.2 :=
    measurable_radialOf_uncurry.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact ((GFFInv.measurable_pair φ).comp measurable_fst).add
    (MoTPort.ConeMeas2.measurable_ofFunC_apply (F := fun p : DistC × C(ℝ, ℝ) => radialOf p.2) hF φ)

/-! ### Dilations and constants on `ofFunC` -/

/-- Local integrability is preserved by a nonzero dilation of `ℂ`. -/
theorem locallyIntegrable_comp_smul {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) {R : ℝ}
    (hR : R ≠ 0) : LocallyIntegrable (fun z => f (R • z)) volume := by
  rw [locallyIntegrable_iff] at hf ⊢
  intro K hK
  set K' : Set ℂ := (fun z : ℂ => R • z) '' K
  have hK' : IsCompact K' := hK.image (continuous_const_smul R)
  have h1 : Integrable (K'.indicator f) volume :=
    (integrable_indicator_iff hK'.measurableSet).2 (hf K' hK')
  have h2 : Integrable (fun z => K'.indicator f (R • z)) volume := h1.comp_smul hR
  have hpre : MeasurableSet ((fun z : ℂ => R • z) ⁻¹' K') :=
    hK'.isClosed.measurableSet.preimage (continuous_const_smul R).measurable
  have h3 : IntegrableOn (fun z => f (R • z)) ((fun z : ℂ => R • z) ⁻¹' K') volume := by
    rw [← integrable_indicator_iff hpre]
    have e : ((fun z : ℂ => R • z) ⁻¹' K').indicator (fun z => f (R • z)) =
        fun z => K'.indicator f (R • z) := by
      funext z
      by_cases hz : R • z ∈ K'
      · rw [indicator_of_mem (show z ∈ (fun z : ℂ => R • z) ⁻¹' K' from hz),
          indicator_of_mem hz]
      · rw [indicator_of_notMem (show z ∉ (fun z : ℂ => R • z) ⁻¹' K' from hz),
          indicator_of_notMem hz]
    rw [e]; exact h2
  exact h3.mono_set (subset_preimage_image _ _)

lemma ofFunC_apply_of_li {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (φ : TestC) :
    ofFunC f φ = ∫ x, φ x * f x := by
  rw [ofFunC, Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  rfl

/-- **Dilation of a function distribution**: `(ofFunC f)(R ·) = ofFunC (f(R ·))` for `R > 0`
(change of variables `x = R z`, `dx = R² dz`). -/
theorem affineComp_ofFunC {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) {R : ℝ} (hR : 0 < R) :
    affineComp R 0 (ofFunC f) = ofFunC (fun z => f (R • z)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.affineComp_apply, ofFunC_apply_of_li hf,
    ofFunC_apply_of_li (locallyIntegrable_comp_smul hf hR.ne')]
  have hcv := GFFInv.integral_smul_add (fun x => testAffinePull R 0 φ x * f x) hR 0
  simp only [add_zero] at hcv
  rw [← hcv]
  congr 1
  funext v
  rw [testAffinePull_apply _ _ hR.ne', sub_zero, Complex.real_smul,
    mul_div_cancel_left₀ _ (by exact_mod_cast hR.ne')]

/-- **Adding a constant to a function distribution**: `ofFunC f + c = ofFunC (f + c)`. -/
theorem addConst_ofFunC {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (c : ℝ) :
    addConst (ofFunC f) c = ofFunC (fun z => f z + c) := by
  have e : (fun z => f z + c) = f + fun _ => c := rfl
  simp only [e, ofFunC]
  rw [Distribution.ofFun_add (hf.locallyIntegrableOn _)
    ((locallyIntegrable_const c).locallyIntegrableOn _)]
  rfl

/-- The path `t ↦ w(t − a) + c`. -/
def shiftAdd (w : C(ℝ, ℝ)) (a c : ℝ) : C(ℝ, ℝ) := ⟨fun t => w (t - a) + c, by fun_prop⟩

/-- The radial summand under `h ↦ h(R ·) + c`: its path is shifted by `log R` and raised by `c`. -/
theorem addConst_affineComp_ofFunC_radialOf {w : C(ℝ, ℝ)}
    (hw : LocallyIntegrable (radialOf w) volume) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    addConst (affineComp R 0 (ofFunC (radialOf w))) c =
      ofFunC (radialOf (shiftAdd w (Real.log R) c)) := by
  rw [affineComp_ofFunC hw hR, addConst_ofFunC (locallyIntegrable_comp_smul hw hR.ne') c]
  refine MoTPort.ConeArea3.ofFunC_congr_ae ?_
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hne] with z hz
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  simp only [radialOf, shiftAdd, ContinuousMap.coe_mk, norm_smul, Real.norm_eq_abs,
    abs_of_pos hR, Real.log_mul hR.ne' hz']
  ring_nf

/-! ### The re-centred cone field -/

/-- `h(R ·) + Q log R − γ⁻¹ log b` splits into the dilated lateral part and the radial summand. -/
theorem coneRescaleField_fieldOf_split (γ R b₀ : ℝ) (l : DistC) (w : C(ℝ, ℝ)) :
    coneRescaleField γ R b₀ (fieldOf l w) =
      affineComp R 0 l + addConst (affineComp R 0 (ofFunC (radialOf w)))
        (lqgQ γ * Real.log R - γ⁻¹ * Real.log b₀) := by
  rw [coneRescaleField, fieldOf, LQGMetric.GM.affineComp_add]
  simp only [LQGMetric.addConst, LQGMetric.addFun, add_assoc]

/-- **The re-centred cone field**: for `R = exp (L_y(w))`, `y = γ⁻¹ log b₀`,
`h_b = fieldOf (l(R ·)) (radShift Q y w)` whenever `h = fieldOf l w` with `w(−log|·|)` locally
integrable. -/
theorem coneRescaleField_fieldOf (γ b₀ : ℝ) (l : DistC) {w : C(ℝ, ℝ)}
    (hw : LocallyIntegrable (radialOf w) volume) :
    coneRescaleField γ (Real.exp (lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀) w)) b₀ (fieldOf l w) =
      fieldOf (affineComp (Real.exp (lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀) w)) 0 l)
        (radShift (lqgQ γ) (γ⁻¹ * Real.log b₀) w) := by
  rw [coneRescaleField_fieldOf_split, addConst_affineComp_ofFunC_radialOf hw (Real.exp_pos _),
    fieldOf]
  congr 3
  ext t
  simp only [shiftAdd, ContinuousMap.coe_mk, Real.log_exp, radShift_apply]
  ring

/-- The cell model's cone field in lateral/radial coordinates. -/
theorem coneFieldOf_eq_fieldOf (γ : ℝ) (X : DistC) {b b' : NNReal → ℝ} {w : C(ℝ, ℝ)}
    (hw : ∀ t, w t = coneRadial γ γ b b' t) :
    coneFieldOf γ X b b' = fieldOf (lateralPart X) w := by
  unfold coneFieldOf coneField fieldOf
  congr 2
  funext z
  simp only [radialOf, hw]

/-- The cone scale `R_b` is `exp (L_y)` of the radial path, `y = γ⁻¹ log b`. -/
theorem coneScale_eq_exp_lastLevel (γ b₀ : ℝ) {b b' : NNReal → ℝ} {w : C(ℝ, ℝ)}
    (hw : ∀ t, w t = coneRadial γ γ b b' t) :
    coneScale γ γ b b' b₀ = Real.exp (lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀) w) := by
  unfold coneScale lastLevel coneLogRadial
  simp only [hw]

end MatedCRTHarmonic.ConeScaling
