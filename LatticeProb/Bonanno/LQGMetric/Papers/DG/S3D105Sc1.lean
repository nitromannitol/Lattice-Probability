/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc1 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_eq_lintegral_rpow_enorm_toReal takes the measurability hypotheses, supplied after the rewrite; MemLp is now the bound eLpNorm < ∞. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePushL2
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatScale
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent2Circ
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L3
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# DG scale invariance of `ĥ`, part 1: the white-noise scaling isometry (task P2-DG105c, D105 N5)

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), DG:1010 ("by the basic properties
of `ĥ`", the field `(ĥ − ĥ_δ)(δ·+b)` has the law of `ĥ`), realized pathwise as in DEC-105 §1
item 3: for `δ > 0`, `b ∈ ℂ` the space-time map `φ(s,w) = (δ⁻²s, δ⁻¹(w − b))` pushes Lebesgue
measure on `ℝ × ℂ` to `δ⁴ ·` Lebesgue measure (`map_scMap`), so

  `U_{δ,b} f (s,w) := δ⁻² f(δ⁻²s, δ⁻¹(w − b))`

is a linear isometry of `WNSpace = L²(ℝ × ℂ)` (`wnScale`), and `W ∘ U` is again a white noise
(`isWhiteNoise_comp`; the covariance `‖Σ cᵢ U fᵢ‖² = ‖Σ cᵢ fᵢ‖²` is preserved). This is the
standard scaling of white noise (`W(dw, ds)` scales by `δ²` under `s = δ²s'`, `w = δw' + b`);
the Lean construction follows the pattern of `WNPush.pushL2` (Field/WhiteNoisePushL2), with the
change of variables from mathlib (`Real.map_volume_mul_left`, `Measure.map_addHaar_smul`).
Own elementary argument (DV-D105-2).

Section `Killed`: Brownian scaling of the killed heat kernel `p_{δA+b}(δ²t; δz+b, δw+b) =
δ⁻² p_A(t; z, w)` (`killedHeat_affineC`, from `KilledHeat.bridgeStay_scale` and translation
invariance `bridgeStay_add`), the kernel covariance `U_{δ,b}(K^{A,I}_μ) = K^{δA+b, δ²I}_{(δ·+b)_*μ}`
(`scFun_measKer`) and the same for `ĥ^tr` (`scFun_trMeasKer`: ball radius `δ/10`, times `≤ δ²`;
DG:953 note that `ĥ^tr` is only translation invariant), and `dgHU_wnScale`:
`h^𝕍[W ∘ U](σ_{z,r}) = h^{δ𝕍+b}[W](σ_{δz+b,δr})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise

namespace LQGMetric
namespace DG

open WhiteNoise

/-- the space-time scaling map `φ(s, w) = (δ⁻² s, δ⁻¹ (w − b))` -/
def scMap (δ : ℝ) (b : ℂ) (p : ℝ × ℂ) : ℝ × ℂ := ((δ ^ 2)⁻¹ * p.1, (δ⁻¹ : ℝ) • (p.2 - b))

lemma measurable_scMap (δ : ℝ) (b : ℂ) : Measurable (scMap δ b) := by
  unfold scMap; fun_prop

/-- **Change of variables**: `φ_* Leb = δ⁴ Leb` on `ℝ × ℂ`. -/
lemma map_scMap {δ : ℝ} (hδ : 0 < δ) (b : ℂ) :
    Measure.map (scMap δ b) volume = ENNReal.ofReal (δ ^ 4) • (volume : Measure (ℝ × ℂ)) := by
  have e : scMap δ b = Prod.map (fun s : ℝ => (δ ^ 2)⁻¹ * s)
      ((fun w : ℂ => (δ⁻¹ : ℝ) • w) ∘ fun w => w + -b) := by
    funext p; simp only [scMap, Prod.map, Function.comp_apply, sub_eq_add_neg]
  have h1 : Measure.map (fun s : ℝ => (δ ^ 2)⁻¹ * s) volume =
      ENNReal.ofReal (δ ^ 2) • (volume : Measure ℝ) := by
    rw [Real.map_volume_mul_left (by positivity), inv_inv, abs_of_pos (by positivity)]
  have h2 : Measure.map ((fun w : ℂ => (δ⁻¹ : ℝ) • w) ∘ fun w => w + -b) volume =
      ENNReal.ofReal (δ ^ 2) • (volume : Measure ℂ) := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
      Measure.map_addHaar_smul _ (by positivity : (δ⁻¹ : ℝ) ≠ 0), Complex.finrank_real_complex,
      inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [e, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h1, h2,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

lemma lintegral_comp_scMap {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {g : ℝ × ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g (scMap δ b p) = ENNReal.ofReal (δ ^ 4) * ∫⁻ p, g p := by
  rw [← lintegral_map hg (measurable_scMap δ b), map_scMap hδ b, lintegral_smul_measure]
  rfl

lemma qmp_scMap {δ : ℝ} (hδ : 0 < δ) (b : ℂ) :
    Measure.QuasiMeasurePreserving (scMap δ b) volume volume :=
  ⟨measurable_scMap δ b, by rw [map_scMap hδ b]; exact Measure.smul_absolutelyContinuous⟩

/-- `U_{δ,b}` on functions: `(U u)(s, w) = δ⁻² u(δ⁻² s, δ⁻¹ (w − b))` -/
def scFun (δ : ℝ) (b : ℂ) (u : ℝ × ℂ → ℝ) (p : ℝ × ℂ) : ℝ := (δ ^ 2)⁻¹ * u (scMap δ b p)

lemma scFun_congr {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {u v : ℝ × ℂ → ℝ} (huv : u =ᵐ[volume] v) :
    scFun δ b u =ᵐ[volume] scFun δ b v := by
  filter_upwards [(qmp_scMap hδ b).ae_eq_comp huv] with p hp
  simp only [scFun]
  rw [show u (scMap δ b p) = v (scMap δ b p) from hp]

lemma lintegral_scFun {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {u : ℝ × ℂ → ℝ} (hu : Measurable u) :
    ∫⁻ p, ‖scFun δ b u p‖ₑ ^ (2 : ℝ) = ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) := by
  have e : ∀ p, ‖scFun δ b u p‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((δ ^ 4)⁻¹) * ‖u (scMap δ b p)‖ₑ ^ (2 : ℝ) := by
    intro p
    rw [scFun, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      Real.enorm_of_nonneg (by positivity)]
    congr 1
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    congr 1; ring
  simp_rw [e]
  rw [lintegral_const_mul _ (show Measurable fun p => ‖u (scMap δ b p)‖ₑ ^ (2 : ℝ) from
      (hu.comp (measurable_scMap δ b)).enorm.pow_const (2 : ℝ)),
    lintegral_comp_scMap hδ b (hu.enorm.pow_const _), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_mul]

lemma eLpNorm_scFun {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {u : ℝ × ℂ → ℝ}
    (hu : AEStronglyMeasurable u volume) :
    eLpNorm (scFun δ b u) 2 volume = eLpNorm u 2 volume := by
  have hv := hu.ae_eq_mk
  rw [eLpNorm_congr_ae (scFun_congr hδ b hv), eLpNorm_congr_ae hv,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    lintegral_scFun hδ b hu.stronglyMeasurable_mk.measurable]
  all_goals first
    | exact hu.stronglyMeasurable_mk.aestronglyMeasurable
    | exact (hu.stronglyMeasurable_mk.aestronglyMeasurable.comp_quasiMeasurePreserving (qmp_scMap hδ b)).const_mul _

lemma memLp_scFun {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {u : ℝ × ℂ → ℝ} (hu : MemLp u 2 volume) :
    MemLp (scFun δ b u) 2 volume := by
  rw [memLp_iff, eLpNorm_scFun hδ b hu.aestronglyMeasurable]; exact hu

/-- `U_{δ,b}` on `WNSpace` -/
def wnScaleFun {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (g : WNSpace) : WNSpace :=
  (memLp_scFun hδ b (Lp.memLp g)).toLp _

lemma coeFn_wnScaleFun {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (g : WNSpace) :
    (wnScaleFun hδ b g : ℝ × ℂ → ℝ) =ᵐ[volume] scFun δ b g :=
  MemLp.coeFn_toLp _

lemma wnScaleFun_add {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (f g : WNSpace) :
    wnScaleFun hδ b (f + g) = wnScaleFun hδ b f + wnScaleFun hδ b g := by
  apply Lp.ext
  filter_upwards [coeFn_wnScaleFun hδ b (f + g), coeFn_wnScaleFun hδ b f, coeFn_wnScaleFun hδ b g,
    Lp.coeFn_add (wnScaleFun hδ b f) (wnScaleFun hδ b g),
    scFun_congr hδ b (Lp.coeFn_add f g)] with p h1 h2 h3 h4 h5
  rw [h4, h1, h5, Pi.add_apply, h2, h3]
  simp only [scFun, Pi.add_apply, mul_add]

lemma wnScaleFun_smul {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (c : ℝ) (g : WNSpace) :
    wnScaleFun hδ b (c • g) = c • wnScaleFun hδ b g := by
  apply Lp.ext
  filter_upwards [coeFn_wnScaleFun hδ b (c • g), coeFn_wnScaleFun hδ b g,
    Lp.coeFn_smul c (wnScaleFun hδ b g), scFun_congr hδ b (Lp.coeFn_smul c g)] with p h1 h2 h4 h5
  rw [h4, h1, h5, Pi.smul_apply, h2]
  simp only [scFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The white-noise scaling isometry** `U_{δ,b} f (s,w) = δ⁻² f(δ⁻²s, δ⁻¹(w − b))`. -/
def wnScale {δ : ℝ} (hδ : 0 < δ) (b : ℂ) : WNSpace →ₗᵢ[ℝ] WNSpace where
  toFun := wnScaleFun hδ b
  map_add' := wnScaleFun_add hδ b
  map_smul' := wnScaleFun_smul hδ b
  norm_map' g := by
    show ‖wnScaleFun hδ b g‖ = ‖g‖
    rw [wnScaleFun, Lp.norm_toLp, eLpNorm_scFun hδ b (Lp.aestronglyMeasurable g), Lp.norm_def]

lemma coeFn_wnScale {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (g : WNSpace) :
    (wnScale hδ b g : ℝ × ℂ → ℝ) =ᵐ[volume] scFun δ b g :=
  coeFn_wnScaleFun hδ b g

/-- `U_{δ,b}` on an explicit square-integrable kernel -/
lemma wnScale_toLp {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {u : ℝ × ℂ → ℝ} (hu : MemLp u 2 volume) :
    wnScale hδ b (hu.toLp u) = (memLp_scFun hδ b hu).toLp _ := by
  apply Lp.ext
  filter_upwards [coeFn_wnScale hδ b (hu.toLp u), scFun_congr hδ b hu.coeFn_toLp,
    (memLp_scFun hδ b hu).coeFn_toLp] with p h1 h2 h3
  rw [h1, h2, h3]

/-- the dyadic scaling `δ = 2^{-m}` (DG:1535, D105 N5) -/
def wnScaleDy (m : ℕ) (b : ℂ) : WNSpace →ₗᵢ[ℝ] WNSpace :=
  wnScale (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) m) b

/-- **`W ∘ T` is a white noise** for every linear isometry `T` of `WNSpace`. -/
theorem isWhiteNoise_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (T : WNSpace →ₗᵢ[ℝ] WNSpace) :
    IsWhiteNoise P fun f ω => W (T f) ω := by
  refine ⟨fun f => hW.measurable _, fun {ι} _ f c => ?_⟩
  have h := hW.hasLaw (fun i => T (f i)) c
  have e : ‖∑ i, c i • T (f i)‖ = ‖∑ i, c i • f i‖ := by
    rw [← T.norm_map (∑ i, c i • f i), map_sum]
    simp only [LinearIsometry.map_smul]
  rw [e] at h
  exact h

/-! ### Kernel covariance for the zero-boundary field `h^U` (killed heat kernel) -/

section Killed

open KilledHeat DZZ GMCIdent QuantumZipper

/-- **Brownian scaling of the heat kernel**: `p_{δ²t}(δx+b, δy+b) = δ⁻² p_t(x, y)`. -/
lemma heatKernel_affineC {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (t : ℝ) (x y : ℂ) :
    heatKernel (δ ^ 2 * t) (affineC δ b x) (affineC δ b y) = (δ ^ 2)⁻¹ * heatKernel t x y := by
  have hn : ‖affineC δ b x - affineC δ b y‖ ^ 2 = δ ^ 2 * ‖x - y‖ ^ 2 := by
    rw [← dist_eq_norm, dist_affineC hδ, dist_eq_norm, mul_pow]
  unfold heatKernel
  rw [hn, ← mul_neg, show 2 * (δ ^ 2 * t) = δ ^ 2 * (2 * t) by ring,
    mul_div_mul_left _ _ (by positivity : δ ^ 2 ≠ 0)]
  ring

/-- the image of a circle measure under `y ↦ δy + b` -/
lemma map_affineC_circleUnif (δ : ℝ) (b z : ℂ) (r : ℝ) :
    (circleUnif z r).map (affineC δ b) = circleUnif (affineC δ b z) (δ * r) := by
  unfold circleUnif
  rw [Measure.map_smul, Measure.map_map (continuous_affineC δ b).measurable
    (continuous_circleMap z r).measurable]
  congr 2
  funext θ
  simp only [Function.comp_apply, circleMap, affineC]
  push_cast; ring
  exact (continuous_affineC δ b).aemeasurable

/-- translation invariance of the bridge probability -/
lemma bridgeStay_add (A : Set ℂ) (t : NNReal) (c z w : ℂ) :
    bridgeStay ((· + c) '' A) t (z + c) (w + c) = bridgeStay A t z w := by
  unfold bridgeStay
  congr 2
  ext ω
  simp only [bridgeEvent, Set.mem_ofPred_eq]
  refine forall₂_congr fun s _ => ?_
  have e : bridgePath t (z + c) (w + c) (stdBridge t) s ω =
      bridgePath t z w (stdBridge t) s ω + c := by
    unfold bridgePath; ring
  rw [e, Set.image_add_right, mem_preimage, add_neg_cancel_right]

/-- the affine map `y ↦ δy + b` as a homeomorphism -/
def affineHomeoC {δ : ℝ} (hδ : 0 < δ) (b : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (δ : ℂ) (by exact_mod_cast hδ.ne')).trans (Homeomorph.addRight b)

lemma coe_affineHomeoC {δ : ℝ} (hδ : 0 < δ) (b : ℂ) : ⇑(affineHomeoC hδ b) = affineC δ b := rfl

/-- **Brownian scaling of the killed heat kernel**:
`p_{δA+b}(δ²t; δz+b, δw+b) = δ⁻² p_A(t; z, w)`. -/
theorem killedHeat_affineC {A : Set ℂ} (hA : IsOpen A) {δ : ℝ} (hδ : 0 < δ) (b : ℂ)
    {t : NNReal} (ht : t ≠ 0) (z w : ℂ) :
    killedHeat (affineC δ b '' A) ((δ ^ 2).toNNReal * t) (affineC δ b z) (affineC δ b w) =
      (δ ^ 2)⁻¹ * killedHeat A t z w := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne t.2 (Ne.symm (by exact_mod_cast ht))
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hct : (((δ ^ 2).toNNReal * t : NNReal) : ℝ) = δ ^ 2 * t := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hδ2.le]
  have ht'0 : (δ ^ 2).toNNReal * t ≠ 0 := mul_ne_zero (Real.toNNReal_pos.2 hδ2).ne' ht
  have hopen : IsOpen (affineC δ b '' A) := by
    rw [← coe_affineHomeoC hδ b]; exact (affineHomeoC hδ b).isOpenMap A hA
  have hs : Real.sqrt (((δ ^ 2).toNNReal * t : NNReal) : ℝ) = δ * Real.sqrt t := by
    rw [hct, Real.sqrt_mul hδ2.le, Real.sqrt_sq hδ.le]
  have hst : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht').ne'
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have key : ∀ x, ((Real.sqrt (((δ ^ 2).toNNReal * t : NNReal) : ℝ) : ℝ) : ℂ)⁻¹ * affineC δ b x =
      ((Real.sqrt t : ℝ) : ℂ)⁻¹ * x +
        ((Real.sqrt (((δ ^ 2).toNNReal * t : NNReal) : ℝ) : ℝ) : ℂ)⁻¹ * b := by
    intro x
    rw [hs, affineC]
    push_cast
    field_simp
  have hset : ((Real.sqrt (((δ ^ 2).toNNReal * t : NNReal) : ℝ) : ℝ) : ℂ)⁻¹ • (affineC δ b '' A) =
      (· + ((Real.sqrt (((δ ^ 2).toNNReal * t : NNReal) : ℝ) : ℝ) : ℂ)⁻¹ * b) ''
        (((Real.sqrt t : ℝ) : ℂ)⁻¹ • A) := by
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    funext x
    rw [smul_eq_mul, smul_eq_mul, key]
  have hbr : bridgeStay (affineC δ b '' A) ((δ ^ 2).toNNReal * t) (affineC δ b z) (affineC δ b w) =
      bridgeStay A t z w := by
    rw [bridgeStay_scale hopen ht'0, bridgeStay_scale hA ht, hset, key, key, bridgeStay_add]
  unfold killedHeat
  rw [hct, heatKernel_affineC hδ b, hbr, mul_assoc]

lemma mem_Ioc_iff_scale {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    s ∈ Ioc 0 (δ ^ 2) ↔ (δ ^ 2)⁻¹ * s ∈ Ioc (0 : ℝ) 1 := by
  have h2 : 0 < δ ^ 2 := by positivity
  simp only [mem_Ioc]
  rw [inv_mul_le_iff₀ h2, mul_one, mul_pos_iff_of_pos_left (inv_pos.2 h2)]

lemma affineC_image_ball {δ : ℝ} (hδ : 0 < δ) (b x : ℂ) (ρ : ℝ) :
    affineC δ b '' Metric.ball x ρ = Metric.ball (affineC δ b x) (δ * ρ) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Metric.mem_ball, dist_affineC hδ]; exact mul_lt_mul_of_pos_left hu hδ
  · intro hy
    have hyy : affineC δ b (affineC δ⁻¹ (-b / δ) y) = y := by
      have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
      simp only [affineC]; push_cast; field_simp; ring
    refine ⟨affineC δ⁻¹ (-b / δ) y, ?_, hyy⟩
    have h := dist_affineC hδ b (affineC δ⁻¹ (-b / δ) y) x
    rw [hyy] at h
    rw [Metric.mem_ball] at hy ⊢
    rw [h] at hy
    exact lt_of_mul_lt_mul_left hy hδ.le

/-- the kernel of `ĥ^tr` after scaling: `1_{(0,δ²]}(s) p_{B_{δ/10}(z)}(s/2; z, w)` -/
def trKerSc (δ : ℝ) (z : ℂ) (p : ℝ × ℂ) : ℝ :=
  wndKernel (Metric.ball z (δ / 10)) (Ioc 0 (δ ^ 2)) z p

/-- the scaled `ĥ^tr` kernel integrated against `μ` -/
def trMeasKerSc (δ : ℝ) (μ : Measure ℂ) (p : ℝ × ℂ) : ℝ := ∫ z, trKerSc δ z p ∂μ

open Classical in
/-- the `L²` class of `trMeasKerSc δ μ` (junk `0` if it is not square integrable) -/
def trMeasKerScL2 (δ : ℝ) (μ : Measure ℂ) : WNSpace :=
  if h : MemLp (trMeasKerSc δ μ) 2 volume then h.toLp _ else 0

/-- **Kernel covariance for `ĥ^tr`**: `U_{δ,b}(K^{tr}_μ) = K^{tr,δ}_{(δ·+b)_*μ}` (ball radius
`δ/10`, times `≤ δ²`; for `δ = 1` this is the translation invariance of `ĥ^tr`, DG:953). -/
theorem scFun_trMeasKer {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (μ : Measure ℂ) :
    scFun δ b (trMeasKer μ) = trMeasKerSc δ (μ.map (affineC δ b)) := by
  funext p
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hδ2 : 0 < δ ^ 2 := by positivity
  rw [← coe_affineHomeoC hδ b, ← (affineHomeoC hδ b).toMeasurableEquiv_coe]
  simp only [scFun, trMeasKer, trMeasKerSc]
  rw [integral_map_equiv, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [trKer, trKerSc, wndKernel, scMap, Homeomorph.toMeasurableEquiv_coe, coe_affineHomeoC]
  by_cases hs : p.1 ∈ Ioc 0 (δ ^ 2)
  · rw [indicator_of_mem hs, indicator_of_mem ((mem_Ioc_iff_scale hδ _).1 hs)]
    have hs0 : 0 < (δ ^ 2)⁻¹ * p.1 := ((mem_Ioc_iff_scale hδ _).1 hs).1
    have hw : affineC δ b ((δ⁻¹ : ℝ) • (p.2 - b)) = p.2 := by
      simp only [affineC, Complex.real_smul, Complex.ofReal_inv]
      rw [← mul_assoc, mul_inv_cancel₀ hδC, one_mul, sub_add_cancel]
    have htne : ((δ ^ 2)⁻¹ * p.1 / 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
    have htime : (δ ^ 2).toNNReal * ((δ ^ 2)⁻¹ * p.1 / 2).toNNReal = (p.1 / 2).toNNReal := by
      rw [← Real.toNNReal_mul hδ2.le]; congr 1; field_simp
    rw [← killedHeat_affineC Metric.isOpen_ball hδ b htne, htime, hw, affineC_image_ball hδ,
      show δ * (1 / 10) = δ / 10 by ring]
  · rw [indicator_of_notMem hs, indicator_of_notMem (fun h => hs ((mem_Ioc_iff_scale hδ _).2 h)),
      mul_zero]

end Killed

end DG
end LQGMetric
