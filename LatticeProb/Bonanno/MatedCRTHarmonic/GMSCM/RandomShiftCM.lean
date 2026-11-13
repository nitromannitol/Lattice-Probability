/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.RandomShiftCM at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.LocalMarkov
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.ZBCMLaw

/-!
# Scalar-parameter Cameron–Martin shifts of a zero-boundary GFF

The normalization difference is a random real scalar `c`. This module treats
the family `f₀ + c • f₁` of compactly supported smooth zero-boundary shifts.
It proves joint measurability of its Cameron–Martin density and the quadratic
energy bound used with a Gaussian square exponential moment.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovHarm
open QuantumZipper QuantumZipper.K3
open MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

variable {U : Opens ℂ}

/-- The Cameron–Martin test function is additive on compactly supported
smooth shifts. -/
theorem cmTestOn_add (f g : zsSub (U : Set ℂ)) :
    cmTestOn (f + g) = cmTestOn f + cmTestOn g := by
  ext x
  change (cmTest (zsTest (f + g).2)) x =
    (cmTest (zsTest f.2)) x + (cmTest (zsTest g.2)) x
  simpa only [add_apply] using
    congrArg (fun ψ : TestC => ψ x) (cmTest_add f.2 g.2 (f + g).2)

/-- The Cameron–Martin test function respects scalar multiplication. -/
theorem cmTestOn_smul (a : ℝ) (f : zsSub (U : Set ℂ)) :
    cmTestOn (a • f) = a • cmTestOn f := by
  ext x
  change (cmTest (zsTest (a • f).2)) x = a * (cmTest (zsTest f.2)) x
  simpa only [smul_apply, smul_eq_mul] using
    congrArg (fun ψ : TestC => ψ x) (cmTest_smul a f.2 (a • f).2)

/-- The Dirichlet energy of a test shift is the squared Hilbert norm of its
gradient feature. -/
theorem dirichletEnergyOn_eq_norm_gradLin_sq (f : zsSub (U : Set ℂ)) :
    dirichletEnergyOn U f.1 = ‖gradLin U f‖ ^ 2 := by
  exact (norm_gradFeat_sq ((isDNSpace_zeroSpace _).smooth f f.2)
    ((isDNSpace_zeroSpace _).energy f f.2)).symm

/-- A scalar-indexed Cameron–Martin shift has at most quadratic energy in the
scalar coefficient. -/
theorem dirichletEnergyOn_add_smul_le (f₀ f₁ : zsSub (U : Set ℂ)) (c : ℝ) :
    dirichletEnergyOn U (f₀ + c • f₁).1 ≤
      2 * dirichletEnergyOn U f₀.1 + 2 * c ^ 2 * dirichletEnergyOn U f₁.1 := by
  rw [dirichletEnergyOn_eq_norm_gradLin_sq,
    dirichletEnergyOn_eq_norm_gradLin_sq,
    dirichletEnergyOn_eq_norm_gradLin_sq, map_add, map_smul]
  have htri : ‖gradLin U f₀ + c • gradLin U f₁‖ ≤
      ‖gradLin U f₀‖ + |c| * ‖gradLin U f₁‖ := by
    calc
      _ ≤ ‖gradLin U f₀‖ + ‖c • gradLin U f₁‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs]
  have h0 : 0 ≤ ‖gradLin U f₀‖ := norm_nonneg _
  have h1 : 0 ≤ |c| * ‖gradLin U f₁‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have h2 : 0 ≤ ‖gradLin U f₀ + c • gradLin U f₁‖ := norm_nonneg _
  have hc : |c| ^ 2 = c ^ 2 := sq_abs c
  nlinarith [sq_nonneg (‖gradLin U f₀‖ - |c| * ‖gradLin U f₁‖)]

/-- The jointly measurable density for `f₀ + c • f₁`. -/
def randomZBDensity (f₀ f₁ : zsSub (U : Set ℂ)) (c : ℝ) (z : DistOn U) : ℝ≥0∞ :=
  ENNReal.ofReal (GMSAppA.zbDensity (f₀ + c • f₁) z)

/-- Joint measurability of the scalar-parameter Cameron–Martin density. -/
theorem measurable_randomZBDensity (f₀ f₁ : zsSub (U : Set ℂ)) :
    Measurable (fun x : ℝ × DistOn U => randomZBDensity f₀ f₁ x.1 x.2) := by
  have hE : Measurable fun c : ℝ => dirichletEnergyOn U (f₀ + c • f₁).1 := by
    rw [show (fun c : ℝ => dirichletEnergyOn U (f₀ + c • f₁).1) =
      fun c => ‖gradLin U f₀ + c • gradLin U f₁‖ ^ 2 by
        funext c; rw [dirichletEnergyOn_eq_norm_gradLin_sq, map_add, map_smul]]
    exact ((continuous_const.add (continuous_id.smul continuous_const)).norm.pow 2).measurable
  have hpair : Measurable fun x : ℝ × DistOn U =>
      x.2 (cmTestOn f₀) + x.1 * x.2 (cmTestOn f₁) := by
    exact ((measurable_distOn_apply _).comp measurable_snd).add
      (measurable_fst.mul ((measurable_distOn_apply _).comp measurable_snd))
  have hE' : Measurable fun x : ℝ × DistOn U =>
      dirichletEnergyOn U (f₀ + x.1 • f₁).1 := hE.comp measurable_fst
  have heq : (fun x : ℝ × DistOn U => randomZBDensity f₀ f₁ x.1 x.2) =
      fun (x : ℝ × DistOn U) => ENNReal.ofReal (Real.exp
        (x.2 (cmTestOn f₀) + x.1 * x.2 (cmTestOn f₁) -
          dirichletEnergyOn U (f₀ + x.1 • f₁).1 / 2)) := by
    funext x
    rw [randomZBDensity, GMSAppA.zbDensity, cmTestOn_add, cmTestOn_smul]
    simp [map_add, map_smul, smul_eq_mul]
  rw [heq]
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hpair.sub (hE'.div_const _)))

/-- The distribution associated with a compactly supported smooth shift has
the expected action on test functions. -/
theorem ofFunOn_zsSub_apply (f : zsSub (U : Set ℂ)) (φ : TestOn U) :
    ofFunOn U f.1 φ = ∫ x, f.1 x * φ x := by
  rw [GFFBdry.ofFunOn_apply (f.2.1.continuous.locallyIntegrable.locallyIntegrableOn _)]
  congr 1
  funext x
  ring

/-- For each fixed scalar, the random-shift density is the genuine
Cameron–Martin RN density of the zero-boundary GFF. -/
theorem randomZBDensity_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P)
    (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    (f₀ f₁ : zsSub (U : Set ℂ)) (c : ℝ) :
    (P.map Z).map (fun z => z + ofFunOn U (f₀ + c • f₁).1) =
      (P.map Z).withDensity (randomZBDensity f₀ f₁ c) := by
  let f : zsSub (U : Set ℂ) := f₀ + c • f₁
  let T : DistOn U := ofFunOn U f.1
  have hT : Measurable (fun z : DistOn U => z + T) :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const (T φ)
  have hρ : Measurable (randomZBDensity f₀ f₁ c) :=
    (measurable_randomZBDensity f₀ f₁).comp (measurable_const.prodMk measurable_id)
  refine Measure.ext_of_lintegral _ fun Ψ hΨ => ?_
  rw [lintegral_map hΨ hT,
    lintegral_withDensity_eq_lintegral_mul _ hρ hΨ]
  calc
    (∫⁻ z, Ψ (z + T) ∂(P.map Z)) =
        ∫⁻ z, Ψ z * randomZBDensity f₀ f₁ c z ∂(P.map Z) :=
      GMSAppA.zbcm_lintegral hadm hne hZ f (ofFunOn_zsSub_apply f) hΨ
    _ = ∫⁻ z, randomZBDensity f₀ f₁ c z * Ψ z ∂(P.map Z) := by
      refine lintegral_congr fun z => ?_
      exact mul_comm _ _

/-- Every conditional density in the scalar family has the exact Gaussian
moment given by the Dirichlet energy of its shift. -/
theorem randomZBDensity_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P)
    (hadm : ZBAdmissible U) (f₀ f₁ : zsSub (U : Set ℂ)) (c s : ℝ) :
    ∫⁻ z, randomZBDensity f₀ f₁ c z ^ s ∂(P.map Z) =
      ENNReal.ofReal (Real.exp (s * (s - 1) *
        dirichletEnergyOn U (f₀ + c • f₁).1 / 2)) := by
  exact GMSAppA.zbcm_moment hadm hZ (f₀ + c • f₁) s
/-- The distributional shift is affine in the scalar parameter. -/
theorem ofFunOn_add_smul_zsSub (f₀ f₁ : zsSub (U : Set ℂ)) (c : ℝ) :
    ofFunOn U (f₀ + c • f₁).1 = ofFunOn U f₀.1 + c • ofFunOn U f₁.1 := by
  ext φ
  rw [ofFunOn_zsSub_apply, add_apply, smul_apply,
    ofFunOn_zsSub_apply, ofFunOn_zsSub_apply]
  have h₀ : Integrable (fun x => f₀.1 x * φ x) volume :=
    integrable_mul_test (f₀.2.1.of_le (by simp)).contDiffOn φ
  have h₁ : Integrable (fun x => f₁.1 x * φ x) volume :=
    integrable_mul_test (f₁.2.1.of_le (by simp)).contDiffOn φ
  have heq : (fun x => (f₀ + c • f₁).1 x * φ x) =
      fun x => f₀.1 x * φ x + c * (f₁.1 x * φ x) := by
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, integral_add h₀ (h₁.const_mul c), integral_const_mul]
  ring

/-- Negation of a compactly supported shift negates its distribution. -/
theorem ofFunOn_neg_zsSub (f : zsSub (U : Set ℂ)) :
    ofFunOn U (-f).1 = -ofFunOn U f.1 := by
  ext φ
  change ofFunOn U (-f).1 φ = -(ofFunOn U f.1 φ)
  rw [ofFunOn_zsSub_apply, ofFunOn_zsSub_apply]
  have heq : (fun x => (-f).1 x * φ x) = fun x => -(f.1 x * φ x) := by
    funext x
    simp
  rw [heq, integral_neg]

/-- The jointly measurable scalar-indexed shift on zero-boundary distributions. -/
def randomZBShift (f₀ f₁ : zsSub (U : Set ℂ)) (c : ℝ) (z : DistOn U) : DistOn U :=
  z + ofFunOn U f₀.1 + c • ofFunOn U f₁.1

theorem measurable_randomZBShift (f₀ f₁ : zsSub (U : Set ℂ)) :
    Measurable (fun x : ℝ × DistOn U => randomZBShift f₀ f₁ x.1 x.2) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  have heq : (fun x : ℝ × DistOn U => randomZBShift f₀ f₁ x.1 x.2 φ) =
      fun x => x.2 φ + ofFunOn U f₀.1 φ + x.1 * ofFunOn U f₁.1 φ := by
    funext x
    simp [randomZBShift, add_apply, smul_apply, smul_eq_mul]
  rw [heq]
  exact (((measurable_distOn_apply φ).comp measurable_snd).add_const _).add
    (measurable_fst.mul_const _)
/-- The scalar-indexed law identity in the jointly measurable affine form. -/
theorem randomZBShift_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P)
    (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    (f₀ f₁ : zsSub (U : Set ℂ)) (c : ℝ) :
    (P.map Z).map (randomZBShift f₀ f₁ c) =
      (P.map Z).withDensity (randomZBDensity f₀ f₁ c) := by
  have e : randomZBShift f₀ f₁ c = fun z => z + ofFunOn U (f₀ + c • f₁).1 := by
    funext z
    rw [randomZBShift, ofFunOn_add_smul_zsSub, add_assoc]
  rw [e]
  exact randomZBDensity_law hZ hadm hne f₀ f₁ c

/-- Choose a Hölder exponent close enough to one that the coefficient of the
Gaussian normalization square stays below a prescribed exponential rate. -/
theorem exists_holder_exponent_for_energy {E t : ℝ} (hE : 0 ≤ E) (ht : 0 < t) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ p * (p - 1) * E ≤ t := by
  let d : ℝ := min 1 (t / (E + 1))
  have hden : 0 < E + 1 := by linarith
  have hd0 : 0 < d := lt_min one_pos (div_pos ht hden)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdt : d ≤ t / (E + 1) := min_le_right _ _
  let p : ℝ := 1 + d / 2
  have hp : 1 < p := by dsimp [p]; linarith
  have hp2 : p < 2 := by dsimp [p]; linarith
  have hprod : p * (p - 1) ≤ d := by
    dsimp [p]
    nlinarith [sq_nonneg d]
  have hde : d * E ≤ t := by
    have hmul := mul_le_mul_of_nonneg_right hdt hE
    have hfac : t / (E + 1) * E ≤ t := by
      calc
        t / (E + 1) * E = (t * E) / (E + 1) := by ring
        _ ≤ t := (div_le_iff₀ hden).2 (by nlinarith)
    exact hmul.trans hfac
  exact ⟨p, hp, hp2, (mul_le_mul_of_nonneg_right hprod hE).trans hde⟩

/-- A Gaussian-square exponential moment of the scalar makes the joint
Cameron–Martin density `L^p` for some `p > 1`. -/
theorem exists_randomZBDensity_product_moment
    {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    {κ : Measure A} [IsProbabilityMeasure κ] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P)
    (hadm : ZBAdmissible U) (f₀ f₁ : zsSub (U : Set ℂ))
    (c : A → ℝ) (hc : Measurable c) {t : ℝ} (ht : 0 < t)
    (hct : Integrable (fun a => Real.exp (t * (c a) ^ 2)) κ) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧
      ∫⁻ x, randomZBDensity f₀ f₁ (c x.1) x.2 ^ p ∂(κ.prod (P.map Z)) < ⊤ := by
  let E₀ : ℝ := dirichletEnergyOn U f₀.1
  let E₁ : ℝ := dirichletEnergyOn U f₁.1
  have hE₁ : 0 ≤ E₁ := by
    rw [show E₁ = ‖gradLin U f₁‖ ^ 2 from dirichletEnergyOn_eq_norm_gradLin_sq f₁]
    positivity
  obtain ⟨p, hp, hp2, hcoef⟩ := exists_holder_exponent_for_energy hE₁ ht
  let a : ℝ := p * (p - 1)
  have ha : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  have hρm : Measurable (fun x : A × DistOn U => randomZBDensity f₀ f₁ (c x.1) x.2) :=
    (measurable_randomZBDensity f₀ f₁).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have hK : Integrable (fun x => Real.exp (a * E₀ + t * (c x) ^ 2)) κ := by
    have heq : (fun x => Real.exp (a * E₀ + t * (c x) ^ 2)) =
        fun x => Real.exp (a * E₀) * Real.exp (t * (c x) ^ 2) := by
      funext x
      rw [Real.exp_add]
    rw [heq]
    exact hct.const_mul _
  refine ⟨p, hp, hp2, ?_⟩
  rw [lintegral_prod _ (hρm.pow_const p).aemeasurable]
  simp_rw [randomZBDensity_moment hZ hadm f₀ f₁]
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (p * (p - 1) *
        dirichletEnergyOn U (f₀ + c x • f₁).1 / 2)) ∂κ) ≤
        ∫⁻ x, ENNReal.ofReal (Real.exp (a * E₀ + t * (c x) ^ 2)) ∂κ := by
      refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have henergy := dirichletEnergyOn_add_smul_le f₀ f₁ (c x)
      calc
        p * (p - 1) * dirichletEnergyOn U (f₀ + c x • f₁).1 / 2 ≤
            a * (2 * E₀ + 2 * (c x) ^ 2 * E₁) / 2 := by
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left henergy ha)
                (by norm_num)
        _ = a * E₀ + (a * E₁) * (c x) ^ 2 := by ring
        _ ≤ a * E₀ + t * (c x) ^ 2 := by
          have hm : a * E₁ * (c x) ^ 2 ≤ t * (c x) ^ 2 :=
            mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
          linarith
    _ = ENNReal.ofReal (∫ x, Real.exp (a * E₀ + t * (c x) ^ 2) ∂κ) :=
      (ofReal_integral_eq_lintegral_ofReal hK
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end MatedCRTHarmonic.GMSCM
