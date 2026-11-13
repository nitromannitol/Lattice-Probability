/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2SignDecomp at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

 











set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.QPos

variable {W : Type*} [Fintype W] [DecidableEq W]

 
def signApply (s : W → Bool) (a : EuclideanSpace ℝ W) : EuclideanSpace ℝ W :=
  WithLp.toLp 2 fun v => if s v then a v else -a v

 
def absE (z : EuclideanSpace ℝ W) : EuclideanSpace ℝ W :=
  WithLp.toLp 2 fun v => |z v|

 
def signKernel (ρ : EuclideanSpace ℝ W → ℝ) (a : EuclideanSpace ℝ W) (s : W → Bool) : ℝ :=
  ρ (signApply s a) / ∑ s', ρ (signApply s' a)

theorem signKernel_nonneg {ρ : EuclideanSpace ℝ W → ℝ} (hρ : ∀ z, 0 < ρ z) (a : EuclideanSpace ℝ W)
    (s : W → Bool) : 0 ≤ signKernel ρ a s :=
  div_nonneg (hρ _).le (Finset.sum_nonneg fun s' _ => (hρ _).le)

theorem sum_signKernel {ρ : EuclideanSpace ℝ W → ℝ} (hρ : ∀ z, 0 < ρ z) (a : EuclideanSpace ℝ W) :
    ∑ s, signKernel ρ a s = 1 := by
  unfold signKernel
  rw [← Finset.sum_div, div_self (Finset.sum_pos (fun s _ => hρ _) Finset.univ_nonempty).ne']

 
def reflE (r : W → Bool) : EuclideanSpace ℝ W ≃ₗᵢ[ℝ] EuclideanSpace ℝ W :=
  LinearIsometryEquiv.piLpCongrRight 2 fun v =>
    if r v then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ

theorem reflE_apply (r : W → Bool) (z : EuclideanSpace ℝ W) : reflE r z = signApply r z := by
  unfold reflE signApply
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  congr 1
  funext v
  by_cases h : r v <;> simp [h]

theorem absE_signApply (r : W → Bool) (z : EuclideanSpace ℝ W) :
    absE (signApply r z) = absE z := by
  unfold absE signApply
  congr 1
  funext v
  by_cases h : r v <;> simp [h]

 
def relSign (z : EuclideanSpace ℝ W) (r : W → Bool) : W → Bool := fun v => xor (r v) (decide (z v < 0))

theorem signApply_relSign (z : EuclideanSpace ℝ W) (r : W → Bool) :
    signApply (relSign z r) (absE z) = signApply r z := by
  unfold signApply relSign absE
  congr 1
  funext v
  simp only [WithLp.ofLp_toLp]
  by_cases hz : z v < 0
  · rw [abs_of_neg hz]
    by_cases h : r v <;> simp [h, hz]
  · rw [abs_of_nonneg (not_lt.mp hz)]
    by_cases h : r v <;> simp [h, hz]

 
def relSignEquiv (z : EuclideanSpace ℝ W) : (W → Bool) ≃ (W → Bool) where
  toFun := relSign z
  invFun := relSign z
  left_inv r := by funext v; simp [relSign]
  right_inv r := by funext v; simp [relSign]

theorem sum_reflect_eq (z : EuclideanSpace ℝ W) (G : EuclideanSpace ℝ W → ℝ) :
    ∑ r, G (signApply r z) = ∑ s, G (signApply s (absE z)) := by
  conv_rhs => rw [← (relSignEquiv z).sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  rw [show (relSignEquiv z) r = relSign z r from rfl, signApply_relSign]

theorem continuous_signApply (s : W → Bool) : Continuous (signApply (W := W) s) := by
  rw [show signApply (W := W) s = ⇑(reflE s) from funext fun z => (reflE_apply s z).symm]
  exact (reflE s).continuous

theorem continuous_absE : Continuous (absE (W := W)) := by
  unfold absE
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun v => (PiLp.continuous_apply 2 _ v).abs)

theorem integrable_comp_signApply {g : EuclideanSpace ℝ W → ℝ} (hg : Integrable g)
    (r : W → Bool) : Integrable (fun z => g (signApply r z)) := by
  have h := ((reflE r).measurePreserving.integrable_comp_emb
    (reflE r).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr hg
  rwa [show (g ∘ ⇑(reflE r)) = fun z => g (signApply r z) from
    funext fun z => by simp [reflE_apply]] at h

 
theorem integral_eq_avg_reflect {g : EuclideanSpace ℝ W → ℝ} (hg : Integrable g) :
    ∫ z, g z = (Fintype.card (W → Bool) : ℝ)⁻¹ * ∫ z, ∑ r, g (signApply r z) := by
  have hcomp : ∀ r : W → Bool, ∫ z, g (signApply r z) = ∫ z, g z := by
    intro r
    have := (reflE r).measurePreserving.integral_comp'
      (f := (reflE r).toHomeomorph.toMeasurableEquiv) g
    simpa [reflE_apply] using this
  rw [integral_finsetSum _ fun r _ => integrable_comp_signApply hg r]
  simp_rw [hcomp]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

 
def signAverage (ρ : EuclideanSpace ℝ W → ℝ) (F : EuclideanSpace ℝ W → ℝ)
    (z : EuclideanSpace ℝ W) : ℝ :=
  ∑ s, signKernel ρ (absE z) s * F (signApply s (absE z))

theorem measurable_signAverage {ρ : EuclideanSpace ℝ W → ℝ} (hρc : Continuous ρ)
    {F : EuclideanSpace ℝ W → ℝ} (hF : Measurable F) : Measurable (signAverage ρ F) := by
  unfold signAverage signKernel
  refine Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.mul ?_ (hF.comp ((continuous_signApply s).comp continuous_absE).measurable)
  refine Measurable.div ?_ ?_
  · exact (hρc.comp ((continuous_signApply s).comp continuous_absE)).measurable
  · exact Finset.measurable_sum _ fun s' _ =>
      (hρc.comp ((continuous_signApply s').comp continuous_absE)).measurable

theorem abs_signAverage_le {ρ : EuclideanSpace ℝ W → ℝ} (hρ : ∀ z, 0 < ρ z)
    {F : EuclideanSpace ℝ W → ℝ} {C : ℝ} (hFb : ∀ z, |F z| ≤ C) (z : EuclideanSpace ℝ W) :
    |signAverage ρ F z| ≤ C := by
  unfold signAverage
  calc |∑ s, signKernel ρ (absE z) s * F (signApply s (absE z))|
      ≤ ∑ s, |signKernel ρ (absE z) s * F (signApply s (absE z))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, signKernel ρ (absE z) s * C := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul, abs_of_nonneg (signKernel_nonneg hρ _ _)]
        exact mul_le_mul_of_nonneg_left (hFb _) (signKernel_nonneg hρ _ _)
    _ = C := by rw [← Finset.sum_mul, sum_signKernel hρ, one_mul]

 
theorem integral_mul_density_sign_decomp {ρ : EuclideanSpace ℝ W → ℝ} (hρc : Continuous ρ)
    (hρ : ∀ z, 0 < ρ z) (hρint : Integrable ρ) {F : EuclideanSpace ℝ W → ℝ} (hF : Measurable F)
    {C : ℝ} (hFb : ∀ z, |F z| ≤ C) :
    ∫ z, F z * ρ z = ∫ z, signAverage ρ F z * ρ z := by
  have hint1 : Integrable (fun z => F z * ρ z) :=
    hρint.bdd_mul hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hFb z)
  have hint2 : Integrable (fun z => signAverage ρ F z * ρ z) :=
    hρint.bdd_mul (measurable_signAverage hρc hF).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_signAverage_le hρ hFb z)
  rw [integral_eq_avg_reflect hint1, integral_eq_avg_reflect hint2]
  congr 2
  funext z
  rw [sum_reflect_eq z (fun y => F y * ρ y)]
  have hH : ∀ r : W → Bool, signAverage ρ F (signApply r z) = signAverage ρ F z := by
    intro r
    simp only [signAverage, absE_signApply]
  simp_rw [hH]
  rw [← Finset.mul_sum, sum_reflect_eq z ρ]
  unfold signAverage signKernel
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hpos : 0 < ∑ s', ρ (signApply s' (absE z)) :=
    Finset.sum_pos (fun s' _ => hρ _) Finset.univ_nonempty
  field_simp

 

theorem integral_sign_decomp {ρ : EuclideanSpace ℝ W → ℝ} (hρc : Continuous ρ)
    (hρ : ∀ z, 0 < ρ z) (hρint : Integrable ρ) {F : EuclideanSpace ℝ W → ℝ} (hF : Measurable F)
    {C : ℝ} (hFb : ∀ z, |F z| ≤ C) :
    ∫ z, F z ∂(volume.withDensity fun z => ENNReal.ofReal (ρ z)) =
      ∫ z, signAverage ρ F z ∂(volume.withDensity fun z => ENNReal.ofReal (ρ z)) := by
  have hm : Measurable fun z => ENNReal.ofReal (ρ z) := hρc.measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hρ _).le, smul_eq_mul, mul_comm (ρ _)]
  exact integral_mul_density_sign_decomp hρc hρ hρint hF hFb

end SupercriticalLQGUniqueness.B2.QPos
