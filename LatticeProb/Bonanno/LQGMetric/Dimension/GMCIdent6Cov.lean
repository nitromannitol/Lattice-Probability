/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent6Cov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGreen
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound

/-!
# Uniform upper bound on the covariance of the band field `h̃^δ_ε` (P2-GMCID6, step (b))

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 684–688) use that the band field
`h̃^δ_ε = √π ∫_{ε²}^{δ²} ∫ p_𝕍(s/2; ·, w) W(dw, ds)` (DZZ (eq:WND_decomposition)) is
log-correlated below scale `δ`. Only the upper bound is needed for the Kahane comparison (both
for positive and for negative moments, Kahane's inequality being monotone in the covariance):

* **`pi_integral_killedHeat_le`** : for `0 < ε ≤ δ ≤ L` and `‖u − v‖ ≤ L`,
  `π ∫_{ε²}^{δ²} p_𝕍(s; u, v) ds ≤ log(L / max(ε, ‖u − v‖)) + 1`.

Proof (own elementary proof): `p_𝕍 ≤ p_ℂ` (`killedHeat_le_heatKernel`) and
`π p_ℂ(s; u, v) ≤ min((2s)⁻¹, ‖u − v‖⁻²)` (`heatKernel_le_inv`, `heatKernel_le_inv_sq`); then
`∫_a^b (2s)⁻¹ ds = log(b/a)/2` and `∫_{ε²}^{r²} r⁻² ds ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent6

open KilledHeat DZZ

lemma pi_killedHeat_le_inv {s : ℝ} (hs : 0 < s) (u v : ℂ) :
    Real.pi * killedHeat openSquare s.toNNReal u v ≤ (2 * s)⁻¹ := by
  have h := (killedHeat_le_heatKernel openSquare s.toNNReal u v).trans
    (heatKernel_le_inv _ (NNReal.coe_nonneg _) u v)
  rw [Real.coe_toNNReal _ hs.le] at h
  have := Real.pi_pos
  calc Real.pi * killedHeat openSquare s.toNNReal u v ≤ Real.pi * (2 * Real.pi * s)⁻¹ :=
        mul_le_mul_of_nonneg_left h this.le
    _ = (2 * s)⁻¹ := by field_simp

lemma pi_killedHeat_le_inv_sq {s : ℝ} (hs : 0 < s) {u v : ℂ} (huv : u ≠ v) :
    Real.pi * killedHeat openSquare s.toNNReal u v ≤ (‖u - v‖ ^ 2)⁻¹ := by
  have h := (killedHeat_le_heatKernel openSquare s.toNNReal u v).trans
    (heatKernel_le_inv_sq _ (by rw [Real.coe_toNNReal _ hs.le]; exact hs) huv)
  have := Real.pi_pos
  have hr : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
  calc Real.pi * killedHeat openSquare s.toNNReal u v ≤ Real.pi * (Real.pi * ‖u - v‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h this.le
    _ = (‖u - v‖ ^ 2)⁻¹ := by field_simp

lemma integrableOn_killedHeat_Ioo {a b : ℝ} (ha : 0 < a) (u v : ℂ) :
    IntegrableOn (fun s : ℝ => killedHeat openSquare s.toNNReal u v) (Ioo a b) :=
  integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball (half_pos ha) (fun s hs => (half_lt_self ha).trans hs.1) u v

lemma integrableOn_inv_Ioo {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s⁻¹) (Ioo a b) := by
  rcases le_total a b with hab | hab
  · exact ((continuousOn_inv₀.mono fun x hx => mem_compl_singleton_iff.mpr
      (ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · rw [Ioo_eq_empty (not_lt.2 hab)]; exact integrableOn_empty

/-- `π ∫_a^b p_𝕍(s; u, v) ds ≤ log(b/a)/2` -/
lemma pi_integral_killedHeat_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (u v : ℂ) :
    Real.pi * ∫ s in Ioo a b, killedHeat openSquare s.toNNReal u v ≤ Real.log (b / a) / 2 := by
  rw [← integral_const_mul]
  calc ∫ s in Ioo a b, Real.pi * killedHeat openSquare s.toNNReal u v
      ≤ ∫ s in Ioo a b, (2 : ℝ)⁻¹ * s⁻¹ := by
        refine setIntegral_mono_on ((integrableOn_killedHeat_Ioo ha u v).const_mul _)
          ((integrableOn_inv_Ioo ha).const_mul _) measurableSet_Ioo fun s hs => ?_
        have hs0 : 0 < s := ha.trans hs.1
        rw [← mul_inv]; exact pi_killedHeat_le_inv hs0 u v
    _ = Real.log (b / a) / 2 := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
        ring

/-- **uniform upper bound on the band covariance** -/
theorem pi_integral_killedHeat_le {ε δ L : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hδL : δ ≤ L)
    (u v : ℂ) (huv : ‖u - v‖ ≤ L) :
    Real.pi * ∫ s in Ioo (ε ^ 2) (δ ^ 2), killedHeat openSquare s.toNNReal u v ≤
      Real.log (L / max ε ‖u - v‖) + 1 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  set r := ‖u - v‖ with hr
  rcases le_or_gt r ε with hrε | hrε
  · rw [max_eq_left hrε]
    have h := pi_integral_killedHeat_le_log hε2 (pow_le_pow_left₀ hε.le hεδ 2) u v
    have e : Real.log (δ ^ 2 / ε ^ 2) / 2 = Real.log (δ / ε) := by
      rw [← div_pow, Real.log_pow]; push_cast; ring
    have hL : Real.log (δ / ε) ≤ Real.log (L / ε) :=
      Real.log_le_log (div_pos (hε.trans_le hεδ) hε) (div_le_div_of_nonneg_right hδL hε.le)
    linarith
  · rw [max_eq_right hrε.le]
    have hr0 : 0 < r := hε.trans hrε
    have huv' : u ≠ v := fun h => by rw [hr, h, sub_self, norm_zero] at hr0; exact lt_irrefl _ hr0
    set D := max δ r
    have hD : r ≤ D := le_max_right _ _
    have hDL : D ≤ L := max_le hδL huv
    have hr2 : ε ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hε.le hrε.le 2
    have hrD2 : r ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hr0.le hD 2
    have hint := integrableOn_killedHeat_Ioo (b := D ^ 2) hε2 u v
    have hnn : ∀ s : ℝ, 0 ≤ killedHeat openSquare s.toNNReal u v := fun s => killedHeat_nonneg _ _ _ _
    -- enlarge the interval to `(ε², D²)`
    have h1 : ∫ s in Ioo (ε ^ 2) (δ ^ 2), killedHeat openSquare s.toNNReal u v ≤
        ∫ s in Ioo (ε ^ 2) (D ^ 2), killedHeat openSquare s.toNNReal u v :=
      setIntegral_mono_set hint (Eventually.of_forall fun s => hnn s)
        (Eventually.of_forall (Ioo_subset_Ioo_right
          (pow_le_pow_left₀ (hε.trans_le hεδ).le (le_max_left δ r) 2)))
    -- split at `r²`
    have hr2' : ε ^ 2 < r ^ 2 := pow_lt_pow_left₀ hrε hε.le two_ne_zero
    have hsplit : ∫ s in Ioo (ε ^ 2) (D ^ 2), killedHeat openSquare s.toNNReal u v =
        (∫ s in Ioo (ε ^ 2) (r ^ 2), killedHeat openSquare s.toNNReal u v) +
          ∫ s in Ioo (r ^ 2) (D ^ 2), killedHeat openSquare s.toNNReal u v := by
      rw [← Ioo_union_Ico_eq_Ioo hr2' hrD2, setIntegral_union
        (Set.disjoint_left.2 fun s h1 h2 => not_lt.2 h2.1 h1.2) measurableSet_Ico
        (hint.mono_set (Ioo_subset_Ioo_right hrD2)) (hint.mono_set
          (fun s hs => ⟨hr2'.trans_le hs.1, hs.2⟩)), integral_Ico_eq_integral_Ioo]
    have h2 : Real.pi * ∫ s in Ioo (ε ^ 2) (r ^ 2), killedHeat openSquare s.toNNReal u v ≤ 1 := by
      rw [← integral_const_mul]
      calc ∫ s in Ioo (ε ^ 2) (r ^ 2), Real.pi * killedHeat openSquare s.toNNReal u v
          ≤ ∫ s in Ioo (ε ^ 2) (r ^ 2), (r ^ 2)⁻¹ := by
            refine setIntegral_mono_on ((hint.mono_set (Ioo_subset_Ioo_right hrD2)).const_mul
              _) (integrableOn_const (by simp)) measurableSet_Ioo fun s hs => ?_
            exact pi_killedHeat_le_inv_sq (hε2.trans hs.1) huv'
        _ = (r ^ 2 - ε ^ 2) * (r ^ 2)⁻¹ := by
            rw [setIntegral_const, Real.volume_real_Ioo_of_le hr2, smul_eq_mul]
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
    have h3 := pi_integral_killedHeat_le_log (by positivity : 0 < r ^ 2) hrD2 u v
    have e : Real.log (D ^ 2 / r ^ 2) / 2 = Real.log (D / r) := by
      rw [← div_pow, Real.log_pow]; push_cast; ring
    have hL : Real.log (D / r) ≤ Real.log (L / r) :=
      Real.log_le_log (div_pos (hr0.trans_le hD) hr0) (div_le_div_of_nonneg_right hDL hr0.le)
    have := Real.pi_pos
    nlinarith [mul_le_mul_of_nonneg_left h1 this.le]

end GMCIdent6
end LQGMetric
