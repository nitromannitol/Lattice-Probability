/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.Kernel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Kappa
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPKernel
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsBandVersion
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPExponent
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# The kernel `C = κ ⋆ κ` of the white-noise field (packet P-F1, target T3)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1) and (3.1); planning audit HA2, Details D1
(Lemma D1.3).  For an admissible kernel `κ` (`IsLFPPKernel`) the covariance profile of the band
fields is the autocorrelation
`C(x) = autoCorr κ x = ∫ κ(y) κ(y + x) dy`,
which equals `κ ⋆ κ` because `κ` is even (HA2-16: defining `C` as the autocorrelation makes (3.1)
independent of radiality).

Main results (namespace `HigherDimLFPP`):

* basic facts on admissible kernels: continuity, integrability, boundedness, a Lipschitz constant, a
  support radius, evenness and invariance under linear isometries (`IsLFPPKernel.*`);
* `autoCorr_zero` (`C(0) = 1`), `autoCorr_neg` (even), `autoCorr_linearIsometryEquiv` and
  `autoCorr_eq_of_norm_eq` (radial), `abs_autoCorr_le_one`, `autoCorr_nonneg`, `autoCorr_le_one`;
* support: `autoCorr_eq_zero_of_two_mul_le`, `support_autoCorr_subset_ball`,
  `tsupport_autoCorr_subset_closedBall`, `hasCompactSupport_autoCorr`;
* `one_sub_autoCorr_eq` (`1 - C(x) = ½ ‖κ(· + x) - κ‖²`) and the quadratic bound
  `one_sub_autoCorr_le_of_lipschitzWith` (`1 - C(x) ≤ K² |B(0,ρ)| ‖x‖²` for a Lipschitz constant `K`
  and a support radius `ρ` of `κ`), with the existential form `exists_one_sub_autoCorr_le`;
* `abs_autoCorr_sub_le` (`|C(x) - C(x')| ≤ K (∫ κ) ‖x - x'‖`), `exists_lipschitzWith_autoCorr`,
  `continuous_autoCorr`;
* `autoCorr_eq_convolution` and `contDiff_autoCorr` (`C` is `C^∞`).

There is no 2D source file for this layer: the 2D library (`LQGDimension`) works with the Gaussian
heat kernel, for which the analogous facts are explicit formulas (HA6, packet F1: "new").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ}

/-- The covariance profile `C(x) = ∫ κ(y) κ(y + x) dy` of the band fields ((3.1); the
autocorrelation of `κ`, equal to `κ ⋆ κ` for even `κ`). -/
def autoCorr (κ : Rd d → ℝ) (x : Rd d) : ℝ := ∫ y, κ y * κ (y + x)

namespace IsLFPPKernel

variable {κ : Rd d → ℝ}

theorem continuous (hκ : IsLFPPKernel κ) : Continuous κ := hκ.contDiff.continuous

theorem integrable (hκ : IsLFPPKernel κ) : Integrable κ :=
  hκ.continuous.integrable_of_hasCompactSupport hκ.hasCompactSupport

theorem hasCompactSupport_sq (hκ : IsLFPPKernel κ) : HasCompactSupport fun x => κ x ^ 2 :=
  hκ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)

theorem integrable_sq (hκ : IsLFPPKernel κ) : Integrable fun x => κ x ^ 2 :=
  (hκ.continuous.pow 2).integrable_of_hasCompactSupport hκ.hasCompactSupport_sq

/-- `y ↦ κ(y) κ(y + x)` is integrable. -/
theorem integrable_mul_add (hκ : IsLFPPKernel κ) (x : Rd d) :
    Integrable fun y => κ y * κ (y + x) :=
  (hκ.continuous.mul (hκ.continuous.comp (continuous_id.add continuous_const)))
    |>.integrable_of_hasCompactSupport hκ.hasCompactSupport.mul_right

/-- `∫ κ(y + x)² dy = 1`. -/
theorem integral_sq_add (hκ : IsLFPPKernel κ) (x : Rd d) : ∫ y, κ (y + x) ^ 2 = 1 := by
  rw [integral_add_right_eq_self (fun y => κ y ^ 2) x]
  exact hκ.integral_sq

/-- `κ` is bounded. -/
theorem exists_bound (hκ : IsLFPPKernel κ) : ∃ A, ∀ x, |κ x| ≤ A := by
  obtain ⟨A, hA⟩ := hκ.continuous.bounded_above_of_compact_support hκ.hasCompactSupport
  exact ⟨A, fun x => by simpa only [Real.norm_eq_abs] using hA x⟩

/-- `κ` is Lipschitz (it is `C¹` with compact support). -/
theorem exists_lipschitzWith (hκ : IsLFPPKernel κ) : ∃ K, LipschitzWith K κ :=
  ContDiff.lipschitzWith_of_hasCompactSupport hκ.hasCompactSupport hκ.contDiff (by
    simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])

/-- A support radius: `κ y = 0` for `‖y‖ ≥ ρ`. -/
theorem exists_radius (hκ : IsLFPPKernel κ) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y, ρ ≤ ‖y‖ → κ y = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).1
    hκ.hasCompactSupport.isCompact.isBounded
  refine ⟨max r 0 + 1, by positivity, fun y hy => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h1 := hr hmem
  rw [mem_closedBall, dist_zero_right] at h1
  have h2 : r < max r 0 + 1 := lt_of_le_of_lt (le_max_left r 0) (lt_add_one _)
  linarith

/-- `κ` is invariant under linear isometries. -/
theorem comp_linearIsometryEquiv (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x : Rd d) :
    κ (O x) = κ x :=
  hκ.radial (O x) x (O.norm_map x)

end IsLFPPKernel

/-! ### Basic properties of `C` -/

section AutoCorr

variable {κ : Rd d → ℝ}

/-- `C(0) = ‖κ‖₂² = 1`. -/
theorem autoCorr_zero (hκ : IsLFPPKernel κ) : autoCorr κ 0 = 1 := by
  unfold autoCorr
  simp_rw [add_zero, ← sq]
  exact hκ.integral_sq

/-- `C` is invariant under linear isometries (`κ` is radial). -/
theorem autoCorr_linearIsometryEquiv (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x : Rd d) :
    autoCorr κ (O x) = autoCorr κ x := by
  unfold autoCorr
  rw [← (O.measurePreserving).integral_comp' (f := O.toMeasurableEquiv)
    (fun y => κ y * κ (y + O x))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv]
  rw [← map_add, hκ.comp_linearIsometryEquiv, hκ.comp_linearIsometryEquiv]

/-- `C` is radial: `C(x) = C(x')` whenever `‖x‖ = ‖x'‖`. -/
theorem autoCorr_eq_of_norm_eq (hκ : IsLFPPKernel κ) {x x' : Rd d} (h : ‖x‖ = ‖x'‖) :
    autoCorr κ x = autoCorr κ x' := by
  have := autoCorr_linearIsometryEquiv hκ (ℝ ∙ (x - x'))ᗮ.reflection x
  rw [Submodule.reflection_sub h] at this
  exact this.symm

/-- `0 ≤ C` (`κ ≥ 0`). -/
theorem autoCorr_nonneg (hκ : IsLFPPKernel κ) (x : Rd d) : 0 ≤ autoCorr κ x :=
  integral_nonneg fun y => mul_nonneg (hκ.nonneg y) (hκ.nonneg (y + x))

/-- `|C| ≤ 1`, from `2|ab| ≤ a² + b²` (Cauchy–Schwarz). -/
theorem abs_autoCorr_le_one (hκ : IsLFPPKernel κ) (x : Rd d) : |autoCorr κ x| ≤ 1 := by
  have h1 : Integrable fun y => κ y ^ 2 := hκ.integrable_sq
  have h2 : Integrable fun y => κ (y + x) ^ 2 := h1.comp_add_right x
  calc |autoCorr κ x| = ‖∫ y, κ y * κ (y + x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖κ y * κ (y + x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (κ y ^ 2 + κ (y + x) ^ 2) / 2 := by
        refine integral_mono (hκ.integrable_mul_add x).norm ((h1.add h2).div_const 2) fun y => ?_
        simp only [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|κ y| - |κ (y + x)|), sq_abs (κ y), sq_abs (κ (y + x))]
    _ = 1 := by
        rw [integral_div, integral_add h1 h2, hκ.integral_sq, hκ.integral_sq_add x]
        norm_num

theorem autoCorr_le_one (hκ : IsLFPPKernel κ) (x : Rd d) : autoCorr κ x ≤ 1 :=
  (le_abs_self _).trans (abs_autoCorr_le_one hκ x)

/-- `1 - C(x) = ½ ∫ (κ(y + x) - κ(y))² dy`. -/
theorem one_sub_autoCorr_eq (hκ : IsLFPPKernel κ) (x : Rd d) :
    1 - autoCorr κ x = (1 / 2) * ∫ y, (κ (y + x) - κ y) ^ 2 := by
  have h1 : Integrable fun y => κ y ^ 2 := hκ.integrable_sq
  have h2 : Integrable fun y => κ (y + x) ^ 2 := h1.comp_add_right x
  have e : ∀ y, (κ (y + x) - κ y) ^ 2 = κ (y + x) ^ 2 + κ y ^ 2 - 2 * (κ y * κ (y + x)) :=
    fun y => by ring
  have h3 : Integrable fun y => κ (y + x) ^ 2 + κ y ^ 2 := h2.add h1
  have h4 : Integrable fun y => 2 * (κ y * κ (y + x)) := (hκ.integrable_mul_add x).const_mul 2
  simp_rw [e]
  rw [integral_sub h3 h4, integral_add h2 h1, integral_const_mul, hκ.integral_sq_add x,
    hκ.integral_sq]
  unfold autoCorr
  ring

theorem one_sub_autoCorr_nonneg (hκ : IsLFPPKernel κ) (x : Rd d) : 0 ≤ 1 - autoCorr κ x :=
  sub_nonneg.2 (autoCorr_le_one hκ x)

/-! ### Support of `C` -/

/-- If `κ y = 0` for `‖y‖ ≥ ρ`, then `C(x) = 0` for `‖x‖ ≥ 2ρ`. -/
theorem autoCorr_eq_zero_of_two_mul_le {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {x : Rd d}
    (hx : 2 * ρ ≤ ‖x‖) : autoCorr κ x = 0 := by
  unfold autoCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : ρ ≤ ‖y‖
  · simp only [hρ y hy, zero_mul, Pi.zero_apply]
  · have h1 : ‖x‖ ≤ ‖y + x‖ + ‖y‖ := by
      have := norm_add_le (y + x) (-y)
      rwa [add_neg_cancel_comm, norm_neg] at this
    have h2 : ρ ≤ ‖y + x‖ := by linarith
    simp only [hρ _ h2, mul_zero, Pi.zero_apply]

/-! ### The quadratic bound `0 ≤ 1 - C(x) ≤ L ‖x‖²` -/

/-- **Quadratic bound** with an explicit constant: if `κ` is `K`-Lipschitz and vanishes outside
`B(0, ρ)`, then `1 - C(x) ≤ K² |B(0, ρ)| ‖x‖²` (HA2 D1.3, last item, with `‖∇κ‖₂` replaced by the
cruder `K |B(0,ρ)|^{1/2}`). -/
theorem one_sub_autoCorr_le_of_lipschitzWith (hκ : IsLFPPKernel κ) {K : NNReal}
    (hK : LipschitzWith K κ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (x : Rd d) :
    1 - autoCorr κ x ≤ (K : ℝ) ^ 2 * volume.real (ball (0 : Rd d) ρ) * ‖x‖ ^ 2 := by
  set B : Set (Rd d) := ball 0 ρ with hB
  set g : Rd d → ℝ := fun y => B.indicator (fun _ => (1 : ℝ)) y + B.indicator (fun _ => 1) (y + x)
    with hg
  have hBm : MeasurableSet B := measurableSet_ball
  have hBfin : volume B < ⊤ := measure_ball_lt_top
  have hI : Integrable (B.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin.ne)
  have hIx : Integrable fun y => B.indicator (fun _ => (1 : ℝ)) (y + x) := hI.comp_add_right x
  have hgi : Integrable g := hI.add hIx
  have hint : ∫ y, g y = 2 * volume.real B := by
    rw [hg, integral_add hI hIx, integral_add_right_eq_self (B.indicator fun _ => (1 : ℝ)) x,
      integral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one]
    ring
  have hpt : ∀ y, (κ (y + x) - κ y) ^ 2 ≤ ((K : ℝ) * ‖x‖) ^ 2 * g y := by
    intro y
    have hlip : |κ (y + x) - κ y| ≤ (K : ℝ) * ‖x‖ := by
      have := hK.dist_le_mul (y + x) y
      rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
    have hsq : (κ (y + x) - κ y) ^ 2 ≤ ((K : ℝ) * ‖x‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hlip 2
    by_cases h1 : y ∈ B
    · have hg1 : 1 ≤ g y := by
        simp only [hg, indicator_of_mem h1]
        have : 0 ≤ B.indicator (fun _ => (1 : ℝ)) (y + x) :=
          indicator_nonneg (fun _ _ => zero_le_one) _
        linarith
      calc (κ (y + x) - κ y) ^ 2 ≤ ((K : ℝ) * ‖x‖) ^ 2 := hsq
        _ ≤ ((K : ℝ) * ‖x‖) ^ 2 * g y := le_mul_of_one_le_right (sq_nonneg _) hg1
    · by_cases h2 : y + x ∈ B
      · have hg1 : 1 ≤ g y := by
          simp only [hg, indicator_of_mem h2, indicator_of_notMem h1]
          norm_num
        calc (κ (y + x) - κ y) ^ 2 ≤ ((K : ℝ) * ‖x‖) ^ 2 := hsq
          _ ≤ ((K : ℝ) * ‖x‖) ^ 2 * g y := le_mul_of_one_le_right (sq_nonneg _) hg1
      · rw [hB, mem_ball, dist_zero_right, not_lt] at h1 h2
        rw [hρ y h1, hρ (y + x) h2]
        have : 0 ≤ g y := add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
          (indicator_nonneg (fun _ _ => zero_le_one) _)
        simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
  have hsqi : Integrable fun y => (κ (y + x) - κ y) ^ 2 := by
    have h1 : Integrable fun y => κ y ^ 2 := hκ.integrable_sq
    have h2 : Integrable fun y => κ (y + x) ^ 2 := h1.comp_add_right x
    refine ((h2.add h1).const_mul 2).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((hκ.continuous.comp (continuous_id.add continuous_const)).sub
        hκ.continuous).pow 2 |>.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (κ (y + x) + κ y)]
  rw [one_sub_autoCorr_eq hκ x]
  calc (1 / 2) * ∫ y, (κ (y + x) - κ y) ^ 2
      ≤ (1 / 2) * ∫ y, ((K : ℝ) * ‖x‖) ^ 2 * g y := by
        exact mul_le_mul_of_nonneg_left (integral_mono hsqi (hgi.const_mul _) hpt) (by norm_num)
    _ = (K : ℝ) ^ 2 * volume.real B * ‖x‖ ^ 2 := by
        rw [integral_const_mul, hint]
        ring

/-- **Quadratic bound** `0 ≤ 1 - C(x) ≤ L ‖x‖²` (existential form, `L ≥ 0`). -/
theorem exists_one_sub_autoCorr_le (hκ : IsLFPPKernel κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : Rd d, 0 ≤ 1 - autoCorr κ x ∧ 1 - autoCorr κ x ≤ L * ‖x‖ ^ 2 := by
  obtain ⟨K, hK⟩ := hκ.exists_lipschitzWith
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  exact ⟨(K : ℝ) ^ 2 * volume.real (ball (0 : Rd d) ρ), by positivity, fun x =>
    ⟨one_sub_autoCorr_nonneg hκ x, one_sub_autoCorr_le_of_lipschitzWith hκ hK hρ x⟩⟩

/-! ### Regularity of `C` -/

/-- `C` is Lipschitz with constant `K ∫ κ`, for a Lipschitz constant `K` of `κ`. -/
theorem abs_autoCorr_sub_le (hκ : IsLFPPKernel κ) {K : NNReal} (hK : LipschitzWith K κ)
    (x x' : Rd d) :
    |autoCorr κ x - autoCorr κ x'| ≤ (K : ℝ) * (∫ y, κ y) * ‖x - x'‖ := by
  unfold autoCorr
  rw [← integral_sub (hκ.integrable_mul_add x) (hκ.integrable_mul_add x')]
  have hpt : ∀ y, ‖κ y * κ (y + x) - κ y * κ (y + x')‖ ≤ ((K : ℝ) * ‖x - x'‖) * κ y := by
    intro y
    have hlip : |κ (y + x) - κ (y + x')| ≤ (K : ℝ) * ‖x - x'‖ := by
      have := hK.dist_le_mul (y + x) (y + x')
      rwa [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub] at this
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hκ.nonneg y), mul_comm]
    exact mul_le_mul_of_nonneg_right hlip (hκ.nonneg y)
  calc ‖∫ y, (κ y * κ (y + x) - κ y * κ (y + x'))‖
      ≤ ∫ y, ((K : ℝ) * ‖x - x'‖) * κ y :=
        norm_integral_le_of_norm_le (hκ.integrable.const_mul _) (Eventually.of_forall hpt)
    _ = (K : ℝ) * (∫ y, κ y) * ‖x - x'‖ := by rw [integral_const_mul]; ring

/-- `C` is Lipschitz. -/
theorem exists_lipschitzWith_autoCorr (hκ : IsLFPPKernel κ) :
    ∃ K' : NNReal, LipschitzWith K' (autoCorr κ) := by
  obtain ⟨K, hK⟩ := hκ.exists_lipschitzWith
  refine ⟨K * (∫ y, κ y).toNNReal, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _
    (integral_nonneg hκ.nonneg)]
  exact abs_autoCorr_sub_le hκ hK x x'

theorem continuous_autoCorr (hκ : IsLFPPKernel κ) : Continuous (autoCorr κ) := by
  obtain ⟨K', hK'⟩ := exists_lipschitzWith_autoCorr hκ
  exact hK'.continuous

end AutoCorr

end HigherDimLFPP
