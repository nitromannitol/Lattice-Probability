/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.Exists at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.Version
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Non-vacuity: admissible kernels and white-noise fields exist (packet P-F1, target T2)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 (the standing assumptions on `κ`, `W` and
the smooth field `H_{ε,1}`); ruling H10; HA2 Details D9 (R1), (R3); HA6 §4.4 ("radial smooth bump
with unit `L²` norm").

* `bumpKernel d`: the radial bump `x ↦ s(1 - ‖x‖²) / ‖s(1 - ‖·‖²)‖₂`, where `s` is Mathlib's
  `Real.smoothTransition` (smooth, `0` on `(-∞, 0]`, `1` on `[1, ∞)`); `isLFPPKernel_bumpKernel`.
* `exists_isLFPPKernel`: an admissible kernel exists in every dimension.
* `field_exists_impl`: the frozen `field_exists` (target T2): for every admissible `κ` there is a
  probability space with a white noise `W` on `L²(ℝ × ℝ^d)` and continuous versions `H ε` of
  `H_{ε,1}` for all `ε ∈ (0, 1)` (`exists_isWhiteNoise`, `exists_isBandVersion`).

The 2D analogue (non-vacuity of the circle-average hypothesis) is `LQGDimension/Existence/`; its
GFF-specific construction is not needed here (HA6 §3.5, alternative route for F6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace HigherDimLFPP

variable {d : ℕ}

/-- The unnormalized radial bump `x ↦ s(1 - ‖x‖²)` (supported in the closed unit ball). -/
def bump0 (d : ℕ) (x : Rd d) : ℝ := Real.smoothTransition (1 - ‖x‖ ^ 2)

theorem contDiff_bump0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump0 d) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem bump0_nonneg (x : Rd d) : 0 ≤ bump0 d x := Real.smoothTransition.nonneg _

theorem bump0_eq_zero {x : Rd d} (hx : 1 ≤ ‖x‖) : bump0 d x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  nlinarith

theorem bump0_zero : bump0 d 0 = 1 := by
  simp only [bump0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.smoothTransition.one]

theorem hasCompactSupport_bump0 : HasCompactSupport (bump0 d) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) 1) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  exact bump0_eq_zero hx.le

theorem integral_bump0_sq_pos : 0 < ∫ x, bump0 d x ^ 2 := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (contDiff_bump0.continuous.pow 2) (hasCompactSupport_bump0.comp_left (g := fun t : ℝ => t ^ 2)
      (by norm_num)) (fun x => sq_nonneg _) ?_
  simp only [bump0_zero, one_pow, ne_eq, one_ne_zero, not_false_eq_true]

/-- The normalized radial bump: an admissible kernel. -/
def bumpKernel (d : ℕ) (x : Rd d) : ℝ := bump0 d x / Real.sqrt (∫ y, bump0 d y ^ 2)

/-- **An admissible kernel** (`IsLFPPKernel`): smooth, nonnegative, compactly supported, radial,
with `∫ κ² = 1`. -/
theorem isLFPPKernel_bumpKernel (d : ℕ) : IsLFPPKernel (bumpKernel d) where
  contDiff := contDiff_bump0.div_const _
  nonneg x := div_nonneg (bump0_nonneg x) (Real.sqrt_nonneg _)
  hasCompactSupport := by
    have h : bumpKernel d = fun x => bump0 d x * (Real.sqrt (∫ y, bump0 d y ^ 2))⁻¹ := by
      funext x; rw [bumpKernel, div_eq_mul_inv]
    rw [h]
    exact hasCompactSupport_bump0.mul_right
  radial z w hzw := by
    simp only [bumpKernel, bump0, hzw]
  integral_sq := by
    have hpos := integral_bump0_sq_pos (d := d)
    simp_rw [bumpKernel, div_pow, Real.sq_sqrt hpos.le]
    rw [integral_div]
    exact div_self hpos.ne'

/-- Admissible kernels exist in every dimension. -/
theorem exists_isLFPPKernel (d : ℕ) : ∃ κ : Rd d → ℝ, IsLFPPKernel κ :=
  ⟨bumpKernel d, isLFPPKernel_bumpKernel d⟩

/-- **Target T2** (the frozen `field_exists`): admissible kernels exist in every dimension `d ≥ 1`,
and for each of them there is a probability space with a white noise `W` and continuous versions
`H ε` of `H_{ε,1}` for every `ε ∈ (0, 1)`. -/
theorem field_exists_impl : ∀ d : ℕ, 1 ≤ d →
    (∃ κ : Rd d → ℝ, IsLFPPKernel κ) ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℝ → Rd d → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsWhiteNoise P W ∧
          ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε) := by
  intro d _
  refine ⟨exists_isLFPPKernel d, fun κ hκ => ?_⟩
  obtain ⟨W, hW⟩ := exists_isWhiteNoise d
  have hver : ∀ ε : ℝ, ∃ H : Rd d → (ℕ → ℝ) → ℝ,
      0 < ε → IsBandVersion LQGDimension.ExistAsm.stdP W κ ε 1 H := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨H, hH⟩ := exists_isBandVersion hκ hW hε 1
      exact ⟨H, fun _ => hH⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hε⟩
  choose H hH using hver
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, W, H, hW.isProbabilityMeasure, hW,
    fun ε hε => hH ε hε.1⟩

end HigherDimLFPP
