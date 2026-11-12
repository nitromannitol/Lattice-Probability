/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_6Path at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece

/-!
# DFGPS Lemma 2.6, deterministic part: spatial scaling of LFPP paths

Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Lemma 2.6 (T:847–855): the
change of variables `P̃ = P / r` in the LFPP infimum. Here for a general weight: if
`φ₁(x) = φ₂(r x) − c` then `D^{φ₁}(z, w) = r⁻¹ e^{−ξ c} D^{φ₂}(r z, r w)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS

/-- `D^φ(z, w)`: the LFPP infimum for a weight `φ` (so `lfppDistE ξ ε h = lfppInfFn ξ h*_ε`). -/
def lfppInfFn (ξ : ℝ) (φ : ℂ → ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P z w}, lfppLen ξ φ P.1

theorem lfppDistE_eq_lfppInfFn (ξ ε : ℝ) (h : DistC) (z w : ℂ) :
    lfppDistE ξ ε h z w = lfppInfFn ξ (heatMollify ε h) z w := rfl

/-- `a P` is piecewise C¹ from `a z` to `a w`. -/
theorem isPiecewiseC1Path_const_mul {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    (a : ℂ) : IsPiecewiseC1Path (fun t => a * P t) (a * z) (a * w) := by
  obtain ⟨k, t, ht, h0, h1, hC⟩ := hP.piecewise
  refine ⟨by simp [hP.source], by simp [hP.target], continuousOn_const.mul hP.continuousOn,
    k, t, ht, h0, h1, fun i => ?_⟩
  exact contDiffOn_const.mul (hC i)

/-- `lfppLen` of `a P` -/
theorem lfppLen_const_mul (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) (a : ℂ) :
    lfppLen ξ φ (fun t => a * P t) =
      ENNReal.ofReal ‖a‖ * lfppLen ξ (fun x => φ (a * x)) P := by
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  simp only
  rw [deriv_const_mul_field, norm_mul, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  ring

/-- `lfppLen` of the weight `φ + c` -/
theorem lfppLen_add_const (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) (c : ℝ) :
    lfppLen ξ (fun x => φ x + c) P = ENNReal.ofReal (Real.exp (ξ * c)) * lfppLen ξ φ P := by
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
  congr 1
  ring

/-- the change of variables `P ↦ a P` in the LFPP infimum (`a ≠ 0`) -/
theorem lfppInfFn_const_mul (ξ : ℝ) (φ : ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (z w : ℂ) :
    lfppInfFn ξ φ (a * z) (a * w) =
      ENNReal.ofReal ‖a‖ * lfppInfFn ξ (fun x => φ (a * x)) z w := by
  unfold lfppInfFn
  rw [ENNReal.mul_iInf_of_ne (by simpa using ha) ENNReal.ofReal_ne_top]
  refine le_antisymm (le_iInf fun P => ?_) (le_iInf fun Q => ?_)
  · rw [← lfppLen_const_mul]
    exact iInf_le_of_le ⟨_, isPiecewiseC1Path_const_mul P.2 a⟩ le_rfl
  · have hQ := isPiecewiseC1Path_const_mul Q.2 a⁻¹
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, one_mul] at hQ
    refine iInf_le_of_le ⟨_, hQ⟩ (le_of_eq ?_)
    rw [lfppLen_const_mul, ← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), ← norm_mul,
      mul_inv_cancel₀ ha, norm_one, ENNReal.ofReal_one, one_mul]
    simp only [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- **DFGPS Lemma 2.6, deterministic core** (T:847–855): if `φ₁(x) = φ₂(r x) − c` for all `x`,
then `D^{φ₁}(z, w) = r⁻¹ e^{−ξ c} D^{φ₂}(r z, r w)`. -/
theorem lfppInfFn_scale (ξ : ℝ) {φ₁ φ₂ : ℂ → ℝ} {r c : ℝ} (hr : 0 < r)
    (hφ : ∀ x, φ₁ x = φ₂ ((r : ℂ) * x) - c) (z w : ℂ) :
    lfppInfFn ξ φ₁ z w = ENNReal.ofReal (r⁻¹ * Real.exp (-ξ * c)) *
      lfppInfFn ξ φ₂ ((r : ℂ) * z) ((r : ℂ) * w) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [lfppInfFn_const_mul ξ φ₂ hr0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have e1 : (fun x => φ₂ ((r : ℂ) * x)) = fun x => φ₁ x + c := funext fun x => by
    rw [hφ]; ring
  have e2 : lfppInfFn ξ (fun x => φ₁ x + c) z w =
      ENNReal.ofReal (Real.exp (ξ * c)) * lfppInfFn ξ φ₁ z w := by
    unfold lfppInfFn
    rw [ENNReal.mul_iInf_of_ne (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top]
    simp only [lfppLen_add_const]
  rw [e1, e2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  have : r⁻¹ * Real.exp (-ξ * c) * r * Real.exp (ξ * c) = 1 := by
    rw [show -ξ * c = -(ξ * c) by ring, Real.exp_neg]
    field_simp
  rw [this, ENNReal.ofReal_one, one_mul]

end LQGMetric.DFGPS
