/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5CentreFin at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5CentreDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.5: the bounds on `𝔠_{δ𝕣}/𝔠_𝕣` on the good event (deterministic)

DFGPS (arXiv:1905.00380, "T"), proof of Theorem 1.5, end of Step 2 (T:1688–1691) and of Step 3
(T:1716–1720): on the intersection of the Prop 3.1 events (with `A = δ^{-ζ'}`) and the event of
Lemma 3.6 (with `ζ'`),
`δ^{ξQ + 3ζ'} ≤ 8 𝔠_{δ𝕣}/𝔠_𝕣` and `𝔠_{δ𝕣}/𝔠_𝕣 ≤ 2 δ^{ξQ - 3ζ'}`.
-/

noncomputable section

open Set Metric Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

/-- **Steps 2–3, conclusion on one realization.** -/
theorem scaling_bounds_of_good (D' : ContMetric) {ξ Qv : ℝ} (c : ℝ → ℝ) (g : DistC)
    {δ r ζ' : ℝ} (hδ : 0 < δ) (hδ8 : δ < 1 / 8) (hr : 0 < r) (hcs : 0 < c (δ * r))
    (hcr : 0 < c r)
    (hH : ∀ z ∈ rS r ∩ gridPts (δ * r), setDistIn D' (scaleSet (δ * r) z rectHK₁)
      (scaleSet (δ * r) z rectHK₂) (scaleSet (δ * r) z rectHU) ≤
        ENNReal.ofReal (δ ^ (-ζ') * scaleFac ξ c g (δ * r) z))
    (hV : ∀ z ∈ rS r ∩ gridPts (δ * r), setDistIn D' (scaleSet (δ * r) z rectVK₁)
      (scaleSet (δ * r) z rectVK₂) (scaleSet (δ * r) z rectVU) ≤
        ENNReal.ofReal (δ ^ (-ζ') * scaleFac ξ c g (δ * r) z))
    (hA : ∀ z ∈ rS r ∩ gridPts (δ * r), ENNReal.ofReal ((δ ^ (-ζ'))⁻¹ * scaleFac ξ c g (δ * r) z) ≤
      setDistIn D' (closedBall z (3 / 4 * (δ * r))) (sphere z (3 / 2 * (δ * r)))
        (ball z (2 * (δ * r))))
    (h2 : ENNReal.ofReal ((δ ^ (-ζ'))⁻¹ * scaleFac ξ c g r 0) ≤
      setDistIn D' (scaleSet r 0 box2K₁) (scaleSet r 0 box2K₂) (scaleSet r 0 box2U))
    (h3 : setDistIn D' (scaleSet r 0 box3K₁) (scaleSet r 0 box3K₂) (scaleSet r 0 box3U) ≤
      ENNReal.ofReal (δ ^ (-ζ') * scaleFac ξ c g r 0))
    (h36 : δ ^ (-ξ * Qv + ζ') * Real.exp (ξ * circleAvg g r 0) ≤
        graphLFPP ξ (δ * r) (fun x => circleAvg g (δ * r) x)
          (leftVerts (δ * r) r) (rightVerts (δ * r) r) (rS r) ∧
      graphLFPP ξ (δ * r) (fun x => circleAvg g (δ * r) x)
          (leftVerts (δ * r) r) (rightVerts (δ * r) r) (rS r) ≤
        δ ^ (-ξ * Qv - ζ') * Real.exp (ξ * circleAvg g r 0)) :
    δ ^ (ξ * Qv + 3 * ζ') ≤ 8 * (c (δ * r) / c r) ∧
      c (δ * r) / c r ≤ 2 * δ ^ (ξ * Qv - 3 * ζ') := by
  set s := δ * r with hs_def
  have hs : 0 < s := mul_pos hδ hr
  have hs8 : 8 * s ≤ r := by rw [hs_def]; nlinarith
  set A := δ ^ (-ζ') with hA_def
  have hA0 : 0 < A := Real.rpow_pos_of_pos hδ _
  have hAinv : A⁻¹ = δ ^ ζ' := by rw [hA_def, Real.rpow_neg hδ.le, inv_inv]
  set e := Real.exp (ξ * circleAvg g r 0) with he
  have he0 : 0 < e := Real.exp_pos _
  set φ : ℂ → ℝ := fun x => circleAvg g s x with hφ
  set Γ := graphLFPP ξ s φ (leftVerts s r) (rightVerts s r) (rS r) with hΓ
  have hΓ0 : 0 < Γ := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hδ _) he0) h36.1
  have hsc : ∀ (t : ℝ) (z : ℂ) (B : ℝ), B * scaleFac ξ c g t z =
      (B * c t) * Real.exp (ξ * circleAvg g t z) := fun t z B => by unfold scaleFac; ring
  have hpow : ∀ x y : ℝ, δ ^ x * δ ^ y = δ ^ (x + y) := fun x y => (Real.rpow_add hδ x y).symm
  constructor
  · -- Step 2
    have k := step2_det D' hs hs8 (mul_pos hA0 hcs) φ
      (fun z hz => (hH z hz).trans_eq (congrArg ENNReal.ofReal (hsc s z A)))
      (fun z hz => (hV z hz).trans_eq (congrArg ENNReal.ofReal (hsc s z A))) hΓ0
      (M := 2 * Γ) (by linarith)
    have k2 := h2.trans k
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity), hsc r 0 A⁻¹, hAinv] at k2
    -- k2 : δ^ζ' c_r e ≤ 4 (A c_s) (2Γ) ≤ 8 A c_s δ^(-ξQ-ζ') e
    have k3 : (δ ^ ζ' * c r) * e ≤ (8 * c s * (A * δ ^ (-ξ * Qv - ζ'))) * e := by
      calc (δ ^ ζ' * c r) * e ≤ 4 * (A * c s) * (2 * Γ) := k2
        _ ≤ 4 * (A * c s) * (2 * (δ ^ (-ξ * Qv - ζ') * e)) := by
          gcongr; exact h36.2
        _ = (8 * c s * (A * δ ^ (-ξ * Qv - ζ'))) * e := by ring
    have k4 := le_of_mul_le_mul_right k3 he0
    have k5 := mul_le_mul_of_nonneg_right k4 (Real.rpow_pos_of_pos hδ (ξ * Qv + 2 * ζ')).le
    have e1 : δ ^ ζ' * c r * δ ^ (ξ * Qv + 2 * ζ') = δ ^ (ξ * Qv + 3 * ζ') * c r := by
      rw [mul_comm (δ ^ ζ'), mul_assoc, hpow]; ring_nf
    have e2 : 8 * c s * (A * δ ^ (-ξ * Qv - ζ')) * δ ^ (ξ * Qv + 2 * ζ') = 8 * c s := by
      rw [hA_def, mul_assoc, mul_assoc, hpow, hpow]
      have : -ζ' + (-ξ * Qv - ζ') + (ξ * Qv + 2 * ζ') = 0 := by ring
      rw [this, Real.rpow_zero, mul_one]
    rw [e1, e2] at k5
    rw [mul_div_assoc', le_div_iff₀ hcr]
    exact k5
  · -- Step 3
    have hX : setDistIn D' (scaleSet r 0 box3K₁) (scaleSet r 0 box3K₂) (scaleSet r 0 box3U) <
        ENNReal.ofReal (2 * A * (c r * e)) := by
      refine h3.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
      unfold scaleFac
      have : 0 < A * (c r * e) := by positivity
      nlinarith
    have k := step3_det D' hs hs8 (mul_pos (inv_pos.2 hA0) hcs) φ
      (fun z hz => (congrArg ENNReal.ofReal (hsc s z A⁻¹)).symm.trans_le (hA z hz)) hX
    rw [hAinv] at k
    -- k : δ^ζ' c_s Γ ≤ 2 A c_r e, Γ ≥ δ^(-ξQ+ζ') e
    have k3 : (δ ^ ζ' * c s * δ ^ (-ξ * Qv + ζ')) * e ≤ (2 * A * c r) * e := by
      calc (δ ^ ζ' * c s * δ ^ (-ξ * Qv + ζ')) * e = δ ^ ζ' * c s * (δ ^ (-ξ * Qv + ζ') * e) := by
            ring
        _ ≤ δ ^ ζ' * c s * Γ := by gcongr; exact h36.1
        _ ≤ 2 * A * (c r * e) := k
        _ = (2 * A * c r) * e := by ring
    have k4 := le_of_mul_le_mul_right k3 he0
    have k5 := mul_le_mul_of_nonneg_right k4 (Real.rpow_pos_of_pos hδ (ξ * Qv - 2 * ζ')).le
    have e1 : δ ^ ζ' * c s * δ ^ (-ξ * Qv + ζ') * δ ^ (ξ * Qv - 2 * ζ') = c s := by
      rw [mul_comm (δ ^ ζ'), mul_assoc, mul_assoc, hpow, hpow]
      have : ζ' + (-ξ * Qv + ζ' + (ξ * Qv - 2 * ζ')) = 0 := by ring
      rw [this, Real.rpow_zero, mul_one]
    have e2 : 2 * A * c r * δ ^ (ξ * Qv - 2 * ζ') = 2 * δ ^ (ξ * Qv - 3 * ζ') * c r := by
      have hp := hpow (-ζ') (ξ * Qv - 2 * ζ')
      rw [show -ζ' + (ξ * Qv - 2 * ζ') = ξ * Qv - 3 * ζ' by ring] at hp
      rw [hA_def, ← hp]; ring
    rw [e1, e2] at k5
    rw [div_le_iff₀ hcr]
    exact k5

end LQGMetric.DFGPS
