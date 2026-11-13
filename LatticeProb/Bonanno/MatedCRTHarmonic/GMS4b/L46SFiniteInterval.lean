/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SFiniteInterval at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STail

set_option autoImplicit false
noncomputable section

open Set

namespace MatedCRTHarmonic.GMS4b

/-- There are at most `2T/ε + 4` mesh vertices in the interval confining
visits to the covered disk. -/
theorem l46s_finite_interval_card_le {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ((Finset.Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1)).card : ℝ) ≤ 2 * T / ε + 4 := by
  have hlow : ⌈-T / ε⌉ ≤ ⌈T / ε⌉ + 2 := by
    have hratio : -T / ε ≤ T / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      linarith
    have hc := Int.ceil_mono hratio
    omega
  have hcard : ((Finset.Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1)).card : ℤ) =
      ⌈T / ε⌉ + 1 + 1 - ⌈-T / ε⌉ :=
    Int.card_Icc_of_le _ _ (by omega)
  have hcardR : ((Finset.Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1)).card : ℝ) =
      (⌈T / ε⌉ : ℝ) + 1 + 1 - (⌈-T / ε⌉ : ℝ) := by exact_mod_cast hcard
  rw [hcardR]
  have hceil : (⌈T / ε⌉ : ℝ) < T / ε + 1 := Int.ceil_lt_add_one _
  have hfloor : -T / ε ≤ (⌈-T / ε⌉ : ℝ) := Int.le_ceil _
  have hneg : -T / ε = -(T / ε) := by ring
  rw [hneg] at hfloor
  have hdiv : T / ε + T / ε = 2 * T / ε := by ring
  rw [hneg]
  linarith

/-- Polynomially many cells lie in the time window `[-ε⁻ᵖ, ε⁻ᵖ]`. -/
theorem l46s_finite_interval_card_power {ε p : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hp : 0 ≤ p) :
    ((Finset.Icc ⌈-(ε ^ (-p)) / ε⌉ (⌈(ε ^ (-p)) / ε⌉ + 1)).card : ℝ) ≤
      6 * ε ^ (-(p + 1)) := by
  have hεpos : 0 < ε := hε.1
  have hT : 0 ≤ ε ^ (-p) := by positivity
  have hcard := l46s_finite_interval_card_le hT hεpos
  have hpow : ε ^ (-p) / ε = ε ^ (-(p + 1)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hεpos]
    congr 1
    ring
  have hone : 1 ≤ ε ^ (-(p + 1)) := by
    have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hεpos).mpr hε.2.le
    have hh : 0 ≤ p + 1 := by linarith
    have hx := Real.one_le_rpow hinv hh
    rw [Real.inv_rpow hεpos.le] at hx
    rwa [Real.rpow_neg hεpos.le]
  have htwo : 2 * ε ^ (-p) / ε = 2 * ε ^ (-(p + 1)) := by
    rw [show 2 * ε ^ (-p) / ε = 2 * (ε ^ (-p) / ε) by ring, hpow]
  rw [htwo] at hcard
  linarith

end MatedCRTHarmonic.GMS4b
