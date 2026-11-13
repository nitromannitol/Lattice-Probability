/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46STailAsymptotic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SFiniteInterval
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SAsymptotic

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

/-- An exponential tail evaluated at a superlinear power of `log ε⁻¹`
beats every prescribed power of `ε`. -/
theorem l46s_exp_log_power_le_rpow {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (s : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Real.exp (-(c * (⌈(Real.log ε⁻¹) ^ (1 + δ)⌉₊ : ℝ))) ≤ ε ^ s := by
  have hlog : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hpow := (tendsto_rpow_atTop hδ).comp hlog
  have hlarge := hpow.eventually_ge_atTop (max s 0 / c + 1)
  filter_upwards [hlarge, self_mem_nhdsWithin, eventually_lt_nhdsGT_zero one_pos]
    with ε hlarge hε0 hε1
  have hεpos : 0 < ε := hε0
  have hLpos : 0 < Real.log ε⁻¹ := Real.log_pos ((one_lt_inv₀ hεpos).mpr hε1)
  have hceil : (Real.log ε⁻¹) ^ (1 + δ) ≤
      (⌈(Real.log ε⁻¹) ^ (1 + δ)⌉₊ : ℝ) := Nat.le_ceil _
  have hfactor : (Real.log ε⁻¹) ^ (1 + δ) =
      Real.log ε⁻¹ * (Real.log ε⁻¹) ^ δ := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have hs : s ≤ c * ((Real.log ε⁻¹) ^ δ) := by
    have hmax : s ≤ max s 0 := le_max_left _ _
    have hc' : c * (max s 0 / c + 1) = max s 0 + c := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hlarge hc.le
    dsimp only [Function.comp_apply] at hmul
    linarith
  have hmain : s * Real.log ε⁻¹ ≤
      c * (⌈(Real.log ε⁻¹) ^ (1 + δ)⌉₊ : ℝ) := by
    have hfactor' : (Real.log ε⁻¹) ^ (1 + δ) =
        Real.log ε⁻¹ * (Real.log ε⁻¹) ^ δ := hfactor
    have hm := mul_le_mul_of_nonneg_right hs hLpos.le
    have hc' := mul_le_mul_of_nonneg_left hceil hc.le
    nlinarith [hm, hc']
  rw [Real.rpow_def_of_pos hεpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv]
  rw [Real.log_inv] at hmain
  nlinarith [hmain]

end MatedCRTHarmonic.GMS4b
