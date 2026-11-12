/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Split3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Split2

/-!
# DDDF Proposition 29 on `(−1,2)²` from the first-term increments

`p29DKerBounds_of_firstIncr`: the kernel bounds `P29DKerBounds` from `P29FirstIncr` and the
proved second/third-term and first-term-variance estimates (DDDF arXiv:1904.08021,
DD:1562–1596; the time change `r = (t+s)/2` of the second term is `lintegral_comp_half_le`).
`dddfProp29Sq_of_firstIncr : P29FirstIncr → DDDFProp29Sq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq WhiteNoise Blueprint

lemma norm_sub_le_six {u v : ℂ} (hu : u ∈ sqOpen (-1) 3) (hv : v ∈ sqOpen (-1) 3) :
    ‖v - u‖ ≤ 6 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  obtain ⟨h1, h2, h3, h4⟩ := hu
  obtain ⟨h5, h6, h7, h8⟩ := hv
  rw [Complex.sub_re, Complex.sub_im]
  have e1 : |v.re - u.re| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |v.im - u.im| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- the second term after the time change `r = (t+s)/2` -/
lemma secondTerm_comp_le {t : ℝ} (ht : 0 ≤ t) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioc 0 1, F ((t + s) / 2) ≤ 2 * ∫⁻ r in Ioi 0, F r :=
  (lintegral_mono_set Ioc_subset_Ioi_self).trans (lintegral_comp_half_le F ht)

theorem p29DKerBounds_of_firstIncr (h1 : P29FirstIncr) : P29DKerBounds := by
  intro K hK hKD
  obtain ⟨d, hd, hdK⟩ := exists_margin (a := -1) (L := 3) hK hKD
  obtain ⟨C1, hC1, hb1⟩ := h1 d hd
  set C2 : ℝ := 8 * (π * d ^ 2)⁻¹ + (8 * π)⁻¹ with hC2
  set C3 : ℝ := thirdConst 3 (1 / 2) with hC3
  have hC2p : 0 < C2 := by positivity
  have hC3p : 0 ≤ C3 := by rw [hC3, thirdConst]; positivity
  set V : ℝ := firstConst d 3 ^ 2 * 3 ^ 2 * 2 + 2 * (2 * (π * d ^ 2)⁻¹ * 1) +
    thirdVarConst 3 (1 / 2) with hV
  have hTV : 0 ≤ thirdVarConst 3 (1 / 2) := by unfold thirdVarConst; positivity
  have hVp : 0 ≤ V := by rw [hV]; positivity
  refine ⟨C1 + 2 * C2 + 6 * C3 + 1, Real.sqrt V + 1, by positivity, by positivity,
    fun t ht u hu v hv => ⟨?_, ?_⟩⟩
  · have hL := lintegral_dKer_le ht (fun a b => ENNReal.ofReal ((a - b) ^ 2))
      (ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).pow_const 2))
      (fun a b => by ring_nf) (by simp) u v
    refine hL.trans ?_
    have p1 := hb1 t ht v u (hdK v hv).1 (hdK v hv).2 (hdK u hu).1 (hdK u hu).2
    have p2 : ∫⁻ s in Ioc 0 1, ∫⁻ y in (sqOpen (-1) 3)ᶜ, ENNReal.ofReal
        ((heatKernel ((t + s) / 2) v y - heatKernel ((t + s) / 2) u y) ^ 2) ≤
        ENNReal.ofReal (2 * (C2 * ‖v - u‖)) := by
      refine (secondTerm_comp_le ht.1.le (fun r => ∫⁻ y in (sqOpen (-1) 3)ᶜ,
        ENNReal.ofReal ((heatKernel r v y - heatKernel r u y) ^ 2))).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      exact lintegral_secondTerm_incr_le hd (hdK v hv).1 (hdK v hv).2 (hdK u hu).1 (hdK u hu).2
    have p3 := lintegral_thirdTerm_incr_le (a := -1) (L := 3) (by norm_num) ht.1
      (by norm_num : (0 : ℝ) < 1 / 2) v u
    have h6 := norm_sub_le_six (hKD hu) (hKD hv)
    have hn : 0 ≤ ‖v - u‖ := norm_nonneg _
    calc _ ≤ ENNReal.ofReal (C1 * ‖v - u‖) + ENNReal.ofReal (2 * (C2 * ‖v - u‖)) +
          ENNReal.ofReal (thirdConst 3 (1 / 2) * ‖v - u‖ ^ 2) := by gcongr
      _ = ENNReal.ofReal (C1 * ‖v - u‖ + 2 * (C2 * ‖v - u‖) + C3 * ‖v - u‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((C1 + 2 * C2 + 6 * C3 + 1) * ‖u - v‖) := by
          rw [norm_sub_rev u v]
          refine ENNReal.ofReal_le_ofReal ?_
          have : C3 * ‖v - u‖ ^ 2 ≤ 6 * C3 * ‖v - u‖ := by
            rw [sq, ← mul_assoc, mul_comm C3 ‖v - u‖]
            nlinarith [mul_nonneg hC3p hn]
          nlinarith
  · have hL := lintegral_dKer_le ht (fun a _ => ENNReal.ofReal (a ^ 2))
      (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const 2))
      (fun a b => by ring_nf) (by simp) u v
    refine hL.trans ?_
    have q1 : ∫⁻ s in Ioc 0 1, ∫⁻ y in sqOpen (-1) 3,
        ENNReal.ofReal (firstKer (-1) 3 t s v y ^ 2) ≤
        ENNReal.ofReal (firstConst d 3 ^ 2 * 3 ^ 2 * 2) :=
      (lintegral_mono_set (Ioc_subset_Ioc_right (by norm_num))).trans
        (lintegral_firstTerm_var_le ht.1 hd (by norm_num) (hdK v hv).1 (hdK v hv).2)
    set F2 : ℝ → ℝ≥0∞ := fun r => ∫⁻ y in (sqOpen (-1) 3)ᶜ, ENNReal.ofReal (heatKernel r v y ^ 2)
    have q2 : ∫⁻ s in Ioc 0 1, F2 ((t + s) / 2) ≤
        ENNReal.ofReal (2 * (2 * (π * d ^ 2)⁻¹ * 1)) := by
      have hm : ∫⁻ s in Ioc 0 1, F2 ((t + s) / 2) ≤
          ∫⁻ s in Ioc 0 1, (Ioc (0 : ℝ) 1).indicator F2 ((t + s) / 2) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        rw [indicator_of_mem (show (t + s) / 2 ∈ Ioc (0 : ℝ) 1 from
          ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩)]
      refine (hm.trans (secondTerm_comp_le ht.1.le _)).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      refine (setLIntegral_le_lintegral _ _).trans ?_
      rw [lintegral_indicator measurableSet_Ioc]
      exact lintegral_secondTerm_var_le hd (hdK v hv).1 (hdK v hv).2
    have q3 := lintegral_thirdTerm_var_le (a := -1) (L := 3) (by norm_num) ht.1
      (by norm_num : (0 : ℝ) < 1 / 2) v
    calc _ ≤ ENNReal.ofReal (firstConst d 3 ^ 2 * 3 ^ 2 * 2) +
          ENNReal.ofReal (2 * (2 * (π * d ^ 2)⁻¹ * 1)) +
          ENNReal.ofReal (thirdVarConst 3 (1 / 2)) := by gcongr
      _ = ENNReal.ofReal V := by
          rw [hV, ENNReal.ofReal_add (by positivity) hTV,
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((Real.sqrt V + 1) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := Real.sq_sqrt hVp
          nlinarith [Real.sqrt_nonneg V]

/-- **DDDF Proposition 29 on `(−1,2)²`** modulo the first-term increments (DD:1571–1576). -/
theorem dddfProp29Sq_of_firstIncr (h1 : P29FirstIncr) : DDDFProp29Sq :=
  dddfProp29Sq_of_kerBounds (p29KerBounds_of_dKer (p29DKerBounds_of_firstIncr h1))

end P29WN
end DDDF
end LQGMetric
